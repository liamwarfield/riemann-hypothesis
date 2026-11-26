module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjInner

theorem inner_eq_integral {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (c : ℂ)
    (h : ∀ x y, inner ℂ x y = c * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x y : H) :
    inner ℂ x y = c * ∫ g in 𝓕, star (e x v g) * e y v g ∂μ := by
  have hd : ∀ z : H, ∃ a, IsMultIP M μ 𝓕 (e z) (e z) a := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := h z z
      simp only [ipM, dif_neg hn, mul_zero] at this
      exact hz (inner_self_eq_zero.1 this)
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add (f := _)] at hs ht
  rw [map_smul] at ht
  have h1 := (ipM_spec M μ 𝓕 _ _ ⟨_, GlobalTheory.SchurPolar.exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩ v v).2
  rw [h, h1, Finset.prod_eq_one, mul_one]
  intro τ _
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

theorem conj_integral {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℂ) (hq : starRingEnd ℂ q = q) {a b a' b' : X → ℂ}
    (ha : ∀ g, a g = starRingEnd ℂ (a' g)) (hb : ∀ g, b g = starRingEnd ℂ (b' g)) :
    q * ∫ g, star (a g) * b g ∂μ = starRingEnd ℂ (q * ∫ g, star (a' g) * b' g ∂μ) := by
  rw [map_mul, hq, ← integral_conj]
  congr 2
  funext g
  rw [ha, hb, map_mul]
  rfl

theorem inner_conj_of_span {L W H H' : Type} [Field L] [AddCommGroup W] [Module L W] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : L →+* ℂ) (j : W →ₛₗ[σ] H)
    (j' : W →ₛₗ[(starRingEnd ℂ).comp σ] H') (s : Set W) (hs : Submodule.span L s = ⊤)
    (h : ∀ x ∈ s, ∀ y ∈ s, ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ) (x y : W) :
    ⟪j x, j y⟫_ℂ = starRingEnd ℂ ⟪j' x, j' y⟫_ℂ := by
  have hx : x ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span L s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), inner_add_right, inner_add_right, map_add (f := _), h1, h2]
    | smul a y _ h1 =>
      rw [map_smulₛₗ, map_smulₛₗ, inner_smul_right, inner_smul_right, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]
  | zero => simp
  | add x z _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), inner_add_left, inner_add_left, map_add (f := _), h1, h2]
  | smul a x _ h1 =>
    rw [map_smulₛₗ, map_smulₛₗ, inner_smul_left, inner_smul_left, map_mul, h1, RingHom.comp_apply, Complex.conj_conj]

theorem dim_conj {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt W ((starRingEnd ℂ).comp σ) ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  refine Finset.prod_congr rfl fun ρ _ => ?_
  unfold kapAt
  rw [GlobalTheory.ConjEval.lab_conj]

theorem dim_real {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) :
    starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _


set_option maxHeartbeats 1000000 in
theorem inner_conj_of_values {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (he : R.models_HW) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) {v : (R.MW i σ).Vec} {v' : (R.MW i ((starRingEnd ℂ).comp σ)).Vec} (hv : IsUnitV v) (hv' : IsUnitV v')
    {x y : (R.HW i σ).H} {x' y' : (R.HW i ((starRingEnd ℂ).comp σ)).H}
    (hx : ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i _ v' x' g))
    (hy : ∀ g, evAt R i σ v y g = starRingEnd ℂ (evAt R i _ v' y' g)) :
    ⟪x, y⟫_ℂ = starRingEnd ℂ ⟪x', y'⟫_ℂ := by
  have h1 := inner_eq_integral (R.MW i σ) (R.νW i) (R.fdW i) (R.HW i σ).e _ (he i σ).2.2 v hv x y
  have h2 := inner_eq_integral (R.MW i _) (R.νW i) (R.fdW i) (R.HW i _).e _ (he i _).2.2 v' hv' x' y'
  rw [dim_conj] at h2
  exact h1.trans ((conj_integral _ _ (dim_real _ σ) hx hy).trans (congrArg (starRingEnd ℂ) h2).symm)


end GlobalTheory.ConjInner
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChart
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RoundEqn

open GlobalTheory.Cartier.CartierDiv

variable {X : Scheme.{0}} [IsIntegral X]

theorem eff_of_atlas {C : Type} {E : C → CartierDiv X} {n : ℕ} {ι : Type}
    (𝒜 : SncAtlas E n ι) (c : C) : (E c).Eff := by
  intro y
  have hy : y ∈ ⨆ i, 𝒜.U i := by rw [𝒜.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
  obtain ⟨e, -, -, heq⟩ := 𝒜.snc i
  refine ⟨_, heq c y hi, ?_⟩
  rw [one_mul]
  cases h : e c with
  | none => exact (unitAt_one y).regAt
  | some j => exact ((𝒜.chart i).chart y hi).mem j

theorem Eff.nsmul' {D : CartierDiv X} (h : D.Eff) (m : ℕ) : (m • D).Eff := by
  induction m with
  | zero => rw [zero_nsmul]; exact eff_zero
  | succ m ih => rw [succ_nsmul]; exact ih.add h

theorem isEqn_sum {C : Type} (s : Finset C) (D : C → CartierDiv X) (g : C → X.functionFieldˣ)
    (y : X) (h : ∀ c ∈ s, (D c).IsEqn y (g c)) : (∑ c ∈ s, D c).IsEqn y (∏ c ∈ s, g c) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun c hc => h c (Finset.mem_insert_of_mem hc))

theorem prod_elim_pow {C : Type} [Fintype C] {n : ℕ} {M : Type} [CommMonoid M] (x : Fin n → M)
    (J : Finset (Fin n)) (e : C → Option (Fin n)) (hJ : ∀ j, j ∈ J ↔ ∃ c, e c = some j)
    (r : C → ℕ) :
    ∏ c, ((e c).elim 1 x) ^ r c =
      ∏ j ∈ J, x j ^ (∑ c, if e c = some j then r c else 0) := by
  have step : ∀ c, ((e c).elim 1 x) ^ r c =
      ∏ j ∈ J, x j ^ (if e c = some j then r c else 0) := by
    intro c
    cases h : e c with
    | none => simp
    | some j₀ =>
      have hj₀ : j₀ ∈ J := (hJ j₀).2 ⟨c, h⟩
      rw [Finset.prod_eq_single j₀]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro hn; exact (hn hj₀).elim
  simp_rw [step]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Finset.prod_pow_eq_pow_sum _ _ _

end GlobalTheory.RoundEqn


open GlobalTheory.RoundEqn GlobalTheory.Cartier.CartierDiv in
theorem GlobalTheory.roundedTwist_isEqn :
  ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ((p • G + ∑ c, r c • E c) - p • G).Eff ∧ ∀ (i : ι), ∃ ρ : Fin n → ℕ, (∀ j, ρ j < p) ∧ ∀ y ∈ 𝒜.U i, ∀ t, G.IsEqn y t → (p • G + ∑ c, r c • E c).IsEqn y (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j) := by
  intro p hp X _ _ C _ E n ι _ 𝒜 G r hr
  classical
  refine ⟨?_, fun i => ?_⟩
  · rw [add_sub_cancel_left]
    refine Finset.sum_induction _ (fun D : CartierDiv X => D.Eff) (fun _ _ h h' => h.add h') eff_zero ?_
    intro c _
    exact Eff.nsmul' (eff_of_atlas 𝒜 c) (r c)
  · obtain ⟨e, huniq, hJ, heq⟩ := 𝒜.snc i
    refine ⟨fun j => ∑ c, if e c = some j then r c else 0, fun j => ?_, fun y hy t ht => ?_⟩
    · show (∑ c, if e c = some j then r c else 0) < p
      by_cases h : ∃ c, e c = some j
      · obtain ⟨c₀, hc₀⟩ := h
        rw [Finset.sum_eq_single c₀]
        · rw [if_pos hc₀]; exact hr c₀
        · intro c _ hc; rw [if_neg]; exact fun h' => hc (huniq c c₀ j h' hc₀)
        · intro hn; exact (hn (Finset.mem_univ _)).elim
      · push_neg at h
        rw [Finset.sum_eq_zero fun c _ => if_neg (h c)]
        exact hp.out.pos
    · rw [← prod_elim_pow (𝒜.x i) (𝒜.J i) e hJ r]
      refine (ht.nsmul p).add (isEqn_sum _ _ _ y fun c _ => ?_)
      exact (heq c y hy).nsmul (r c)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roundedTwist_localEquation_chart : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ((p • G + ∑ c, r c • E c) - p • G).Eff ∧ ∀ (i : ι), ∃ ρ : Fin n → ℕ, (∀ j, ρ j < p) ∧ ∀ y ∈ 𝒜.U i, ∀ t, G.IsEqn y t → (p • G + ∑ c, r c • E c).IsEqn y (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j) := by
  first | exact @GlobalTheory.roundedTwist_isEqn | exact GlobalTheory.roundedTwist_isEqn | (intros; apply GlobalTheory.roundedTwist_isEqn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticFibreDescriptionUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticFibreDescriptionUnique
namespace GlobalTheory.AnUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem exp_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ}
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (Pi.single i 1) (u i)) : e = e' := by
  have h0 : e 0 = e' 0 := (HolHom.map_zero_eq_one he).trans (HolHom.map_zero_eq_one he').symm
  refine HolHom.eq_of_fderiv_eq he he' hol hol' fun U hU f =>
    ContinuousLinearMap.coe_injective ((Pi.basisFun ℂ _).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact (((HolHom.isDerivAt0_iff _ _ _).1 (hd i)).2 U hU f).symm.trans
    (((HolHom.isDerivAt0_iff _ _ _).1 (hd' i)).2 U (h0 ▸ hU :) f)

theorem fr_eq {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ Φ' : AnFr A L x0 g) (he : ∀ z, Φ'.e z = Φ.e z) (hH : ∀ z w, hermForm Φ'.Hm z w = hermForm Φ.Hm z w)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) : Φ.fr j z = Φ'.fr j z := by
  choose c hc using Φ.exists_chart_e
  have ne' : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → Φ'.fr j z ≠ 0 := fun j z h => Φ'.fr_ne j z (by rw [he]; exact h)
  let q : (Fin g → ℂ) → ℂ := fun z => Φ.fr (c z) z / Φ'.fr (c z) z
  have key : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → q z = Φ.fr j z / Φ'.fr j z := fun j z h => by
    have hz : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ (L.L.U j ⊓ L.L.U (c z)) := fun p hp => ⟨h hp, hc z hp⟩
    have h1 := Φ.fr_g j (c z) z hz
    have h2 := Φ'.fr_g j (c z) z (by rw [he]; exact hz)
    rw [he] at h2
    rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ Φ.fr_ne j z h))]
  have hq : Differentiable ℂ q := fun z0 => by
    have hO : IsOpen {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := (Φ.hol (L.L.U (c z0)) 0).1
    have h' : DifferentiableOn ℂ (Φ'.fr (c z0)) {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := by
      simpa only [he] using Φ'.fr_hol (c z0)
    have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} :=
      ((Φ.fr_hol (c z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
        (key _ z hz).trans (div_eq_mul_inv _ _)
    exact hd.differentiableAt (hO.mem_nhds (hc z0))
  have hper : ∀ z (a : Φ.lat), ‖q (z + Φ.lat.subtype a)‖ = ‖q z‖ := fun z a => by
    have ha' : (a : Fin g → ℂ) ∈ Φ'.lat := (Φ'.e_ker _).1 ((he _).trans ((Φ.e_ker _).2 a.2))
    have h : ⊤ ≤ (Φ.e (z + a)).left ⁻¹ᵁ L.L.U (c z) := by rw [Φ.e_add_lat a.2]; exact hc z
    have h1 := Φ.fr_per a a.2 (c z) z (hc z)
    have h2 := Φ'.fr_per a ha' (c z) z (by rw [he]; exact hc z)
    rw [hH, hH] at h2
    change ‖q (z + a)‖ = _
    rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      Φ.χ_norm _ a.2, Φ'.χ_norm _ ha',
      mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
  have hc0 := norm_periodic_const_range Φ.lat.subtype
    (by rw [AddSubgroup.coe_subtype, Subtype.range_coe]; exact Φ.span) q hq hper z 0
  have h0 : q 0 = 1 := by
    have := Φ'.fr_0 (c 0) (by rw [he]; exact hc 0)
    rw [← Φ.fr_0 (c 0) (hc 0)] at this
    change Φ.fr (c 0) 0 / Φ'.fr (c 0) 0 = 1
    rw [this, div_self (Φ.fr_ne _ _ (hc 0))]
  rw [h0, key j z hj] at hc0
  exact (div_eq_one_iff_eq (ne' j z hj)).1 hc0

end GlobalTheory.AnUniq

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AnUniq.anFib_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A A' : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → A.ex = A'.ex ∧ ∀ ϑ, A.Reads 1 y.s ϑ ↔ A'.Reads 1 y.s ϑ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A A' hs hx hL
  have hex : A.ex = A'.ex := AnUniq.exp_eq A.ex_add A'.ex_add A.hol A'.hol (fun i => y.u (e i).1 (e i).2)
    (fun i => by simpa only [Equiv.symm_apply_apply] using A.der (e i))
    (fun i => by simpa only [Equiv.symm_apply_apply] using A'.der (e i))
  obtain ⟨Φ, k₁, f₁, -, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, f₂, -, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A' hs hx hL
  have hfr := AnUniq.fr_eq Φ.toAnFr Φ'.toAnFr (fun z => by rw [k₁, k₂, hex]) (fun z w => by rw [m₁, m₂])
  simp only [k₁, f₁, f₂] at hfr
  refine ⟨hex, fun ϑ => ⟨fun h j z pt h1 h2 hj => ?_, fun h j z pt h1 h2 hj => ?_⟩⟩
  · rw [← hex] at h1 hj
    rw [← hfr j z hj]
    exact h j z pt h1 h2 hj
  · rw [hfr j z hj]
    rw [hex] at h1 hj
    exact h j z pt h1 h2 hj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticFibreDescriptionUniqueStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFibreDescription_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A A' : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → A.ex = A'.ex ∧ ∀ ϑ, A.Reads 1 y.s ϑ ↔ A'.Reads 1 y.s ϑ := by
  first | exact @GlobalTheory.AnUniq.anFib_unique | exact GlobalTheory.AnUniq.anFib_unique | (intros; apply GlobalTheory.AnUniq.anFib_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerConjFormsEqCsumAt
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {M W' ι : Type} [AddCommGroup M] [Module K M]
  [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [Fintype ι]


omit [NumberField K] in
theorem inner_coef_of_rat (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W') (pr : M →ₗ⋆[K] M →ₗ[K] K)
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a'))) (u v : M) (hu : ∀ a, b.repr u a ∈ cmMax K) :
    inner ℂ (c₁ u) (c₁ v) = σ (pr u v) := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply (b.repr u a'), hu a' σ]

theorem inner_eq_csumAt (S : CSD K) (hb : S.HasRatBasis) (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (pr : M →ₗ⋆[K] M →ₗ[K] K) (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (e : S.V ≃ₗ[K] M) (hr : ∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) (he : ∀ x x', pr (e x) (e x') = S.pair x x')
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : S.Forms →ₛₗ[σ] H)
    (hj : ∀ x y : S.Forms, inner ℂ (j x) (j y) =
      ∑ c, ((S.wt c : ℂ))⁻¹ * inner ℂ (c₁ (e ((x : S.Cl → S.V) c))) (c₁ (e ((y : S.Cl → S.V) c)))) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  have hrat : ∀ k c a, b.repr (e ((S.basis k : S.Cl → S.V) c)) a ∈ cmMax K := by
    intro k c a
    rw [← S.bV.sum_repr ((S.basis k : S.Cl → S.V) c)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (S.basis_rat hb k c i) (hr i a)
  have hH : ∀ k l, inner ℂ (j (S.basis k)) (j (S.basis l)) = σ (S.H k l) := by
    intro k l
    rw [hj]
    unfold CSD.H CSD.csum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_coef_of_rat b σ c₁ pr hp _ _ (hrat k c), he, map_mul, map_inv₀, map_natCast]
  conv_lhs => rw [← S.basis.sum_repr x, ← S.basis.sum_repr y]
  unfold csumAt
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hH,
    dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply]
  ring

theorem inner_eq_csumAt_of_pres {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ι₀ : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι₀ S σ₀ ρ J χ) (b : Module.Basis ι K M) (c₀ : M →ₛₗ[σ₀] W) (pr : M →ₗ⋆[K] M →ₗ[K] K)
    {Q : (S.V ≃ₗ[K] M) → Prop}
    (hP : ∃ e : S.V ≃ₗ[K] M, (∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) ∧ (∀ x, P.coef x = c₀ (e x)) ∧
      (∀ x x', pr (e x) (e x') = S.pair x x') ∧ Q e)
    (hb : S.HasRatBasis) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (H : HMod (G → W')) (j : S.Forms →ₛₗ[σ] H.H)
    (hH : ∀ x y : H.H, inner ℂ x y = Bridge.adInner ι₀ J P.y (H.e x) (H.e y))
    (hj : ∀ (x : S.Forms) h, ∃ v, P.ext (x : S.Cl → S.V) h = c₀ v ∧ H.e (j x) h = c₁ v) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  obtain ⟨e, hr, he, hpair, -⟩ := hP
  have hval : ∀ (z : S.Forms) cl, H.e (j z) (P.y cl) = c₁ (e (z.1 cl)) := by
    intro z cl
    obtain ⟨v, h0, h1⟩ := hj z (P.y cl)
    have h3 : P.coef (z.1 cl) = P.coef (e.symm v) := by
      rw [← GlobalTheory.PresBasic.ext_y P z cl, h0, he, e.apply_symm_apply]
    rw [h1, GlobalTheory.PresBasic.coef_injective _ h3, e.apply_symm_apply]
  refine inner_eq_csumAt S hb _ σ c₁ _ hp e hr hpair j (fun z w => ?_) x y
  rw [hH]
  unfold Bridge.adInner
  refine Finset.sum_congr rfl fun cl _ => ?_
  rw [hval, hval, CSD.wt, ← Nat.card_eq_fintype_card, Nat.card_congr (P.stabI cl).toEquiv]

end Generic

theorem inner_conjForms_eq_csumAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) c c₁ H j, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ x y, ⟪j x, j y⟫_ℂ = csumAt (A.MtCSD i A.μ0) σ x y := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hjV gramR c0R c0L hT i σ c c₁ H j hC x y
  have hb : (A.MtCSD i A.μ0).HasRatBasis :=
    (GlobalTheory.HeckeRational.dcOp_matrix_mem_cmMax (Vc D i) (R.cV i).coef (R.βV i) (R.datVt i A.μ0) (R.B.L i A.μ0).pres
      (hT.coefL i A.μ0) (hT.mapL i)
      (fun g a k => (coefAction_repr_mem_subfield (labLL D) _ _ GlobalTheory.HeckeRational.labLL_mem_cmMax g a k).2) {1} 1
      (fun f => by funext h; simp [Bridge.dcOp])).1
  have h1 := hC.model.choose_spec.2.2.2
  have h2 : ∀ (z : A.fam.amb.FL i A.μ0) h, ∃ v, (R.B.L i A.μ0).pres.ext z.1 h = c0L i v ∧ H.e (j z) h = c₁ v :=
    fun z h => (hC.base z h).imp fun v hv => ⟨(congrFun (hjV i A.μ0 z) h).symm.trans hv.1, hv.2⟩
  exact inner_eq_csumAt_of_pres (R.B.L i A.μ0).pres _ (c0L i) _ (hT.coefL i A.μ0) hb σ c₁ hC.pair H j h1 h2 x y

end GlobalTheory.LiftLower

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicDualPartnerSelfDualHermitianLatti
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicDualPartnerSelfDualHermitianLatti
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.TraceCorrection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, add_dotProduct]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  have h : (fun i => σ ((y + y') i)) = (fun i => σ (y i)) + fun i => σ (y' i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  have h : (fun i => σ ((c • y) i)) = σ c • fun i => σ (y i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_symm (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (form σ J x y) = form σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ x y₀ : Fin n → E, form σ J x x = 0 → form σ J y₀ x = 1 →
    (∀ z ∈ L, form σ J z x • y₀ ∈ L) →
    ∃ y : Fin n → E, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z y • x ∈ L ∧ form σ J z x • y ∈ L := by
  intro F E _ _ _ _ _ σ hσ n J L hJ hL θ hθ x y₀ hxx hy₀x hL0
  have hsa : σ (form σ J y₀ y₀) = form σ J y₀ y₀ := form_symm σ J hσ hJ y₀ y₀
  have hxw : ∀ w, form σ J x w = σ (form σ J w x) := fun w => (form_symm σ J hσ hJ w x).symm
  have hxy₀ : form σ J x y₀ = 1 := by rw [hxw, hy₀x, map_one]
  have hsθ : σ (θ : E) = 1 - θ := by linear_combination hθ
  have hθi : IsIntegral ℤ (θ : E) := θ.isIntegral_coe
  have hA : ∀ z ∈ L, ∀ w ∈ L,
      IsIntegral ℤ (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
    intro z hz w hw
    have h := (hL _).1 (hL0 z hz) _ (hL0 w hw)
    rw [form_smul_left, form_smul_right] at h
    have k : form σ J z x * (σ (form σ J w x) * form σ J y₀ y₀) =
        form σ J y₀ y₀ * form σ J z x * σ (form σ J w x) := by ring
    rw [← k]; exact h
  refine ⟨y₀ + (-((θ : E) * form σ J y₀ y₀)) • x, ?_, ?_, ?_⟩
  · simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hxx, hxy₀, hy₀x,
      map_neg, map_mul, hsθ, hsa]
    ring
  · simp only [form_add_right, form_smul_right, hxx, hxy₀]
    ring
  intro z hz
  constructor
  · have e : form σ J z (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) • x =
        form σ J z y₀ • x + (σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x) • x := by
      rw [form_add_right, form_smul_right, add_smul]
    rw [e]
    refine L.add_mem ((hL _).2 fun w hw => ?_) ((hL _).2 fun w hw => ?_)
    · have h := (hL z).1 hz _ (hL0 w hw)
      rw [form_smul_right] at h
      rw [form_smul_left, hxw, mul_comm]
      exact h
    · rw [form_smul_left, hxw]
      have h := (hA z hz w hw).neg.add (hθi.mul (hA z hz w hw))
      have k : σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x * σ (form σ J w x) =
          -(form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) +
            (θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
        rw [map_neg, map_mul, hsθ, hsa]; ring
      rw [k]; exact h
  · have e : form σ J z x • (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) =
        form σ J z x • y₀ + (form σ J z x * (-((θ : E) * form σ J y₀ y₀))) • x := by
      rw [smul_add, mul_smul]
    rw [e]
    refine L.add_mem (hL0 z hz) ((hL _).2 fun w hw => ?_)
    rw [form_smul_left, hxw]
    have h := (hθi.mul (hA z hz w hw)).neg
    have k : form σ J z x * (-((θ : E) * form σ J y₀ y₀)) * σ (form σ J w x) =
        -((θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x))) := by ring
    rw [k]; exact h

end GlobalTheory.TraceCorrection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicDualPartnerSelfDualHermitianLattiStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ x y₀ : Fin n → E, form σ J x x = 0 → form σ J y₀ x = 1 →
    (∀ z ∈ L, form σ J z x • y₀ ∈ L) →
    ∃ y : Fin n → E, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z y • x ∈ L ∧ form σ J z x • y ∈ L := by
  first | exact @GlobalTheory.TraceCorrection.exists_pair | exact GlobalTheory.TraceCorrection.exists_pair | (intros; apply GlobalTheory.TraceCorrection.exists_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHolomorphicTypeFamilyHolomorphicType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHolomorphicTypeFamilyHolomorphicType
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem UpT.diag_ne_zero {n : ℕ} {b : Mt n} (hb : UpT b) (a : Fin n) : b a a ≠ 0 := by
  have hdet : b.det = ∏ i, b i i := Matrix.det_of_upperTriangular (fun i j hij => hb.2 i j hij)
  have h := hb.1
  rw [hdet, Finset.prod_ne_zero_iff] at h
  exact h a (Finset.mem_univ a)

theorem holFn_integral : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → (ι → Mt n) → ℂ) (C : ℝ), (∀ o, HolFn Hm q x₀ w (f o)) → (∀ o, ∀ u ∈ UG Hm, ‖f o u‖ ≤ C) → (∀ u ∈ UG Hm, AEStronglyMeasurable (fun o => f o u) ν) → HolFn Hm q x₀ w fun u => ∫ o, f o u ∂ν := by
  intro n ι _ _ Hm q x₀ w hx Ω _ ν _ f C hf hC hmeas

  have hf' : ∀ o, ∃ P, HolSec Hm q w P ∧ ∀ u ∈ UG Hm, f o u = P fun τ => (u τ * x₀ τ : Mt n) := hf
  choose Pc hPc using hf'

  have hβ := fun τ => GlobalTheory.T.smooth_gram_schmidt_indefinite_hermitian_frames n (Hm τ) (q τ) (x₀ τ) (hx τ)
  choose β hβc hβ using hβ
  obtain ⟨hopen, -, hmul, hx0⟩ := GlobalTheory.T.negativeFrameDomainProduct_open_preconnected_stable n ι Hm q x₀ hx

  let uu : (ι → Fin n → Fin n → ℂ) → ι → Mt n :=
    fun y τ => Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹ * (x₀ τ)⁻¹
  let cc : (ι → Fin n → Fin n → ℂ) → ℂ := fun y => ∏ τ, ∏ a, (β τ (y τ)) a a ^ w τ a
  have huu : ∀ y ∈ frDoms Hm q, uu y ∈ UG Hm := fun y hy τ => (hβ τ (y τ) (hy τ)).2

  have hkey : ∀ o, ∀ y ∈ frDoms Hm q, Pc o y = cc y * f o (uu y) := by
    intro o y hy
    have hu := huu y hy
    have hone : ∀ _τ : ι, UpT (1 : Mt n) := fun _ =>
      ⟨by simp, fun a c hca => Matrix.one_apply_ne (ne_of_gt hca)⟩
    have hfr : (fun τ => (uu y τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
      have := hmul (uu y) hu (fun _ => 1) hone (fun τ => (x₀ τ : Mt n)) hx0
      simp only [Matrix.mul_one] at this
      exact this
    have hB : ∀ τ, UpT (Matrix.of (β τ (y τ))) := fun τ => (hβ τ (y τ) (hy τ)).1
    have heq := (hPc o).1.2 (fun τ => (uu y τ * x₀ τ : Mt n)) hfr
      (fun τ => Matrix.of (β τ (y τ))) hB
    have hrec : (fun τ => (Matrix.of ((uu y τ * x₀ τ : Mt n)) * Matrix.of (β τ (y τ)) : Mt n)) = y := by
      funext τ
      have hX : (x₀ τ)⁻¹ * x₀ τ = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hx0 τ).1)
      have hBB : (Matrix.of (β τ (y τ)))⁻¹ * Matrix.of (β τ (y τ)) = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hB τ).1)
      show Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹ * (x₀ τ)⁻¹ * x₀ τ * Matrix.of (β τ (y τ)) = y τ
      rw [Matrix.mul_assoc (Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹), hX, Matrix.mul_one,
        Matrix.mul_assoc, hBB, Matrix.mul_one]
      rfl
    rw [hrec] at heq
    rw [heq, ← (hPc o).2 (uu y) hu]
    rfl

  have hcc : ContinuousOn cc (frDoms Hm q) := by
    apply continuousOn_finsetProd _
    intro τ _
    apply continuousOn_finsetProd _
    intro a _
    have h1 : ContinuousOn (fun y : ι → Fin n → Fin n → ℂ => β τ (y τ)) (frDoms Hm q) :=
      (hβc τ).continuousOn.comp (continuous_apply τ).continuousOn (fun y hy => hy τ)
    have h2 : ContinuousOn (fun y : ι → Fin n → Fin n → ℂ => β τ (y τ) a a) (frDoms Hm q) :=
      (show Continuous fun M : Fin n → Fin n → ℂ => M a a from
        (continuous_apply a).comp (continuous_apply a)).comp_continuousOn h1
    exact h2.zpow₀ _ (fun y hy => Or.inl (UpT.diag_ne_zero (hβ τ (y τ) (hy τ)).1 a))
  have hPmeas : ∀ y ∈ frDoms Hm q, AEStronglyMeasurable (fun o => Pc o y) ν := by
    intro y hy
    have : (fun o => Pc o y) = fun o => cc y * f o (uu y) := funext fun o => hkey o y hy
    rw [this]
    exact (hmeas (uu y) (huu y hy)).const_mul (cc y)
  have hdom : ∀ x ∈ frDoms Hm q, ∃ s ∈ 𝓝 x, ∃ bound : Ω → ℝ, Integrable bound ν ∧
      ∀ᵐ o ∂ν, ∀ y ∈ s, ‖Pc o y‖ ≤ bound o := by
    intro x hxm
    have hca : ContinuousAt cc x := hcc.continuousAt (hopen.mem_nhds hxm)
    have hev : ∀ᶠ y in 𝓝 x, ‖cc y‖ < ‖cc x‖ + 1 :=
      hca.norm.eventually (Iio_mem_nhds (lt_add_one _))
    refine ⟨{y | ‖cc y‖ < ‖cc x‖ + 1} ∩ frDoms Hm q, Filter.inter_mem hev (hopen.mem_nhds hxm),
      fun _ => (‖cc x‖ + 1) * max C 0, integrable_const _, Filter.Eventually.of_forall ?_⟩
    intro o y hy
    rw [hkey o y hy.2, norm_mul]
    exact mul_le_mul hy.1.le (le_max_of_le_left (hC o (uu y) (huu y hy.2))) (norm_nonneg _)
      (by positivity)
  unfold HolFn HolSec
  refine ⟨fun y => ∫ o, Pc o y ∂ν, ⟨?_, ?_⟩, ?_⟩
  · exact (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated hopen hPmeas
      (Filter.Eventually.of_forall fun o => (hPc o).1.1) hdom).1
  · intro x hxm b hb
    calc ∫ o, Pc o (fun τ => (Matrix.of (x τ) * b τ : Mt n)) ∂ν
        = ∫ o, (∏ τ, ∏ a, b τ a a ^ w τ a) * Pc o x ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall fun o => (hPc o).1.2 x hxm b hb)
      _ = (∏ τ, ∏ a, b τ a a ^ w τ a) * ∫ o, Pc o x ∂ν := integral_const_mul _ _
  · intro u hu
    exact integral_congr_ae (Filter.Eventually.of_forall fun o => (hPc o).2 u hu)

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHolomorphicTypeFamilyHolomorphicTypeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_holomorphicTypeFamily_holomorphicType : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → (ι → Mt n) → ℂ) (C : ℝ), (∀ o, HolFn Hm q x₀ w (f o)) → (∀ o, ∀ u ∈ UG Hm, ‖f o u‖ ≤ C) → (∀ u ∈ UG Hm, AEStronglyMeasurable (fun o => f o u) ν) → HolFn Hm q x₀ w fun u => ∫ o, f o u ∂ν := by
  first | exact @GlobalTheory.HolDict.holFn_integral | exact GlobalTheory.HolDict.holFn_integral | (intros; apply GlobalTheory.HolDict.holFn_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTransposeMajorant
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower

namespace GlobalTheory.Proof.ConjugateTransposeMajorant

section

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem csum_eq_coord (S : CSD K) (f g : S.Forms) :
    S.csum (f : S.Cl → S.V) (g : S.Cl → S.V) = star (fun a => S.basis.repr f a) ⬝ᵥ S.H *ᵥ fun a => S.basis.repr g a := by
  have hf : ∀ c, (f : S.Cl → S.V) c = ∑ a, S.basis.repr f a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr f]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hg : ∀ c, (g : S.Cl → S.V) c = ∑ a, S.basis.repr g a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr g]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have e : ∀ c, S.pair ((f : S.Cl → S.V) c) ((g : S.Cl → S.V) c) =
      ∑ a, ∑ b, star (S.basis.repr f a) * (S.pair ((S.basis a : S.Cl → S.V) c) ((S.basis b : S.Cl → S.V) c) *
        S.basis.repr g b) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf c, hg c, map_sum S.pair, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  simp only [CSD.csum, CSD.H, e, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

omit [NumberField K] in
theorem map_conjTranspose_of_mem {m n : Type} (E : Matrix m n K) (hE : ∀ a k, E a k ∈ cmMax K) (σ : K →+* ℂ) :
    Eᴴ.map σ = (E.map σ)ᴴ := by
  ext i j
  exact hE j i σ

omit [NumberField K] [StarRing K] in
theorem map_mulVec' {m n : Type} [Fintype n] (E : Matrix m n K) (x : n → K) (σ : K →+* ℂ) :
    (fun a => σ ((E *ᵥ x) a)) = E.map σ *ᵥ fun k => σ (x k) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)

theorem repr_toF (x : Fin (B.dZ ℓ Z) → K) : (fun a => B.S.basis.repr (B.toF ℓ Z x) a) = B.fE ℓ Z *ᵥ x := by
  have : B.S.basis.equivFun (B.toF ℓ Z x) = B.fE ℓ Z *ᵥ x := by
    rw [BlockDat.fE, ← Matrix.mulVec_mulVec]
    exact B.S.basis.equivFun.apply_symm_apply _
  rw [← this]
  rfl

theorem HZ_eq : B.HZ ℓ Z = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.fE ℓ Z)ᴴ * B.S.H * B.fE ℓ Z) := by
  have : B.HV ℓ = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [BlockDat.HZ, this, BlockDat.fE, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem csumAt_toF (σ : K →+* ℂ) (x : Fin (B.dZ ℓ Z) → K) (u : B.S.Forms) :
    csumAt B.S σ (B.toF ℓ Z x) u = star (fun k => σ (x k)) ⬝ᵥ ((B.fE ℓ Z).map σ)ᴴ *ᵥ
      (B.S.H.map σ *ᵥ fun a => σ (B.S.basis.repr u a)) := by
  have h : (fun a => σ (B.S.basis.repr (B.toF ℓ Z x) a)) = (B.fE ℓ Z).map σ *ᵥ fun k => σ (x k) := by
    rw [← map_mulVec', ← repr_toF]
  unfold csumAt
  rw [h, Matrix.star_mulVec, Matrix.dotProduct_mulVec _ (((B.fE ℓ Z).map σ)ᴴ)]

end

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem majAt_eq_csumAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms), IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → (∀ a k, B.fE ℓ Z a k ∈ cmMax K) → (∀ (v : InfinitePlace K) x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ * csumAt B.S v.embedding (B.toF ℓ Z x) (B.toF ℓ Z y)) ∧ ∀ u : B.S.Forms, (∀ x, B.S.csum (B.toF ℓ Z x : B.S.Cl → B.S.V) (u : B.S.Cl → B.S.V) = 0) → ∀ (σ : K →+* ℂ) x, csumAt B.S σ (B.toF ℓ Z x) u = 0 := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z hH hE
  refine ⟨fun v x y => ?_, fun u hu σ x => ?_⟩
  · have h1 : ∀ w : Fin (B.dZ ℓ Z) → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K _) v w = fun k => v.embedding (w k) := by
      intro w; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    have h2 : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y =
        star ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (x k)) ⬝ᵥ ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (y k)) := by
      simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h1]
      rfl
    have h3 : (fun a => v.embedding (B.S.basis.repr (B.toF ℓ Z y) a)) =
        (B.fE ℓ Z).map v.embedding *ᵥ fun k => v.embedding (y k) := by
      rw [← map_mulVec', ← repr_toF]
    have h4 : (B.HZ ℓ Z).map v.embedding = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ •
        (((B.fE ℓ Z).map v.embedding)ᴴ * B.S.H.map v.embedding * (B.fE ℓ Z).map v.embedding) := by
      rw [← map_conjTranspose_of_mem _ hE, ← Matrix.map_mul, ← Matrix.map_mul, HZ_eq]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
    rw [h2, csumAt_toF, h3, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (hH.2 v).2, h4,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · have h0 : (B.fE ℓ Z)ᴴ *ᵥ (B.S.H *ᵥ fun a => B.S.basis.repr u a) = 0 := by
      funext k
      have := hu (Pi.single k 1)
      rw [csum_eq_coord, repr_toF, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at this
      have e : star (Pi.single k (1 : K) : Fin (B.dZ ℓ Z) → K) = Pi.single k 1 := by
        rw [Pi.star_single, star_one]
      rw [e, single_dotProduct, one_mul] at this
      exact this
    rw [csumAt_toF, ← map_mulVec', ← map_conjTranspose_of_mem _ hE, ← map_mulVec', h0]
    simp

end GlobalTheory.Proof.ConjugateTransposeMajorant

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartEquationsDifferUnit
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

theorem sncChart_germ_eqn_unit : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Sp R) {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ (C C' : SncChart g n L σ) (y : Y) (hy : y ∈ C.U) (hy' : y ∈ C'.U) (c : Fin s), ∃ v : (Y.presheaf.stalk y)ˣ, (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) = v * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t) := by
  intro R _ Y g n s L σ hL C C' y hy hy' c
  have hyi : y ∈ (L c).U (C.c c) := C.le c hy
  have hyj : y ∈ (L c).U (C'.c c) := C'.le c hy'
  have hyij : y ∈ (L c).U (C.c c) ⊓ (L c).U (C'.c c) := ⟨hyi, hyj⟩
  have e1 := congrArg (Y.presheaf.germ C.U y hy).hom (C.eq c)
  have e2 := congrArg (Y.presheaf.germ C'.U y hy').hom (C'.eq c)
  have e3 := congrArg (Y.presheaf.germ _ y hyij).hom ((σ c).2 (C.c c) (C'.c c))
  simp only [resG, map_mul, TopCat.Presheaf.germ_res_apply] at e1 e2 e3
  let w0 := Units.map (Y.presheaf.germ C.U y hy).hom.toMonoidHom (C.u c)
  let w1 := Units.map (Y.presheaf.germ C'.U y hy').hom.toMonoidHom (C'.u c)
  let wg := Units.map (Y.presheaf.germ _ y hyij).hom.toMonoidHom ((L c).g (C.c c) (C'.c c))
  refine ⟨w0⁻¹ * wg * w1, ?_⟩
  have key : (w0 : Y.presheaf.stalk y) * (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) =
      (wg : Y.presheaf.stalk y) * ((w1 : Y.presheaf.stalk y) * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t)) := by
    exact e1.symm.trans (e3.trans (congrArg (fun z => _ * z) e2))
  calc (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t)
      = ((w0⁻¹ : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) * ((w0 : Y.presheaf.stalk y) * (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [key]; simp only [Units.val_mul, mul_assoc]

end GlobalTheory.LogPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesStalkFlat
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}}
    (g : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U →
    _root_.GlobalTheory.LogPair.IsEtCoord g U t → ∀ (y : Y) (hy : y ∈ U),
    ((Y.presheaf.germ U y hy).hom.comp (_root_.GlobalTheory.LogPair.cstOn g U)).Flat := by
  intro R _ Y g U n t hU ht y hy
  have hC : (MvPolynomial.C : R →+* MvPolynomial (Fin n) R).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have hE : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Flat := by
    have h : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Etale := ht
    letI := (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(Y, U) := h
    show Module.Flat _ _
    infer_instance
  have hG : (Y.presheaf.germ U y hy).hom.Flat := by
    letI := (Y.presheaf.germ U y hy).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨y, hy⟩
    show Module.Flat _ _
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  rw [← MvPolynomial.eval₂Hom_comp_C (_root_.GlobalTheory.LogPair.cstOn g U) t, ← RingHom.comp_assoc]
  exact (hC.comp hE).comp hG

end GlobalTheory.LogPair
end

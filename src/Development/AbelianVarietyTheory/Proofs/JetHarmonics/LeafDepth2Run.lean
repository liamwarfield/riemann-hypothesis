module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HostFieldTwoConjugatePlacesOverTwo
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformized
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreAndCapelli
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThirdPointDerivativeAtZeroSeriesMemIntegral
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DmonOfMulCongrOfCongr
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HtDualExists
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBoundAtResidueCharacteristic
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDepthLeResidueCharTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HodgeTateInclusionIntegralChart
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HodgeTateInclusionIntegralChart
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem hodgeTate_inclusion_intChart : ∀ (p : ℕ) [Fact p.Prime], HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), y.IsAlg → ∃ (N : ℕ) (u : Fin N → PS X.O 1 (chD Ch.ch)), (∀ k, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (u k)) ∧ ∀ z : X.O, X.v (algebraMap X.O X.C z) ^ (p - 1) ≤ X.v (p : X.C) → ∀ f : Fin (chD Ch.ch) → X.O, z • f ∈ Submodule.span X.O (Set.range fun k => dl (u k)) := by
  intro p _ hHT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch X hy
  obtain ⟨U⟩ := GlobalTheory.CharDepth.nonempty_unifChart E H Dw l Xo c T io y Ch hy p X
  have hp : ¬IsUnit (p : U.T'.V) := fun h => by
    have h' := h.map U.ι'
    rw [map_natCast] at h'
    exact (Fact.out : ¬IsUnit (p : X.O)) h'
  obtain ⟨N, u, hu, hz⟩ := hHT U.T'.V hp U.t.G U.P.D U.P.A U.P.U.toUnifPre (chD Ch.ch) U.F U.x
    U.chart X.C X.v X.O X.ints U.ι' U.ι'_local
  refine ⟨N, u, fun k => ?_, fun z hv f => hz z (by rwa [map_natCast]) f⟩
  rw [← U.law_eq]
  exact hu k

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HodgeTateInclusionIntegralChartStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_inclusion_integralChart : ∀ (p : ℕ) [Fact p.Prime], HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), y.IsAlg → ∃ (N : ℕ) (u : Fin N → PS X.O 1 (chD Ch.ch)), (∀ k, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (u k)) ∧ ∀ z : X.O, X.v (algebraMap X.O X.C z) ^ (p - 1) ≤ X.v (p : X.C) → ∀ f : Fin (chD Ch.ch) → X.O, z • f ∈ Submodule.span X.O (Set.range fun k => dl (u k)) := by
  first | exact @GlobalTheory.CharDepth.hodgeTate_inclusion_intChart | exact GlobalTheory.CharDepth.hodgeTate_inclusion_intChart | (intros; apply GlobalTheory.CharDepth.hodgeTate_inclusion_intChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartDepthLeOfCharacterFlags
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterGermValuationEqColumnTyped
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonicalGaugeEigenvectorPairingIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonicalGaugeEigenvectorPairingIntegral
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem eigen_pair_mem_range : ∀ (R : Type) [CommRing R] (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d OE) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (σ : OE →+* R) (a0 : OE), IsUnit (σ a0 - σ (star a0)) → ∀ u u' : Fin d → R, (∀ a, (Pdiv.ChartF.linPart (B.A.act a)).mulVec u = σ a • u) → (∀ a, (Pdiv.ChartF.linPart (B.A.act a)).mulVec u' = σ a • u') → ∀ w : OE, dotProduct (fun i => algebraMap R k (u i)) ((ReciprocityTheory.ChartRestriction.G.TB.bilinPart k h).mulVec ((ReciprocityTheory.ChartRestriction.G.TB.dAct k B w).mulVec (fun i => algebraMap R k (u' i)))) ∈ (algebraMap R k).range := by
  intro R _ d OE _ _ k _ _ _ B h hc σ a0 ha u u' hu hu' w
  have key : ∀ v : Fin d → R, (∀ a, (Pdiv.ChartF.linPart (B.A.act a)).mulVec v = σ a • v) → ∀ a,
      (ReciprocityTheory.ChartRestriction.G.TB.dAct k B a).mulVec (fun i => algebraMap R k (v i)) =
        algebraMap R k (σ a) • (fun i => algebraMap R k (v i)) := by
    intro v hv a
    funext i
    have e := congrArg (algebraMap R k) (congrFun (hv a) i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, Pdiv.ChartF.linPart,
      Matrix.of_apply] at e ⊢
    rw [← e]
    rfl
  have h3 := GlobalTheory.bilinPart_eigen_mem_range R d OE k B h hc a0 u u' _ _ (key u hu a0) (key u' hu' (star a0)) ha
  rw [key u' hu' w, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  exact Subring.mul_mem _ ⟨_, rfl⟩ h3

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonicalGaugeEigenvectorPairingIntegralStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalGauge_eigenvector_pairing_integral : ∀ (R : Type) [CommRing R] (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d OE) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (σ : OE →+* R) (a0 : OE), IsUnit (σ a0 - σ (star a0)) → ∀ u u' : Fin d → R, (∀ a, (Pdiv.ChartF.linPart (B.A.act a)).mulVec u = σ a • u) → (∀ a, (Pdiv.ChartF.linPart (B.A.act a)).mulVec u' = σ a • u') → ∀ w : OE, dotProduct (fun i => algebraMap R k (u i)) ((ReciprocityTheory.ChartRestriction.G.TB.bilinPart k h).mulVec ((ReciprocityTheory.ChartRestriction.G.TB.dAct k B w).mulVec (fun i => algebraMap R k (u' i)))) ∈ (algebraMap R k).range := by
  first | exact @GlobalTheory.CharDepth.eigen_pair_mem_range | exact GlobalTheory.CharDepth.eigen_pair_mem_range | (intros; apply GlobalTheory.CharDepth.eigen_pair_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovariantDerivativeValueCharacterGerms
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovariantDerivativeValueCharacterGerms
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem nabVal_character_columns_of_canonGauge : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) :=
  GlobalTheory.nabVal_character_columns (GlobalTheory.exists_integral_germ_nabVal_congr
    GlobalTheory.canonGauge_dmonOf_hL_natCast_mul GlobalTheory.dmonOf_mul_congr_of_congr)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovariantDerivativeValueCharacterGermsStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covariantDerivative_value_character_germs : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) := by
  first | exact @GlobalTheory.nabVal_character_columns_of_canonGauge | exact GlobalTheory.nabVal_character_columns_of_canonGauge | (intros; apply GlobalTheory.nabVal_character_columns_of_canonGauge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterGermValuationEqColumnTyped
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharValue

def ballIdeal {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) (t : NNReal) (ht : 0 < t) : Ideal O where
  carrier := {y | v (algebraMap O C y) < t}
  zero_mem' := by simpa using ht
  add_mem' := by
    intro a b ha hb
    show v (algebraMap O C (a + b)) < t
    rw [map_add (f := _)]
    exact v.map_add_lt ha hb
  smul_mem' := by
    intro c a ha
    show v (algebraMap O C (c * a)) < t
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) ha

def letterEquiv (Ty : Type) (r : Ty → ℕ) (n : ℕ) : (Σ τ : Ty, Fin (r τ)) × Fin n ≃ Letter Ty r n where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun l := (⟨l.1, l.2.1⟩, l.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem dAct_mulVec {R : Type} [CommRing R] {d : ℕ} {OE : Type} [CommRing OE] [StarRing OE] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d OE) (a : OE) (u : Fin d → R) (s : R)
    (hu : (Pdiv.ChartF.linPart (B.A.act a)).mulVec u = s • u) :
    (TB.dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k s • (fun i => algebraMap R k (u i)) := by
  funext i
  have h := congrArg (algebraMap R k) (congrFun hu i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Pdiv.ChartF.linPart, Matrix.of_apply, map_sum, map_mul, Pi.smul_apply,
    smul_eq_mul] at h
  simp only [Matrix.mulVec, dotProduct, TB.dAct, FB.actK, MvPowerSeries.coeff_map, Pi.smul_apply, smul_eq_mul]
  exact h

theorem map_boxSer {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {n d : ℕ} (g : Fin n → PS R 1 d) :
    MvPowerSeries.map φ (PowGerm.boxSer g) = PowGerm.boxSer (fun b => MvPowerSeries.map φ (g b)) := by
  unfold PowGerm.boxSer
  rw [map_prod]
  exact Finset.prod_congr rfl fun b _ => (MvPowerSeries.rename_map _ φ (g b)).symm

theorem exists_germ_valuation_eq : ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (B : FB O d OE) (h : PS C 2 d), B.IsCanonGauge C h → ∀ (w0 : OE) (k n : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) [Fintype (Letter Ty r n)] (σ : Ty → (OE →+* O)) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → O), (∀ ℓ a, (Pdiv.ChartF.linPart (B.A.act a)).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ τ, ∃ a0, IsUnit (σ τ a0 - σ τ (star a0))) → (∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧ ∀ τ, ∃ a : OE, star a * a = (N : OE) ∧ v (algebraMap O C (σ τ a - 1)) < v (algebraMap O C x)) → ∀ (ty : Fin n → Ty) (P : MvPolynomial (Letter Ty r n) O), (∀ mo ∈ P.support, ∀ ℓ, mo ℓ ≠ 0 → ℓ.1 = ty ℓ.2.2) → ∀ χ : Fin n → PS O 1 d, (∀ b, IsCh B.G.F (χ b)) → MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P ≠ 0 → ∃ f : PS O n d, v (nabValN B C h w0 k (MvPowerSeries.map (algebraMap O C) f) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun (ℓ : Letter Ty r n) i => algebraMap O C (u ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap O C) P)) = v (algebraMap O C (MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P)) := by
  intro C _ _ v O _ _ hv d OE _ _ B h hg w0 k n Ty _ r _ σ u hu h0 hN ty P hP χ hχ hx
  classical
  obtain ⟨P', rfl⟩ : ∃ P', P = MvPolynomial.rename (letterEquiv Ty r n) P' :=
    ⟨MvPolynomial.rename (letterEquiv Ty r n).symm P, by simp [MvPolynomial.rename_rename]⟩
  rw [MvPolynomial.eval_rename] at hx ⊢
  set y : (Σ τ : Ty, Fin (r τ)) × Fin n → O :=
    (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) ∘ (letterEquiv Ty r n) with hy
  set x : O := MvPolynomial.eval y P' with hxdef
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hx0 : 0 < v (algebraMap O C x) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact fun e => hx (hinj (by rw [e, map_zero]))
  obtain ⟨N, hNlt, ha⟩ := hN x hx
  choose a ha1 ha2 using ha
  have hh : MvPowerSeries.constantCoeff h = 0 := by
    have := congrArg MvPowerSeries.constantCoeff hg.ax0
    rwa [TB.WickVanishing.gt_const_ev_eq _ (TB.WickVanishing.pair_points_zero_constant TB.WickVanishing.gp_zero₂ (TB.WickVanishing.gp_pt 0)), map_zero] at this
  obtain ⟨g, ρ, hρ, hsum⟩ := GlobalTheory.T.covariantDerivative_value_character_germs O d OE C B h hg hinj w0 N k n (ballIdeal hv _ hx0)
    (by show v (algebraMap O C (N : O)) < _; rwa [map_natCast]) (fun b => a (ty b)) (fun _ => 1)
    (fun b => by rw [ha1, mul_one]) (Σ τ : Ty, Fin (r τ)) u (fun b => {l | l.1 = ty b})
    (fun b l => σ l.1 (a (ty b)))
    (fun b l hl => by
      have hl' : l.1 = ty b := hl
      have h2 : v (algebraMap O C (σ l.1 (a (ty b)) - 1)) < v (algebraMap O C x) := by
        rw [hl']; exact ha2 _
      refine ⟨h2, ?_, dAct_mulVec C B _ _ _ (hu l _)⟩
      apply hv.isUnit_of_one'
      have h3 := v.map_one_add_of_lt (lt_of_lt_of_le h2 (hv.map_le_one x))
      rwa [map_sub, map_one, add_sub_cancel] at h3)
    (fun b l hl l' hl' => by
      have e1 : l.1 = ty b := hl
      have e2 : l'.1 = ty b := hl'
      obtain ⟨a0, ha0⟩ := h0 (ty b)
      exact GlobalTheory.T.canonicalGauge_eigenvector_pairing_integral O d OE C B h hg (σ (ty b)) a0 ha0 (u l) (u l') (fun c => e1 ▸ hu l c)
        (fun c => e2 ▸ hu l' c) _)
    χ y (fun b => (hχ b).1)
    (fun b l _ => GlobalTheory.MultiplicativeSeries.main O d B.G (χ b) (hχ b).2 (u l))
    P' (fun mo hmo l b hne => by
      have hmem : Finsupp.mapDomain (letterEquiv Ty r n) mo ∈
          (MvPolynomial.rename (letterEquiv Ty r n) P').support := by
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_rename_mapDomain _ (letterEquiv Ty r n).injective]
        exact MvPolynomial.mem_support_iff.1 hmo
      exact hP _ hmem (letterEquiv Ty r n (l, b))
        (by rwa [Finsupp.mapDomain_apply_of_injective (letterEquiv Ty r n).injective]))
  refine ⟨PowGerm.boxSer g, ?_⟩
  rw [map_boxSer, MvPolynomial.map_rename,
    GlobalTheory.nabValN_boxSer O d OE B C h w0 hh k n _ (Σ τ : Ty, Fin (r τ)) (Letter Ty r n) (letterEquiv Ty r n) _
      (fun l i => algebraMap O C (u l i)) _ (fun _ => rfl) (fun _ => rfl),
    MvPolynomial.support_map_of_injective _ hinj]
  simp only [MvPolynomial.coeff_map]
  rw [hsum, map_add (f := _)]
  exact v.map_add_eq_of_lt_left hρ

end GlobalTheory.CharValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterGermValuationEqColumnTypedStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characterGerm_valuation_eq_columnTyped : ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (B : FB O d OE) (h : PS C 2 d), B.IsCanonGauge C h → ∀ (w0 : OE) (k n : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) [Fintype (Letter Ty r n)] (σ : Ty → (OE →+* O)) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → O), (∀ ℓ a, (Pdiv.ChartF.linPart (B.A.act a)).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ τ, ∃ a0, IsUnit (σ τ a0 - σ τ (star a0))) → (∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧ ∀ τ, ∃ a : OE, star a * a = (N : OE) ∧ v (algebraMap O C (σ τ a - 1)) < v (algebraMap O C x)) → ∀ (ty : Fin n → Ty) (P : MvPolynomial (Letter Ty r n) O), (∀ mo ∈ P.support, ∀ ℓ, mo ℓ ≠ 0 → ℓ.1 = ty ℓ.2.2) → ∀ χ : Fin n → PS O 1 d, (∀ b, IsCh B.G.F (χ b)) → MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P ≠ 0 → ∃ f : PS O n d, v (nabValN B C h w0 k (MvPowerSeries.map (algebraMap O C) f) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun (ℓ : Letter Ty r n) i => algebraMap O C (u ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap O C) P)) = v (algebraMap O C (MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P)) := by
  first | exact @GlobalTheory.CharValue.exists_germ_valuation_eq | exact GlobalTheory.CharValue.exists_germ_valuation_eq | (intros; apply GlobalTheory.CharValue.exists_germ_valuation_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBlockPolynomialGeProd
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBlockPolynomialGeProd
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem valuation_blockPoly_ge : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Ty : Type) [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) (β : (Σ τ : Ty, Fin (r τ)) → Fin n), Function.Injective β → ∀ (a : Ty → ℕ → ℕ), Crude.Dom r a → ∀ (yv : Letter Ty r n → O) (x : Ty → NNReal), (∀ τ, x τ ≤ 1) → (∀ τ (i : Fin (r τ)), x τ ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => yv ⟨τ, Fin.castLE i.isLt a, β ⟨τ, Fin.castLE i.isLt b⟩⟩).det)) → (∏ τ, x τ ^ (a τ 0) ≤ v (algebraMap O C (MvPolynomial.eval yv (Crude.crP r n O β a)))) ∧ ∀ mo ∈ (Crude.crP r n O β a).support, ∀ ℓ, mo ℓ ≠ 0 → ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2 := by
  intro C _ v O _ _ _ Ty _ _ r n β _ a ha yv x hx hmin
  refine ⟨?_, fun mo hmo ℓ hℓ => ?_⟩
  · unfold Crude.crP
    rw [map_prod, map_prod, map_prod]
    refine Finset.prod_le_prod' fun τ _ => ?_
    rw [map_prod, map_prod, map_prod]
    have h1 : x τ ^ (a τ 0) ≤ ∏ kk : Fin (r τ), x τ ^ Crude.crExp r a τ kk := by
      rw [Finset.prod_pow_eq_pow_sum]
      refine pow_le_pow_of_le_one zero_le (hx τ) ?_
      rcases Nat.eq_zero_or_pos (r τ) with h0 | h0
      · haveI : IsEmpty (Fin (r τ)) := by rw [h0]; infer_instance
        simp
      · have := Crude.crExpSum a ha τ ⟨0, h0⟩
        simp only [Nat.zero_lt_succ, if_true] at this
        exact this.le
    refine h1.trans (Finset.prod_le_prod' fun kk _ => ?_)
    rw [map_pow, map_pow, map_pow]
    refine pow_le_pow_left₀ zero_le ?_ _
    have h2 : MvPolynomial.eval yv (Crude.crMinor r n O β τ kk).det =
        (Matrix.of fun a b : Fin (kk.val + 1) =>
          yv ⟨τ, Fin.castLE kk.isLt a, β ⟨τ, Fin.castLE kk.isLt b⟩⟩).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [Crude.crMinor, RingHom.mapMatrix_apply]
    rw [h2]
    exact hmin τ kk
  · exact MvPolynomial.mem_supported.1 (Crude.crP_mem_supported O β a)
      ((MvPolynomial.mem_vars_iff_mem_support ℓ).2 ⟨mo, hmo, Finsupp.mem_support_iff.2 hℓ⟩)

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBlockPolynomialGeProdStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_blockPolynomial_ge_prod : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Ty : Type) [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) (β : (Σ τ : Ty, Fin (r τ)) → Fin n), Function.Injective β → ∀ (a : Ty → ℕ → ℕ), Crude.Dom r a → ∀ (yv : Letter Ty r n → O) (x : Ty → NNReal), (∀ τ, x τ ≤ 1) → (∀ τ (i : Fin (r τ)), x τ ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => yv ⟨τ, Fin.castLE i.isLt a, β ⟨τ, Fin.castLE i.isLt b⟩⟩).det)) → (∏ τ, x τ ^ (a τ 0) ≤ v (algebraMap O C (MvPolynomial.eval yv (Crude.crP r n O β a)))) ∧ ∀ mo ∈ (Crude.crP r n O β a).support, ∀ ℓ, mo ℓ ≠ 0 → ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2 := by
  first | exact @GlobalTheory.CharDepth.valuation_blockPoly_ge | exact GlobalTheory.CharDepth.valuation_blockPoly_ge | (intros; apply GlobalTheory.CharDepth.valuation_blockPoly_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartDepthLeOfCharacterFlags
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem crP_map_ringHom {Ty : Type} [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) {R S : Type} [CommRing R]
    [CommRing S] (φ : R →+* S) (β : (Σ σ : Ty, Fin (r σ)) → Fin n) (a : Ty → ℕ → ℕ) :
    MvPolynomial.map φ (Crude.crP r n R β a) = Crude.crP r n S β a := by
  rw [← Crude.crP_map R, ← Crude.crP_map S, MvPolynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

theorem exists_col_extend {ι κ α : Type} (β : ι → κ) (hβ : Function.Injective β) (g : ι → α) (x : α) :
    ∃ G : κ → α, (∀ i, G (β i) = g i) ∧ ∀ b, G b = x ∨ ∃ i, G b = g i := by
  classical
  refine ⟨Function.extend β g (fun _ => x), fun i => hβ.extend_apply _ _ _, fun b => ?_⟩
  by_cases hb : ∃ i, β i = b
  · obtain ⟨i, rfl⟩ := hb
    exact Or.inr ⟨i, hβ.extend_apply _ _ _⟩
  · exact Or.inl (Function.extend_apply' _ _ _ hb)

theorem nuLocC_le_of_character_flags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → (∀ τ, ∃ a0, IsUnit (τO τ a0 - τO τ (star a0))) → (∀ x : X.O, x ≠ 0 → ∃ N : ℕ, X.v (N : X.C) < X.v (algebraMap X.O X.C x) ∧ ∀ τ, ∃ a : 𝓞 E, star a * a = (N : 𝓞 E) ∧ X.v (algebraMap X.O X.C (τO τ a - 1)) < X.v (algebraMap X.O X.C x)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ (len : (E →+* ℂ) → ℝ), (∀ τ, 0 ≤ len τ) → (∀ τ, ∃ χ : Fin (Dw.mult τ) → PS X.O 1 (chD Ch.ch), (∀ b, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (χ b)) ∧ ∀ i : Fin (Dw.mult τ), (X.v (p : X.C) : ℝ) ^ len τ ≤ (X.v (algebraMap X.O X.C (Matrix.of fun s b : Fin (i.val + 1) => ∑ j, X.ι (Ch.uvecT ⟨τ, Fin.castLE i.isLt s⟩ j) * dl (χ (Fin.castLE i.isLt b)) j).det) : ℝ)) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * ∑ τ, len τ * (a (τ, 0) : ℝ) : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X τO hty hun happ e k n a he ha hn len hlen hχ
  classical
  obtain ⟨B, hF, hact, hg⟩ := GlobalTheory.T.exists_formalBiextension_integral_chart_valuedExtension E H Dw l Xo c T io y Ch p X
  choose χ hχ1 hχ2 using hχ
  have hβ : Function.Injective (colP Dw hn) := fun p q h =>
    (Fintype.equivFin _).injective (Fin.castLE_injective hn h)
  obtain ⟨ty, hty1, -⟩ := exists_col_extend (colP Dw hn) hβ (fun q : Lt1 Dw => q.1) (Classical.arbitrary _)
  obtain ⟨χ', hχ'1, hχ'2⟩ := exists_col_extend (colP Dw hn) hβ (fun q : Lt1 Dw => χ q.1 q.2) 1
  have hp0 : X.v (p : X.C) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hp1 : X.v (p : X.C) ≤ 1 := by
    have := X.ints.map_le_one (p : X.O)
    rwa [map_natCast] at this
  obtain ⟨hval, hsupp⟩ := GlobalTheory.T.valuation_blockPolynomial_ge_prod X.C X.v X.O X.ints (E →+* ℂ) Dw.mult n (colP Dw hn) hβ
    (fun τ i => a (τ, i)) ha
    (fun ℓ : LtN Dw n => ∑ j, X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ j) * dl (χ' ℓ.2.2) j)
    (fun τ => X.v (p : X.C) ^ len τ) (fun τ => NNReal.rpow_le_one hp1 (hlen τ))
    (fun τ i => by
      have h := hχ2 τ i
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
      simp only [hχ'1]
      exact h)
  have hprod : ∏ τ, (X.v (p : X.C) ^ len τ) ^ (a (τ, 0)) =
      X.v (p : X.C) ^ (∑ τ, len τ * (a (τ, 0) : ℝ)) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_rpow, Real.rpow_sum_of_pos (by exact_mod_cast pos_iff_ne_zero.2 hp0), NNReal.coe_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [NNReal.coe_pow, NNReal.coe_rpow, Real.rpow_mul_natCast (NNReal.coe_nonneg _)]
  rw [hprod] at hval
  have hne : MvPolynomial.eval
      (fun ℓ : LtN Dw n => ∑ j, X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ j) * dl (χ' ℓ.2.2) j)
      (Crude.crP Dw.mult n X.O (colP Dw hn) (fun τ i => a (τ, i))) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hval
    exact absurd hval (not_le.2 (NNReal.rpow_pos (pos_iff_ne_zero.2 hp0)))
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_characterGerm_valuation_eq_columnTyped X.C X.v X.O X.ints (chD Ch.ch) (𝓞 E) B _ hg H.w0 k n (E →+* ℂ) Dw.mult τO
    (fun q j => X.ι (Ch.uvecT q j))
    (fun q a0 => by
      rw [hact]
      exact (GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers E H Dw l Xo c T io y Ch p X τO hty q.1).1.1 q.2 a0)
    hun happ ty (Crude.crP Dw.mult n X.O (colP Dw hn) (fun τ i => a (τ, i)))
    (fun mo hmo ℓ hℓ => by
      obtain ⟨i, hi⟩ := hsupp mo hmo ℓ hℓ
      rw [← hi, hty1])
    χ'
    (fun b => by
      rw [hF]
      rcases hχ'2 b with h | ⟨q, h⟩
      · rw [h]
        exact ⟨by simp, by simp⟩
      · rw [h]
        exact hχ1 q.1 q.2)
    hne
  refine GlobalTheory.T.chart_local_depth_le_of_valuedExtension_bound E H Dw l Xo c T io y Ch p X B hF hact e k n a he
    (Crude.crP Dw.mult n X.O (colP Dw hn) (fun τ i => a (τ, i))) ?_ f _ ?_
  · rw [crP_map_ringHom, ← Crude.crP_map]
    exact (Crude.Pmin_mem Dw.mult n X.C (colP Dw hn) _ ⊤ _ _ (fun τ _ => conj_ne_self_of_CM τ) hβ ha).1
  · rw [← NNReal.coe_rpow, NNReal.coe_le_coe]
    exact hval.trans (le_of_eq hf.symm)

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartDepthLeOfCharacterFlagsStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDepth_le_of_characterFlags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → (∀ τ, ∃ a0, IsUnit (τO τ a0 - τO τ (star a0))) → (∀ x : X.O, x ≠ 0 → ∃ N : ℕ, X.v (N : X.C) < X.v (algebraMap X.O X.C x) ∧ ∀ τ, ∃ a : 𝓞 E, star a * a = (N : 𝓞 E) ∧ X.v (algebraMap X.O X.C (τO τ a - 1)) < X.v (algebraMap X.O X.C x)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ (len : (E →+* ℂ) → ℝ), (∀ τ, 0 ≤ len τ) → (∀ τ, ∃ χ : Fin (Dw.mult τ) → PS X.O 1 (chD Ch.ch), (∀ b, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (χ b)) ∧ ∀ i : Fin (Dw.mult τ), (X.v (p : X.C) : ℝ) ^ len τ ≤ (X.v (algebraMap X.O X.C (Matrix.of fun s b : Fin (i.val + 1) => ∑ j, X.ι (Ch.uvecT ⟨τ, Fin.castLE i.isLt s⟩ j) * dl (χ (Fin.castLE i.isLt b)) j).det) : ℝ)) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * ∑ τ, len τ * (a (τ, 0) : ℝ) : ℝ) : EReal) := by
  first | exact @GlobalTheory.CharDepth.nuLocC_le_of_character_flags | exact GlobalTheory.CharDepth.nuLocC_le_of_character_flags | (intros; apply GlobalTheory.CharDepth.nuLocC_le_of_character_flags <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersLeadingMinorsGeHodgeTate
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersLeadingMinorsGeHodgeTate
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_chars_leading_minors_ge :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d s N : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O), Function.Surjective (res w) → ∀ (u : Fin N → PS O 1 d), (∀ k, IsCh F (u k)) → ∀ c : O, c ≠ 0 → (∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range fun k => dl (u k))) → ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, v (algebraMap O C c) ^ s ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  intro C _ v O _ _ hv d s N F w hw u hu c hc hspan
  have hA : ∀ y : Fin s → O,
      c • y ∈ Submodule.span O (Set.range fun k => res w (dl (u k))) := by
    intro y
    obtain ⟨f, rfl⟩ := hw y
    have h1 : (Set.range fun k => res w (dl (u k))) = res w '' (Set.range fun k => dl (u k)) := by
      rw [← Set.range_comp]
      rfl
    rw [h1, ← Submodule.map_span, ← map_smul]
    exact Submodule.mem_map_of_mem (hspan f)
  obtain ⟨t, ht, hmin⟩ := GlobalTheory.exists_leading_minors_ge C v O hv s _ c hc hA
  choose k hk using ht
  refine ⟨fun b => u (k b), fun b => hu _, fun i => ?_⟩
  have hm : (Matrix.of fun a b : Fin (i.val + 1) =>
      ∑ j, w (Fin.castLE i.isLt a) j * dl (u (k (Fin.castLE i.isLt b))) j) =
      Matrix.of fun a b : Fin (i.val + 1) => t (Fin.castLE i.isLt b) (Fin.castLE i.isLt a) := by
    ext a b
    rw [Matrix.of_apply, Matrix.of_apply, ← hk]
    simp [res, Matrix.mulVec, dotProduct]
  rw [hm]
  exact (pow_le_pow_right_of_le_one' (hv.map_le_one c) i.isLt).trans (hmin i)

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersLeadingMinorsGeHodgeTateStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characters_leading_minors_valuation_ge : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d s N : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O), Function.Surjective (res w) → ∀ (u : Fin N → PS O 1 d), (∀ k, IsCh F (u k)) → ∀ c : O, c ≠ 0 → (∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range fun k => dl (u k))) → ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, v (algebraMap O C c) ^ s ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  first | exact @GlobalTheory.CharDepth.exists_chars_leading_minors_ge | exact GlobalTheory.CharDepth.exists_chars_leading_minors_ge | (intros; apply GlobalTheory.CharDepth.exists_chars_leading_minors_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDepthLeResidueCharTwo
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem sum_log_div_log_le_of_rpow_le_prod {ι : Type} (S : Finset ι) (x : ι → ℝ) (r B : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (hx : ∀ i ∈ S, x i ≠ 0) (h : r ^ B ≤ ∏ i ∈ S, x i) :
    ∑ i ∈ S, Real.log (x i) / Real.log r ≤ B := by
  have hl : Real.log r < 0 := Real.log_neg hr0 hr1
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hr0 B) h
  rw [Real.log_rpow hr0, Real.log_prod hx] at h1
  rw [← Finset.sum_div, div_le_iff_of_neg hl]
  exact h1

theorem nuLocC_le_over_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ¬ IsUnit ((p : ℕ) : T.V) → UpperTheory.Depth.SplitAt H.d p → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuLocC Ch e k a n ≤ (((vV T.V ((p : ℕ) : T.Fr) : ℝ) / (e : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  intro p _ hAv hHT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch hy h2 hsp f vd hvd htp e k n a he hdom hn Ap hAp haA
  classical
  obtain ⟨X⟩ := GlobalTheory.T.nonempty_closedValuedExtensionOfCDVR T p h2
  obtain ⟨τT, -, hty, -⟩ := GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring E H l c T io p X
  obtain ⟨hw0, happ⟩ := UpperTheory.cmDatum_splitPlaces_conj_stable p Fact.out E H hsp X.C X.v X.O X.ints X.nonunit.out
  obtain ⟨xs, hxs, hprod⟩ := GlobalTheory.T.integralChart_colength_bound_prime_two p hAv E H Dw l Xo c T io y Ch X hy f vd htp
  obtain ⟨N, u, hu, hspan⟩ := GlobalTheory.T.hodgeTate_inclusion_integralChart p hHT E H Dw l Xo c T io y Ch X hy
  have h2C : algebraMap X.O X.C ((p : ℕ) : X.O) = ((p : ℕ) : X.C) := map_natCast _ _
  have h2C0 : ((p : ℕ) : X.C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h2O0 : ((p : ℕ) : X.O) ≠ 0 := fun h => h2C0 (by rw [← h2C, h, map_zero])
  have hr0 : (0 : ℝ) < (X.v ((p : ℕ) : X.C) : ℝ) := by
    have : X.v ((p : ℕ) : X.C) ≠ 0 := (Valuation.ne_zero_iff _).2 h2C0
    exact_mod_cast pos_iff_ne_zero.2 this
  have hr1 : (X.v ((p : ℕ) : X.C) : ℝ) < 1 := by
    have hle : X.v ((p : ℕ) : X.C) ≤ 1 := by rw [← h2C]; exact X.ints.map_le_one _
    have hne : X.v ((p : ℕ) : X.C) ≠ 1 := fun h =>
      X.nonunit.out (X.ints.isUnit_iff_valuation_eq_one.2 (by rw [h2C]; exact h))
    exact_mod_cast lt_of_le_of_ne hle hne
  set r : ℝ := (X.v ((p : ℕ) : X.C) : ℝ) with hr
  have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
  have hxs0 : ∀ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.1 (lt_of_lt_of_le (Real.rpow_pos_of_pos hr0 _) hprod).ne'
  have hxs0' : ∀ τ, InPsi H τ → xs τ ≠ 0 := fun τ hτ h =>
    hxs0 τ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ⟩) (by rw [h]; rfl)
  let len : (E →+* ℂ) → ℝ := fun τ => if InPsi H τ then Real.log (xs τ) / Real.log r else (Dw.q : ℝ)
  have hlen0 : ∀ τ, 0 ≤ len τ := by
    intro τ
    by_cases hτ : InPsi H τ
    · simp only [len, if_pos hτ]
      have h1 := (GlobalTheory.T.exists_flag_characters_leading_minors_colength X.C X.v X.O X.ints _ _ _ _ _ (hxs τ hτ) (hxs0' τ hτ)).1
      exact div_nonneg_of_nonpos (Real.log_nonpos (xs τ).2 (by exact_mod_cast h1)) hlog.le
    · simp only [len, if_neg hτ]
      exact Nat.cast_nonneg _
  have key := GlobalTheory.T.chartDepth_le_of_characterFlags E H Dw l Xo c T io y Ch p X _ hty (fun τ => ⟨H.w0, hw0 _⟩)
    (fun x hx => by
      obtain ⟨M, hM, hM'⟩ := happ x hx
      exact ⟨M, hM, fun τ => hM' _⟩) e k n a he hdom hn len hlen0 (by
      intro τ
      by_cases hτ : InPsi H τ
      · obtain ⟨-, χ, hχ, hχ'⟩ := GlobalTheory.T.exists_flag_characters_leading_minors_colength X.C X.v X.O X.ints _ _ _ _ _ (hxs τ hτ) (hxs0' τ hτ)
        refine ⟨χ, hχ, fun i => ?_⟩
        have hpos : (0 : ℝ) < xs τ := by exact_mod_cast pos_iff_ne_zero.2 (hxs0' τ hτ)
        have : r ^ len τ = xs τ := by
          simp only [len, if_pos hτ]
          rw [Real.rpow_def_of_pos hr0, mul_div_cancel₀ _ hlog.ne, Real.exp_log hpos]
        rw [← hr, this]
        exact_mod_cast hχ' i
      · obtain ⟨χ, hχ, hχ'⟩ := GlobalTheory.T.exists_characters_leading_minors_valuation_ge X.C X.v X.O X.ints _ _ N _ _
          (GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers E H Dw l Xo c T io y Ch p X _ hty τ).2 u hu ((p : ℕ) : X.O) h2O0
          (hspan _ (by
            rw [h2C]
            have hle : X.v ((p : ℕ) : X.C) ≤ 1 := by exact_mod_cast hr1.le
            exact pow_le_of_le_one zero_le hle (by have := (Fact.out : p.Prime).two_le; omega)))
        refine ⟨χ, hχ, fun i => ?_⟩
        have hm : Dw.mult τ = Dw.q := if_neg hτ
        have : r ^ len τ = ((X.v (algebraMap X.O X.C ((p : ℕ) : X.O)) ^ Dw.mult τ : NNReal) : ℝ) := by
          simp only [len, if_neg hτ]
          rw [Real.rpow_natCast, h2C, hm, NNReal.coe_pow]
        rw [← hr, this]
        exact_mod_cast hχ' i)
  refine key.trans (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left ?_ ?_))
  · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => InPsi H τ)]
    refine add_le_add ?_ (le_of_eq ?_)
    · have hsum := sum_log_div_log_le_of_rpow_le_prod _ (fun τ => (xs τ : ℝ)) r _ hr0 hr1 hxs0 hprod
      refine le_trans ?_ (mul_le_mul_of_nonneg_right hsum hAp)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun τ hτ => ?_
      have hτ' : InPsi H τ := (Finset.mem_filter.1 hτ).2
      have h0 := hlen0 τ
      simp only [len, if_pos hτ'] at h0 ⊢
      exact mul_le_mul_of_nonneg_left (haA τ hτ') h0
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have hτ' : ¬ InPsi H τ := (Finset.mem_filter.1 hτ).2
      simp only [len, if_neg hτ']
  · have h0 := GlobalTheory.vV_algebraMap_nonneg_dvr T ((p : ℕ) : T.V)
    rw [map_natCast] at h0
    exact div_nonneg (by exact_mod_cast h0) (Nat.cast_nonneg _)

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDepthLeResidueCharTwoStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralChartDepth_le_residueChar_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ¬ IsUnit ((p : ℕ) : T.V) → UpperTheory.Depth.SplitAt H.d p → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuLocC Ch e k a n ≤ (((vV T.V ((p : ℕ) : T.Fr) : ℝ) / (e : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  first | exact @GlobalTheory.CharDepth.nuLocC_le_over_two | exact GlobalTheory.CharDepth.nuLocC_le_over_two | (intros; apply GlobalTheory.CharDepth.nuLocC_le_over_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBoundAtResidueCharacteristic
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem ramOverZ_pos_place {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 < ramOverZ la := by
  have h := Crude.crv_vLa_char la
  rw [Crude.crv_vLa_natCast_eq] at h
  have h0 : ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (Crude.resCharOf_prime la).ne_zero
  have h1 : la.intValuation ((resCharOf la : ℕ) : 𝓞 K) < 1 :=
    (la.intValuation_lt_one_iff_mem _).2 (Crude.crv_char_mem la)
  have h2 : WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K)) < 0 := by
    have := (WithZero.log_lt_log (la.intValuation_ne_zero _ h0) one_ne_zero).2 h1
    simpa using this
  omega

theorem vV_eq_zero_of_isUnit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have h : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hx
  simp [vV, h]

theorem nuW_le_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitAt H.d p → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la = p → ∀ (k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuW Xo c la k a n ≤ (((ramOverZ la : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  intro p _ hA hH E _ _ _ H Dw l Xo c inst hst f vd hvd hsp hT la hla k n a ha hn Ap hAp hle
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starSt E H inst hst
  letI := H.starRing
  have hE : IntChartEx Xo c := (GlobalTheory.IntChartExists.intChart_exists E H Dw l Xo c).2.1 hst
  refine max_le ?_ ?_
  · rw [EReal.coe_nonneg]
    positivity
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho => iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  have hv : vV T.V ((p : ℕ) : T.Fr) = (e : ℤ) * (ramOverZ la : ℤ) := by
    rw [← map_natCast io, ho.2, ← hla, Crude.crv_vLa_char]
  have he : 0 < e := ho.1
  have hnu : ¬ IsUnit ((p : ℕ) : T.V) := by
    intro hu
    have h0 := vV_eq_zero_of_isUnit T hu
    rw [map_natCast, hv] at h0
    have := ramOverZ_pos_place la
    have : (0 : ℤ) < (e : ℤ) * (ramOverZ la : ℤ) := by positivity
    omega
  refine (iInf_le _ C).trans ((GlobalTheory.T.integralChartDepth_le_residueChar_two p hA hH E H Dw l Xo c T io y C hy hnu hsp f vd hvd hT e k n a he ha hn Ap hAp hle).trans (le_of_eq ?_))
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  rw [hv, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_cancel_left₀ _ he']

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBoundAtResidueCharacteristicStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unscaledDepth_le_placeOverTwo : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitAt H.d p → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la = p → ∀ (k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuW Xo c la k a n ≤ (((ramOverZ la : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  first | exact @GlobalTheory.CharDepth.nuW_le_two | exact GlobalTheory.CharDepth.nuW_le_two | (intros; apply GlobalTheory.CharDepth.nuW_le_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SizesBoundAtTwoFirstRowsWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SizesBoundAtTwoFirstRowsWeights
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.L2.DIV hiding conjPl
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem vd2_nonneg_of_D7 (D : D7) : 0 ≤ vd2 D := by
  unfold vd2
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast D.host.QS_pos)

theorem sizes_two_arith (T f q m v A S C b Sc η : ℝ) (hf : 0 ≤ f) (hq : 0 ≤ q) (hqm : q ≤ m) (hv : 0 ≤ v)
    (hC : 1 ≤ C) (hb : 0 ≤ b) (hSc : 0 ≤ Sc) (hη : 0 ≤ η) (hA : T * A = 2 * b + Sc) (hS : T * S ≤ f * η) :
    T * (f * q * (1 + v / 2) * A + q * S) ≤ C * m * (2 + v) * (2 * f * b + f * (Sc + η)) := by
  have hm : 0 ≤ m := hq.trans hqm
  have e1 : T * (f * q * (1 + v / 2) * A + q * S) = q * (f * (1 + v / 2) * (2 * b + Sc) + T * S) := by
    rw [← hA]; ring
  have h1 : f * (1 + v / 2) * (2 * b + Sc) + T * S ≤ (2 + v) * (2 * f * b + f * (Sc + η)) := by
    have p1 : 0 ≤ f * (1 + v / 2) * (2 * b + Sc) := by positivity
    have p2 : 0 ≤ (1 + v) * (f * η) := by positivity
    nlinarith
  have h0 : 0 ≤ (2 + v) * (2 * f * b + f * (Sc + η)) := by positivity
  rw [e1]
  calc q * (f * (1 + v / 2) * (2 * b + Sc) + T * S) ≤ q * ((2 + v) * (2 * f * b + f * (Sc + η))) :=
        mul_le_mul_of_nonneg_left h1 hq
    _ ≤ m * ((2 + v) * (2 * f * b + f * (Sc + η))) := mul_le_mul_of_nonneg_right hqm h0
    _ ≤ C * (m * ((2 + v) * (2 * f * b + f * (Sc + η)))) := le_mul_of_one_le_left (mul_nonneg hm h0) hC
    _ = _ := by ring

theorem sizes_bound_two : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (Q : Par D), Q.Pins → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ C : ℝ, 1 ≤ C → ∀ j, InR D j → ∃ Ap : ℝ, 0 ≤ Ap ∧ (∀ τ, InPsi Q.H τ → (wtA (lR Tp hK j) (τ, 0) : ℝ) ≤ Ap) ∧ (open Classical in (Tp.TO : ℝ) * ((D.R.f : ℝ) * (Q.Dw j).q * (1 + vd2 D / 2) * Ap + (Q.Dw j).q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi Q.H τ), (wtA (lR Tp hK j) (τ, 0) : ℝ)) ≤ C * D.R.m * (2 + vd2 D) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz))) := by
  classical
  intro D L Pm Tp hK Q hQ hx hkb C hC j hj
  obtain ⟨hSe, hw⟩ := GlobalTheory.T.cloudSizes_between_zero_and_twice_b D L Pm hx hkb
  obtain ⟨hw1, -, -⟩ := hw j hj
  obtain ⟨-, -, hP, hN, hwt⟩ := GlobalTheory.T.weightExponents_embeddings_degree D Q hQ j hj (lR Tp hK j)
  have hT : (0 : ℝ) < (Tp.TO : ℝ) := by exact_mod_cast TO_pos Tp
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hSc := L.Sc_pos.le
  have hη := L.etaSz_pos.le
  have hplus : ∀ t, (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aP t) 0 : ℝ) ≤ 2 * L.sc.b + L.Sc := by
    intro t
    unfold Formalism.L2.Pj.ext0
    split_ifs with h
    · have h1 : (Tp.TO : ℝ) * ((lR Tp hK j).aP t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aP t ⟨0, h⟩ : ℝ) := by
        exact_mod_cast (GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK j t).1 ⟨0, h⟩
      obtain ⟨h2, h3, -⟩ := GlobalTheory.T.kappaRows_entries_le_sizes D L Pm Tp hK j hj t
      rcases Nat.lt_or_ge 0 (D.R.k - 1) with hk | hk
      · have := h2 ⟨0, h⟩ hk
        have := (hw1 t).2
        linarith
      · have := h3 ⟨0, h⟩ hk
        linarith
    · simp only [Nat.cast_zero, mul_zero]; linarith
  have hminus : ∀ t, (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aM t) 0 : ℝ) ≤ L.etaSz := by
    intro t
    unfold Formalism.L2.Pj.ext0
    split_ifs with h
    · have h1 : (Tp.TO : ℝ) * ((lR Tp hK j).aM t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aM t ⟨0, h⟩ : ℝ) := by
        exact_mod_cast (GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK j t).2.1 ⟨0, h⟩
      exact h1.trans ((GlobalTheory.T.kappaRows_entries_le_sizes D L Pm Tp hK j hj t).2.2 _)
    · simpa using hη
  refine ⟨(2 * L.sc.b + L.Sc) / Tp.TO, by positivity, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨t, rfl⟩ := (hP τ).1 hτ
    rw [(hwt t 0).1, le_div_iff₀ hT, mul_comm]
    exact hplus t
  · have hq : (Q.Dw j).q ≤ D.R.m := by
      rw [(hQ.2.2.2 j hj).2.1]
      exact Nat.sub_le _ _
    refine sizes_two_arith _ _ _ _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hq)
      (vd2_nonneg_of_D7 D) hC hb hSc hη (by field_simp) ?_
    rw [Finset.mul_sum]
    have hcard : (Finset.univ.filter (fun τ => ¬ InPsi Q.H τ)).card ≤ D.R.f := by
      rw [← (GlobalTheory.T.realPlaceLabel_bijective_card_eq_f D).2, ← Finset.card_univ]
      refine le_trans (Finset.card_le_card ?_)
        (Finset.card_image_le (f := fun t => ComplexEmbedding.conjugate (DV.tauEmb D t)))
      intro τ hτ
      obtain ⟨t, rfl⟩ := (hN τ).1 (Finset.mem_filter.1 hτ).2
      exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩
    refine (Finset.sum_le_card_nsmul _ _ L.etaSz ?_).trans ?_
    · intro τ hτ
      obtain ⟨t, rfl⟩ := (hN τ).1 (Finset.mem_filter.1 hτ).2
      rw [(hwt t 0).2]
      exact hminus t
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hη

end GlobalTheory.RunDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SizesBoundAtTwoFirstRowsWeightsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.L2.DIV hiding conjPl
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_bound_at_two_first_rows_weights : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (Q : Par D), Q.Pins → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ C : ℝ, 1 ≤ C → ∀ j, InR D j → ∃ Ap : ℝ, 0 ≤ Ap ∧ (∀ τ, InPsi Q.H τ → (wtA (lR Tp hK j) (τ, 0) : ℝ) ≤ Ap) ∧ (open Classical in (Tp.TO : ℝ) * ((D.R.f : ℝ) * (Q.Dw j).q * (1 + vd2 D / 2) * Ap + (Q.Dw j).q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi Q.H τ), (wtA (lR Tp hK j) (τ, 0) : ℝ)) ≤ C * D.R.m * (2 + vd2 D) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz))) := by
  first | exact @GlobalTheory.RunDepth.sizes_bound_two | exact GlobalTheory.RunDepth.sizes_bound_two | (intros; apply GlobalTheory.RunDepth.sizes_bound_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthAtTwoOfUnscaledDepthBound
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SprimeNonnegTwo
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.L2.DIV hiding conjPl
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

set_option autoImplicit false

namespace GlobalTheory.RunDepth

theorem sprime_nonneg_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ), O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → PiSplit (H := H) Dd → LeafPage O → ∀ v : HeightOneSpectrum (𝓞 K), plc v ∈ O.sm → ∀ j, 0 ≤ DepthTie.s1T Xo c Dd O ι v j := by
  intro E _ _ _ H l Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι hT hpr hσ hsp hPg v hv j
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hg1p, hg2p, hq1p, hdp, -, -, -, -, -, -, hg1t, hg2t, -, -, -⟩ := hPg
  obtain ⟨h1, h2, h3, h4, h5⟩ := hpr
  have hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime :=
    ⟨h1 ▸ hg1p, h2 ▸ hg2p, h3 ▸ hq1p, h4 ▸ hdp⟩
  have hn1 : plc v ≠ Dd.Q.g1 := by
    rw [← h1]; exact fun h => hg1t (h ▸ hv)
  have hn2 : plc v ≠ Dd.Q.g2 := by
    rw [← h2]; exact fun h => hg2t (h ▸ hv)
  have hs : DepthTie.sWT Xo c Dd ι v j = (Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v) : ℝ) := by
    unfold DepthTie.sWT DepthTie.nuT DepthTie.nuWT nuStarAt DepPage.nuN DepthTie.e2
    rw [DepthTie.resChar_below (F := c.F) v, if_neg hn1, if_neg hn2]
    ring
  set N := DepthTie.Nsig Dd.Q (DF (Dw (ι j)) (Dd.aL (ι j))) (DF (Dw (ι j)) (Dd.aF (ι j))) with hNdef
  have hN : N ≠ 0 := DepthTie.Nsig_ne_zero Dd.Q hprime _ _
  have : Fact (plc v).Prime := ⟨plc_prime v⟩
  have hdvd : (plc v) ^ ((Dd.Q.T : ℕ) * Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v)) ∣ N := by
    rw [hNdef]
    unfold DepthTie.Nsig DepPage.Z1
    refine Dvd.dvd.mul_left ?_ _
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((pow_dvd_pow _ (Nat.le_add_right _ _)).trans
      (Finset.dvd_prod_of_mem (fun p => p ^ ((Dd.Q.T : ℕ) * Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) p + Dd.Q.cP (DF (Dw (ι j)) (Dd.aF (ι j))) p))
        (Finset.mem_filter.2 ⟨h5 ▸ hv, plc_prime v⟩))) _) _
  have hle : ((Dd.Q.T : ℕ) : ℝ) * (Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v) : ℝ) ≤
      (padicValNat (plc v) N : ℝ) := by
    exact_mod_cast ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hN).1 hdvd
  have hnn0 : (0 : ℝ) ≤ (vw v (nnKAt (H := H) (LL := K) Dd (ι j)) : ℝ) := by
    exact_mod_cast DepthTie.vw_nonneg_of_isIntegral v _ (DepthTie.nnK_isIntegral Dd (ι j))
  have he := ramw_pos v
  unfold DepthTie.s1T
  rw [hs, hσ v j, DepthTie.vw_sig Dd hsp hprime v, add_div, mul_div_cancel_right₀ _ he.ne', hT]
  have : 0 ≤ (vw v (nnKAt (H := H) (LL := K) Dd (ι j)) : ℝ) / (ramw v : ℝ) := div_nonneg hnn0 he.le
  linarith

end GlobalTheory.RunDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthAtTwoOfUnscaledDepthBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.L2.DIV hiding conjPl
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem leafDepthTwo_of_unscaled_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs) (Nd : NumDatum), (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O → ContentEqualsDatumContent N Nd ι → TiePrimes O Nd → (∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∈ O.sm → ∀ j, ∃ B : ℝ, O.T * B ≤ O.sC j ∧ nuWAt (Xo := Xo (ι j)) (c := c) Dd la (ι j) ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal)) → LeafDepth2 N O := by
  intro E _ _ _ H l Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N Nd hE hσ hT hpr hsp hPg tF tP hB
  have hT0 : (0 : ℝ) ≤ O.T := by rw [hT]; positivity
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), plc v ∈ O.sm →
      (1 ≤ DepthTie.e1 c v ∧ 1 ≤ DepthTie.e2 c v ∧ ramw v = (DepthTie.e1 c v : ℤ) * (DepthTie.e2 c v : ℤ) ∧
        ∀ j, (O.E v j : ℤ) ≤ (DepthTie.e1 c v : ℤ) *
          ⌈(DepthTie.e2 c v : ℝ) * O.T * (DepthTie.nuT Xo c Dd ι v j + if plc v ∈ O.Bad then 1 else 0)⌉) →
      O.e0 v j ≤ O.sC j + O.T + 1 := by
    intro v j hv ⟨he1, he2, hram, hEv⟩
    have hbad : plc v ∈ O.Bad := by simp [OnObj.Bad, hv]
    have hEj := hEv j
    rw [if_pos hbad] at hEj
    have hR := rounding_condition_holds (DepthTie.e1 c v) (DepthTie.e2 c v) (O.T * (DepthTie.nuT Xo c Dd ι v j + 1))
      (O.E v j) he1 he2 (by rw [← mul_assoc]; exact hEj)
    have hramR : (ramw v : ℝ) = (DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ) := by simp [hram]
    have he2R : (1 : ℝ) ≤ DepthTie.e2 c v := by exact_mod_cast he2
    have hinv : 1 / (DepthTie.e2 c v : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact he2R
    have hs1 := GlobalTheory.RunDepth.sprime_nonneg_two E H l Dw Xo c Dd K Bs Df S P oc O ι hT hpr hσ hsp hPg v hv j
    obtain ⟨B, hTB, hν⟩ := hB (placeBelow (K := c.F) v) (by rw [DepthTie.resChar_below (F := c.F) v]; exact hv) j
    have hW : DepthTie.nuWT Xo c Dd ι v j ≤ B := by
      have h0 : (0 : EReal) ≤ nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j) := le_max_left _ _
      have ht := EReal.toReal_le_toReal hν (ne_bot_of_le_ne_bot EReal.zero_ne_bot h0) (EReal.coe_ne_top _)
      rw [EReal.toReal_coe] at ht
      unfold DepthTie.nuWT
      rw [div_le_iff₀ (by linarith), mul_comm]
      exact ht
    have hTW := mul_le_mul_of_nonneg_left hW hT0
    have he0 : O.e0 v j = (O.E v j : ℝ) / ((DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ)) -
        (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) := by
      unfold OnObj.e0
      rw [sub_div, hramR]
    unfold DepthTie.s1T DepthTie.sWT at hs1
    rw [he0]
    nlinarith
  intro w hw h2 j
  obtain ⟨h1, h1'⟩ := DepthTie.tieE Xo c Dd O ι hE hT hpr w hw
  exact ⟨key w j h2 h1, key (conjPl w) j (by rw [plc_conjPl]; exact h2) h1', content_zero_at_small_primes N O Nd ι hPg tF tP w h2 j⟩

end GlobalTheory.RunDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthAtTwoOfUnscaledDepthBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.L2.DIV hiding conjPl
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthAtTwo_of_unscaled_depth_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs) (Nd : NumDatum), (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O → ContentEqualsDatumContent N Nd ι → TiePrimes O Nd → (∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∈ O.sm → ∀ j, ∃ B : ℝ, O.T * B ≤ O.sC j ∧ nuWAt (Xo := Xo (ι j)) (c := c) Dd la (ι j) ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal)) → LeafDepth2 N O := by
  first | exact @GlobalTheory.RunDepth.leafDepthTwo_of_unscaled_bound | exact GlobalTheory.RunDepth.leafDepthTwo_of_unscaled_bound | (intros; apply GlobalTheory.RunDepth.leafDepthTwo_of_unscaled_bound <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.L2.DIV hiding conjPl
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem GlobalTheory.RunDepth.leafDepth2_run : (∀ (p : ℕ) [Fact p.Prime], AvFSt p) → (∀ (p : ℕ) [Fact p.Prime], HTFSt p) → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepth2 N O := by
  intro hAv hHT D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (lR Tp hK j).n := by
    intro j _
    show _ ≤ Tp.nWn
    refine le_trans ?_ Tp.nW_lo.1
    nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  have hL : LawsPi T (depOf T EX Tp hK) := lawsPi_depRun hM EX _ _ _ _ _ hn
  refine GlobalTheory.T.depthAtTwo_of_unscaled_depth_bound D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι N (numOf D L)
    hR.E_eq hR.σ_eq hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hL.piSplit hPg tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ ?_
  intro la hla j
  obtain ⟨Ap, hAp0, hAp, hle⟩ := GlobalTheory.T.sizes_bound_at_two_first_rows_weights D L Pm Tp hK T.Q hM.pins hx hb O.C hPg.1 (ι j) (hR.inR j)
  haveI : Fact (resCharOf la).Prime := ⟨Crude.resCharOf_prime la⟩
  obtain ⟨hsp, h2, hvd, hup⟩ := GlobalTheory.T.hostField_two_conjugate_places_over_two D T.Q.H hM.pins.1.1 (resCharOf la) (hR.sm_eq ▸ hla)
  refine ⟨_, ?_, GlobalTheory.T.unscaledDepth_le_placeOverTwo (resCharOf la) (hAv _) (hHT _) D.host.E T.Q.H (T.Q.Dw (ι j)) T.Q.l (T.Q.Xo (ι j)) T.Q.c
    hR.star_eq D.R.f (D.host.vdH (resCharOf la)) hvd hsp h2 la rfl _ _ _ (fun τ _ _ h => (hL.wts _ (hR.inR j)).1 τ h)
    (DepthTie.card_of_laws T _ hL hM.pins (ι j) (hR.inR j)) Ap hAp0 hAp⟩
  unfold OnObj.sC OnObj.Se
  rw [hR.T_eq, hR.m_eq, hR.vd_eq, hR.wt_eq, hR.f_eq, hR.Sc_eq, hR.eta_eq]
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (Nat.cast_nonneg _)) hle
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hAp0

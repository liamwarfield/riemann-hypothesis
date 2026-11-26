module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

namespace GlobalTheory.SplitPairLift

theorem isIrreducible_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (χ : G →* ℂˣ) : (twist ρ χ).IsIrreducible := by
  let e : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at h1⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.2 h

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detIrr (n : ℕ) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 h.detChar
  irr := isIrreducible_ofChar _

def twistIrr {n : ℕ} (π : Irr k n) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := π.V
  π := twist π.π (detChar (Fin n) χ)
  smooth := isSmooth_twist π.smooth h.detChar
  irr := isIrreducible_twist π.irr _

theorem twist_twist_inv {n : ℕ} (π : Irr k n) (χ : kˣ →* ℂˣ) :
    twist (twist π.π (detChar (Fin n) χ)) (detChar (Fin n) χ⁻¹) = π.π := by
  rw [twist_twist]
  have : detChar (Fin n) χ⁻¹ * detChar (Fin n) χ = 1 := by
    ext g; simp
  rw [this, twist_one]

end Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem e_spehLoc (T : WDTie N A) (p : Part A.CG) (w : PlE H) :
    T.e w (spehLoc N A p w) = speh (T.e w (A.locG p.π w)) p.d := by
  unfold spehLoc speh
  generalize ((p.d : ℝ) - 1) / 2 = s
  have key : ∀ L : List ℝ,
      T.e w (L.foldr (fun j acc => A.lpSum (A.lpTw (A.locG p.π w) (s - j)) acc) (A.lpZero w)) =
        L.foldr (fun j acc => ((T.e w (A.locG p.π w)).lpTw (s - j)).lpSum acc)
          (WD.lpZero (h := N.plOm.2 w)) := by
    intro L
    induction L with
    | nil => exact T.zero w
    | cons j l ih => rw [List.foldr_cons, List.foldr_cons, T.sum, T.tw, ih]
  exact key _

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SplitPairLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitChart

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

def sc (he : SplitAt D v e) (z : AE D) : Fv D.host.F v := (he.exists_scalar z).choose

theorem sc_spec (he : SplitAt D v e) (z : AE D) : e * z = fj D (singleV D.host.F v (sc he z)) * e :=
  (he.exists_scalar z).choose_spec

theorem sc_eq (he : SplitAt D v e) {z : AE D} {α : Af D.host.F} (h : e * z = fj D α * e) :
    sc he z = evalV D.host.F v α := by
  rw [sc_spec he] at h
  rw [← he.scalar_inj h, evalV_singleV_same]

def comp (he : SplitAt D v e) : AE D →+* Fv D.host.F v where
  toFun := sc he
  map_one' := by rw [sc_eq he (α := 1) (by rw [he.one_mul', mul_one]), map_one]
  map_zero' := by rw [sc_eq he (α := 0) (by rw [map_zero, mul_zero, zero_mul]), map_zero]
  map_mul' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) * singleV D.host.F v (sc he y)), map_mul,
      evalV_singleV_same, evalV_singleV_same]
    rw [map_mul]
    linear_combination y * sc_spec he x + fj D (singleV D.host.F v (sc he x)) * sc_spec he y
  map_add' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) + singleV D.host.F v (sc he y)), map_add (f := _),
      evalV_singleV_same, evalV_singleV_same]
    rw [map_add (f := _)]
    linear_combination sc_spec he x + sc_spec he y

theorem comp_apply (he : SplitAt D v e) (z : AE D) : comp he z = sc he z := rfl

theorem comp_fj (he : SplitAt D v e) (α : Af D.host.F) : comp he (fj D α) = evalV D.host.F v α :=
  sc_eq he (mul_comm _ _)

theorem comp_self (he : SplitAt D v e) : comp he e = 1 := by
  rw [comp_apply, sc_eq he (α := 1) (by rw [he.one_mul', he.1]), map_one]

theorem comp_algebraMap (he : SplitAt D v e) (y : AF D.host.F) :
    comp he (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v y.2 := by
  rw [comp_apply, sc_eq he (α := y.2 * 1), mul_one]
  rw [← algebraMap_mul_fj, mul_assoc, he.one_mul', mul_comm]

theorem isIntegral_of_int (O : Type) {K L : Type} [CommRing O] [CommRing K] [CommRing L] [Algebra O K]
    (f : L →+* K) {x : L} (hx : IsIntegral ℤ x) : IsIntegral O (f x) :=
  (map_isIntegral_int f hx).tower_top

theorem comp_mem (he : SplitAt D v e) {z : AE D} (hz : z ∈ intL D) :
    comp he z ∈ v.adicCompletionIntegers D.host.F := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    have h1 : (pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E) : AE D) =
        fj D α * (1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E) := by
      show _ = (_ ⊗ₜ _) * _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h1, map_mul, comp_fj]
    refine mul_mem (hα v) ?_
    have h3 : IsIntegral (v.adicCompletionIntegers D.host.F)
        (comp he ((1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E))) :=
      isIntegral_of_int _ ((comp he).comp
        (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toRingHom) o.2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
    rw [← hy]
    exact y.2
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add (comp he)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_mem {z : AE D} (hz : z ∈ intL D) : finPart D z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem chart_comp (he : SplitAt D v e) : Chart e v (comp he) := by
  refine ⟨fun a => ⟨fj D (singleV D.host.F v a), by rw [comp_fj, evalV_singleV_same]⟩, fun a => ⟨fun h => ?_, fun h => ?_⟩,
    comp_algebraMap he, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    rw [sc_spec he, ← comp_apply, h, h0, map_zero, zero_mul]
  · rw [← one_mul (comp he a), ← comp_self he, ← map_mul, h, map_zero]
  · have h1 := comp_mem he (inF_mem h)
    rw [inF_finPart, ← mul_assoc, he.one_mul', map_mul, comp_self, one_mul] at h1
    exact isInt_Ov.2 h1
  · rw [sc_spec he]
    exact finPart_mem (fj_mul_mem (singleV_mem_intAf D.host.F v ⟨_, isInt_Ov.1 h⟩) he.mem)

theorem exists_chart : ∀ {D : D7} (e : AE D), IsSplitIdem D e →
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), Chart e v π := by
  intro D e h
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h
  exact ⟨v, comp he, chart_comp he⟩

end GlobalTheory.SplitChart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_chart_of_splitIdempotent : ∀ {D : D7} (e : AE D), IsSplitIdem D e → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), Chart e v π := by
  first | exact @GlobalTheory.SplitChart.exists_chart | exact GlobalTheory.SplitChart.exists_chart | (intros; apply GlobalTheory.SplitChart.exists_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatIntFacts

theorem intValuation_uniformiser {R : Type} [CommRing R] [IsDedekindDomain R] (P : HeightOneSpectrum R) {ϖ : R}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) : P.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
  have a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have a0 : P.intValuation ϖ ≠ 0 := fun h => a2 (h ▸ zero_le')
  rw [← WithZero.exp_log a0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  omega

theorem exists_left_inverse {R : Type} [CommRing R] {n : ℕ} (ε : R) (B C : Matrix (Fin n) (Fin n) R)
    (hε : ε * ε = ε) (h : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R)) :
    ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have key : ∀ X Y : Matrix (Fin n) (Fin n) R,
      (ε • X + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * (ε • Y + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) =
        ε • (X * Y) + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    intro X Y
    have e1 : ε * (1 - ε) = 0 := by linear_combination -hε
    have e2 : (1 - ε) * ε = 0 := by linear_combination -hε
    have e3 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
    simp only [add_mul, mul_add, smul_mul_smul_comm, hε, e1, e2, e3, zero_smul, mul_one, add_zero, zero_add]
  have h1 := key B C
  rw [h, ← add_smul, add_sub_cancel, one_smul] at h1
  have h2 := mul_eq_one_comm.1 h1
  rw [key] at h2
  rw [eq_sub_of_add_eq h2, sub_smul, one_smul, sub_sub_cancel]


set_option maxHeartbeats 1000000 in
theorem int_facts : ∀ {D : D7} (V : HSp D), (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ n : ℤ, finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n)) ∈ intAE D) ∧ ∀ (ε : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ε * ε = ε → (∀ y ∈ LamHat V, ∃ z, (fun a => ε * y a) = fun a => ε * B.mulVec z a) → ∃ C : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), ε • (B * C) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ε • (C * B) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D V
  refine ⟨GlobalTheory.LatDual.smul_mem_lamHat V, ?_, ?_⟩
  · intro P e ϖ ϖ' he h1 h2 h1' h2' n
    have hv : P.valuation D.host.E ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n) ≤ 1 := by
      have v1 : P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ).trans (intValuation_uniformiser P h1 h2)
      have v2 : P.valuation D.host.E (ϖ' : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ').trans (intValuation_uniformiser P h1' h2')
      rw [map_div₀, map_zpow₀, map_zpow₀, v1, v2]
      exact div_self_le_one _
    obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
    have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
    have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
    have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
    have hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
      by_contra hc
      exact hb ((he.2 _ hb0).2 hc)
    have hq : (ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hb1]
      exact hab
    have ha : finPart D (incA D (a : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨1, fun v => one_mem _, a, rfl⟩
    have hm : ∀ {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
      intro x y hx hy
      refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
        refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
        · rw [map_mul]; exact mul_mem (ha w) (hb w)
        · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
      · intro x _; rw [zero_mul]; exact zero_mem _
      · intro x _; rw [mul_zero]; exact zero_mem _
      · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
      · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
      · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
      · intro x y _ _ h; rw [mul_neg]; exact neg_mem h
    have := hm ha hi
    rw [RingHom.map_mul, mul_left_comm] at this
    rw [hq, RingHom.map_mul, RingHom.map_mul]
    exact this
  · intro ε B hε h
    obtain ⟨-, -, -, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
    have hx : ∀ x : Fin V.rank → D.host.E, ∃ z, ∀ a,
        ε * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) = ε * B.mulVec z a := by
      intro x
      have hx : x ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
        rw [hspan]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz⟩ := h (fun a => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) (by
          rw [GlobalTheory.LatDual.lamHat_eq_hat]
          exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩)
        exact ⟨z, congrFun hz⟩
      | zero => exact ⟨0, fun a => by simp⟩
      | add u w _ _ hu hw =>
        obtain ⟨z, hz⟩ := hu
        obtain ⟨z', hz'⟩ := hw
        exact ⟨z + z', fun a => by
          rw [Pi.add_apply, TensorProduct.tmul_add, mul_add, hz, hz', Matrix.mulVec_add, Pi.add_apply, mul_add]⟩
      | smul c u _ hu =>
        obtain ⟨z, hz⟩ := hu
        refine ⟨((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) • z, fun a => ?_⟩
        rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ← hz,
          mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    choose z hz using hx
    have hBC : ε • (B * Matrix.of fun j i => z (Pi.single i 1) j) =
        ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
      refine Matrix.ext fun a i => ?_
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      refine (hz (Pi.single i 1) a).symm.trans ?_
      congr 1
      by_cases hai : a = i
      · subst hai
        rw [Pi.single_eq_same, Matrix.one_apply_eq]; rfl
      · rw [Pi.single_eq_of_ne hai, Matrix.one_apply_ne hai, TensorProduct.tmul_zero]
    exact ⟨_, hBC, exists_left_inverse ε B _ hε hBC⟩

end GlobalTheory.LatIntFacts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFactsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLattice_integrality : ∀ {D : D7} (V : HSp D), (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ n : ℤ, finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n)) ∈ intAE D) ∧ ∀ (ε : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ε * ε = ε → (∀ y ∈ LamHat V, ∃ z, (fun a => ε * y a) = fun a => ε * B.mulVec z a) → ∃ C : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), ε • (B * C) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ε • (C * B) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.LatIntFacts.int_facts | exact GlobalTheory.LatIntFacts.int_facts | (intros; apply GlobalTheory.LatIntFacts.int_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsIwVec {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (θ : Fin n → kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin n) k) V) (v : V) : Prop :=
  (∀ h ∈ KO k (Fin n), (∀ i j, j < i → valuation k (h.val i j) < 1) →
    (∀ i, valuation k (h.val i i - 1) < 1) → π h v = v) ∧
  ∀ t ∈ torusO k (Fin n), π (diagT k (Fin n) t) v = (GlobalTheory.SmGL.torusChar θ t : ℂ) • v

end GlobalTheory.TameIwahori
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDualLat

variable {D : D7}

theorem ringHom_sum {A B ι : Type} [Semiring A] [Semiring B] [Fintype ι] (f : A →+* B) (g : ι → A) :
    f (∑ i, g i) = ∑ i, f (g i) := map_sum f g _

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem finPart_cA (x : AE D) : finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem finPart_surjective : Function.Surjective (finPart D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul a x => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem sigR_mem_intAE {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig (o : D.host.E),
      (show IsIntegral ℤ (o : D.host.E) from o.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

def form (V : HSp D) (x z : Fin V.rank → AE D) : AE D := ∑ i, ∑ j, cA D (x i) * incA D (V.gram i j) * z j

theorem finPart_form (V : HSp D) (x z : Fin V.rank → AE D) :
    finPart D (form V x z) =
      hR (Af D.host.F) D.sp.cm.sig V.gram (fun i => finPart D (x i)) fun i => finPart D (z i) := by
  simp only [form, ringHom_sum, RingHom.map_mul, finPart_cA]
  rfl

theorem cA_form (V : HSp D) (x z : Fin V.rank → AE D) : cA D (form V x z) = form V z x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, map_sum, RingHom.map_mul, cA_cA, cA_incA, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_mul (V : HSp D) (a b : AE D) (x z : Fin V.rank → AE D) :
    form V (fun i => a * x i) (fun i => b * z i) = cA D a * b * form V x z := by
  simp only [form, RingHom.map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_iff (V : HSp D) (x : Fin V.rank → AE D) :
    (fun i => finPart D (x i)) ∈ LamHat V ↔
      ∀ z : Fin V.rank → AE D, (fun i => finPart D (z i)) ∈ LamHat V → finPart D (form V x z) ∈ intAE D := by
  rw [(GlobalTheory.LatDual.lamHat_selfDual_and_module V).1]
  constructor
  · intro h z hz
    rw [← cA_form, finPart_cA, finPart_form]
    exact sigR_mem_intAE (h _ hz)
  · intro h z hz
    obtain ⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z := by
      choose s hs using finPart_surjective (D := D)
      exact ⟨fun i => s (z i), funext fun i => hs _⟩
    rw [← finPart_form, ← cA_form, finPart_cA]
    exact sigR_mem_intAE (h _ hz)

theorem map_form (V : HSp D) {K : Type} [CommRing K] (π : AE D →+* K) (x z : Fin V.rank → AE D) :
    π (form V x z) =
      ((fun i => π (cA D (x i))) ᵥ* (V.gram.map fun a => π (incA D a))) ⬝ᵥ fun k => π (z k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, map_sum, RingHom.map_mul, dotProduct, vecMul, Finset.sum_mul, Matrix.map_apply]
  exact Finset.sum_comm

theorem conj_mem_lamHat_iff : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v) (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j) := by
  intro D e v π he hπ V β hβ y
  rw [mem_iff]
  constructor
  · intro h j
    choose s hs using hπ.1
    have h1 : (fun k => π (s (β.1 k j))) = β.1 *ᵥ Pi.single j 1 := by
      funext k
      rw [hs, Matrix.mulVec_single_one]
      rfl
    have h2 := h _ ((hβ fun k => s (β.1 k j)).2 fun i => by
      rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      by_cases hi : i = j
      · subst hi; rw [Pi.single_eq_same]; exact ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne hi]; exact ⟨0, map_zero _⟩)
    rw [form_mul, cA_cA, he.1, hπ.2.2.2, map_form, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      dotProduct_single, mul_one] at h2
    exact h2
  · intro h z hz
    have h1 := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2 _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1])) _ hz
    simp only [← RingHom.map_mul] at h1
    have h2 := (hβ z).1 h1
    have h3 := form_mul V (cA D e) 1 y z
    simp only [one_mul, mul_one, cA_cA] at h3
    have h4 : (fun k => π (z k)) = β.1 *ᵥ ((β⁻¹).1 *ᵥ fun k => π (z k)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [h3, hπ.2.2.2, map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, isInt_iff]
    exact sum_mem fun i _ => mul_mem (isInt_iff.1 (h i)) (isInt_iff.1 (h2 i))

end GlobalTheory.SplitDualLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_completedLattice_iff_dual_splitPlace : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v) (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j) := by
  first | exact @GlobalTheory.SplitDualLat.conj_mem_lamHat_iff | exact GlobalTheory.SplitDualLat.conj_mem_lamHat_iff | (intros; apply GlobalTheory.SplitDualLat.conj_mem_lamHat_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.SuppLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adele_ext {z z' : AF F ⊗[F] E} (h1 : infP F E z = infP F E z')
    (h2 : ∀ w, evF E w (finP F E z) = evF E w (finP F E z')) : z = z' := by
  have h3 : finP F E z = finP F E z' := evF_ext h2
  let b := Module.Basis.ofVectorSpace F E
  refine (Algebra.TensorProduct.basis (AF F) b).repr.injective (Finsupp.ext fun k => Prod.ext ?_ ?_)
  · have a1 := GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z k
    have a2 := GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z' k
    exact a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Ainf F) b).repr x k) h1).trans a2)
  · have a1 := GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z k
    have a2 := GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z' k
    exact a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Af F) b).repr x k) h3).trans a2)

theorem idem_mul_iff {v : HeightOneSpectrum (𝓞 F)} {e : AF F ⊗[F] E} (he : IsIdemOf E v e) (x : AF F ⊗[F] E) :
    e * x = x ↔ infP F E x = 0 ∧ ∀ w, w ≠ v → evF E w (finP F E x) = 0 := by
  obtain ⟨e1, e2, e3⟩ := he
  constructor
  · intro h
    refine ⟨?_, fun w hw => ?_⟩
    · rw [← h, map_mul, e1, zero_mul]
    · rw [← h, map_mul, map_mul, e3 w hw, zero_mul]
  · rintro ⟨h1, h2⟩
    refine adele_ext ?_ fun w => ?_
    · rw [map_mul, h1, mul_zero]
    · rw [map_mul, map_mul]
      by_cases hw : w = v
      · subst hw
        rw [e2, one_mul]
      · rw [h2 w hw, mul_zero]

theorem bc_eq_one_iff {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B) (g : GL (Fin n) A) :
    Formalism.UG.bc φ g = 1 ↔ ∀ i j, φ ((g.1 - 1) i j) = 0 := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  show φ (g.1 i j) = (1 : Matrix (Fin n) (Fin n) B) i j ↔ _
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable [NumberField E] [StarRing E] (hc : CMData F E) (V : HSpace E)

theorem supp_iff {v : HeightOneSpectrum (𝓞 F)} {e : AF F ⊗[F] E} (he : IsIdemOf E v e)
    (g : HA (AF F) hc.sig V.gram) :
    Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1 := by
  have h1 : IsFin hc V g ↔ ∀ i j, infP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j) = 0 :=
    bc_eq_one_iff _ _
  have h2 : ∀ w, locMat hc V w g = 1 ↔
      ∀ i j, evF E w (finP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j)) = 0 :=
    fun w => bc_eq_one_iff ((evF E w).comp (finP F E)) (HA.mat (AF F) hc.sig V.gram g)
  rw [h1]
  simp only [h2, Supp, idem_mul_iff he]
  exact ⟨fun h => ⟨fun i j => (h i j).1, fun w hw i j => (h i j).2 w hw⟩,
    fun h i j => ⟨h.1 i j, fun w hw => h.2 w hw i j⟩⟩

theorem supp_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E), IsIdemOf E v e → (∀ g, Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1) ∧ (∀ g g', Supp hc V e g → Supp hc V e g' → locMat hc V v g = locMat hc V v g' → g = g') ∧ ∀ u ∈ HR (Fv F v) hc.sig V.gram, ∃ g, Supp hc V e g ∧ locMat hc V v g = u := by
  classical
  intro F E _ _ _ _ _ _ hc V v e he
  refine ⟨supp_iff hc V he, fun g g' hg hg' h => ?_, fun u hu => ?_⟩
  · obtain ⟨a1, a2⟩ := (supp_iff hc V he g).1 hg
    obtain ⟨b1, b2⟩ := (supp_iff hc V he g').1 hg'
    have hw : ∀ w, locMat hc V w g = locMat hc V w g' := fun w => by
      by_cases hw : w = v
      · exact hw ▸ h
      · rw [a2 w hw, b2 w hw]
    have hi := Eq.trans a1 (Eq.symm b1)
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => adele_ext ?_ fun w => ?_))
    · exact congrArg (fun x => x.1 i j) hi
    · exact congrArg (fun x => x.1 i j) (hw w)
  · let u' : HA (Fv F v) hc.sig V.gram := ⟨u, hu⟩
    obtain ⟨k, hk⟩ := GlobalTheory.LocalUnitaryGlue.exists_of_finite hc.sig V.gram
      (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u')
      ((Set.finite_singleton v).subset fun w hw => by
        by_contra hne
        exact hw (Pi.mulSingle_eq_of_ne
          (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) (i := v) (i' := w) hne u'))
    have hl : ∀ w, locMat hc V w (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k) = HA.mat _ _ _
        (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u' w) := fun w => by
      rw [← hk w]
      exact congrArg (fun x => HA.mat _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V w x))
        (GlobalTheory.AutFunCompare.projFin_ofFin hc V k)
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k, (supp_iff hc V he _).2 ⟨?_, fun w hw => ?_⟩, ?_⟩
    · exact congrArg (HA.mat _ _ _) (GlobalTheory.AutFunCompare.projInf_ofFin hc V k)
    · rw [hl, Pi.mulSingle_eq_of_ne hw]; rfl
    · rw [hl, Pi.mulSingle_eq_same]; rfl

end GlobalTheory.SuppLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitarStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E), IsIdemOf E v e → (∀ g, Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1) ∧ (∀ g g', Supp hc V e g → Supp hc V e g' → locMat hc V v g = locMat hc V v g' → g = g') ∧ ∀ u ∈ HR (Fv F v) hc.sig V.gram, ∃ g, Supp hc V e g ∧ locMat hc V v g = u := by
  first | exact @GlobalTheory.SuppLocal.supp_local | exact GlobalTheory.SuppLocal.supp_local | (intros; apply GlobalTheory.SuppLocal.supp_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrame

open GlobalTheory.IdemModTwo (fj inF inF_finPart inF_tmul)
open GlobalTheory.SplitHeckeLabel (exists_local_lattice smul_mem_latHat mul_mem_intA intA)

theorem exists_gl_of_lattice (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {K : Type} [Field K]
    [Algebra O K] [IsFractionRing O K] {n : ℕ} (Λ : Submodule O (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ β : GL (Fin n) K, ∀ w, w ∈ Λ ↔ ∀ i, IsInt O (((β⁻¹).1 *ᵥ w) i) := by
  classical
  have : Submodule.IsFullLattice K Λ := { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := hsp }
  have := Submodule.IsLattice.finite K Λ
  have := Submodule.IsLattice.free K Λ
  have hr : Module.finrank O Λ = n := by
    rw [((Submodule.IsFullLattice.finrank_eq K Λ).trans (Module.finrank_fintype_fun_eq_card K)), Fintype.card_fin]
  let b : Module.Basis (Fin n) O Λ := Module.finBasisOfFinrankEq O Λ hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsFullLattice K
  let s := Pi.basisFun K (Fin n)
  refine ⟨⟨s.toMatrix c, c.toMatrix s, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, fun w => ?_⟩
  have hw : c.toMatrix s *ᵥ w = c.repr w := by
    exact Module.Basis.toMatrix_mulVec_repr s c w
  change _ ↔ ∀ i, IsInt O ((c.toMatrix s *ᵥ w) i)
  rw [hw]
  have hc : ∀ i, c i = (b i : Fin n → K) := fun i => Module.Basis.extendOfIsFullLattice_apply K b i
  constructor
  · intro h i
    refine ⟨b.repr ⟨w, h⟩ i, ?_⟩
    have h1 : w = ∑ j, algebraMap O K (b.repr ⟨w, h⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨w, h⟩)
      rw [Submodule.coe_sum] at this
      refine this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [hc, algebraMap_smul]
      rfl
    conv_rhs => rw [h1]
    rw [c.repr_sum_self]
  · intro h
    choose o ho using h
    rw [← c.sum_repr w]
    refine Λ.sum_mem fun j _ => ?_
    rw [← ho, algebraMap_smul, hc]
    exact Λ.smul_mem _ (b j).2

variable {D : D7}

theorem finPart_inF (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (inF D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [AddMonoidHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [AddMonoidHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem exists_factor {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) : ∃ φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v, ∀ z, φ (finPart D z) = π z := by
  have h1 : π (fj D 1) = 1 := (h.2.2.1 _).trans (map_one (evalV D.host.F v))
  refine ⟨(finPart D).liftOfRightInverse (inF D) finPart_inF ⟨π, fun z hz => ?_⟩, fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z⟩
  rw [RingHom.mem_ker] at hz ⊢
  have h2 := inF_finPart z
  rw [hz, AddMonoidHom.map_zero] at h2
  have h3 := congrArg π h2
  rwa [RingHom.map_zero, RingHom.map_mul, h1, one_mul, eq_comm] at h3

theorem finPart_mul_eq {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) {φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v} (hφ : ∀ z, φ (finPart D z) = π z)
    (y : AE D) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hy : π y = φ z) : finPart D (e * y) = finPart D e * z := by
  have h1 : π y = π (inF D z) := by
    rw [← hφ (inF D z), finPart_inF]
    exact hy
  have h2 := (h.2.1 (y - inF D z)).1 (by rw [RingHom.map_sub, h1, sub_self])
  rw [mul_sub, sub_eq_zero] at h2
  rw [h2, RingHom.map_mul, finPart_inF]

theorem exists_frame : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  intro D e v π he h V
  obtain ⟨φ, hφ⟩ := exists_factor h
  have hei : finPart D e ∈ intA D.host.F D.host.E :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  have hπe : π e = 1 := by
    have := (h.2.1 (e - 1)).2 (by rw [mul_sub, he.1, mul_one, sub_self])
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := Set.ext fun y => by
    change _ ↔ ∑ i, y i • V.frame i ∈ V.L0
    rw [← V.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
      rwa [LinearEquiv.symm_apply_apply]
    · exact fun h => ⟨_, h, V.frame.equivFun.apply_symm_apply y⟩
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    classical
    have hs : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      obtain ⟨s, hs⟩ := V.standardTuple_isLattice.fg
      apply eq_top_iff.mpr
      intro y _
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s (fun x => V.hT x y)
      have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 :=
        (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
      let P : Submodule (𝓞 D.host.E) V.V := {
        carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * V.hT x y}
        zero_mem' := by refine ⟨0, ?_⟩; simp
        add_mem' := by
          rintro x z ⟨b, hb⟩ ⟨c, hc⟩
          refine ⟨b + c, ?_⟩
          change (b : D.host.E) + c = _
          rw [hb, hc, map_add, LinearMap.add_apply, mul_add]
        smul_mem' := by
          rintro c x ⟨b, hb⟩
          refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
          simp only [map_mul, RingOfIntegers.mapRingHom_apply, hb]
          rw [show c • x = (c : D.host.E) • x from (IsScalarTower.algebraMap_smul D.host.E c x).symm, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
          change star (c : D.host.E) * ((algebraMap (𝓞 D.host.E) D.host.E a) * V.hT x y) = _
          simp only [starRingEnd_apply]
          ring }
      have hsP : (s : Set V.V) ⊆ P := by
        intro x hx
        obtain ⟨b, hb⟩ := ha x hx
        exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
      have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        change (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Formalism.E.hdual V.hT V.L0
        simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
        intro x hx
        obtain ⟨b, hb⟩ := (hs ▸ Submodule.span_le.mpr hsP) hx
        change V.hT x ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
        rw [map_smul, smul_eq_mul, ← hb]
        exact Submodule.algebraMap_mem _
      have hy' := (Submodule.span D.host.E (V.L0 : Set V.V)).smul_mem (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ (Submodule.subset_span hy)
      rwa [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at hy'
    change Submodule.span _ (V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)) = ⊤
    rw [← Submodule.map_span, hs, Submodule.map_top, LinearEquiv.range]
  obtain ⟨Λ, hfg, hΛ, hmem⟩ := exists_local_lattice (F := D.host.F) L (V.standardTuple_isLattice.fg.map _) hsp v φ
    (fun a => (hφ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a))).trans (h.2.2.1 _))
    (fun x hx => by
      rw [← finPart_inF x, hφ, ← isInt_Ov, ← h.2.2.2, RingHom.map_mul, finPart_inF]
      exact mul_mem_intA hei hx)
  obtain ⟨β, hβ⟩ := exists_gl_of_lattice (Ov D v) Λ hfg hΛ
  refine ⟨β, fun y => ?_⟩
  rw [← hβ, hmem, LamHat, ← hL]
  constructor
  · intro hy
    refine ⟨_, hy, funext fun i => ?_⟩
    rw [Function.comp_apply, hφ, RingHom.map_mul, hπe, one_mul]
  · rintro ⟨z, hz, hy⟩
    have : (fun i => finPart D (e * y i)) = finPart D e • z := funext fun i =>
      finPart_mul_eq h hφ (y i) (z i) (congrFun hy i)
    rw [this]
    exact smul_mem_latHat L hei hz

end GlobalTheory.SplitFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitFrame_selfDualLattice_completion : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  first | exact @GlobalTheory.SplitFrame.exists_frame | exact GlobalTheory.SplitFrame.exists_frame | (intros; apply GlobalTheory.SplitFrame.exists_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharFiniteOrderUnitIdele
noncomputable section

namespace GlobalTheory.HeckeFin

open Neutral.B1 hiding Ideles
open Formalism.L2.Host hiding HChar
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

theorem circle_pow (ψ : Ideles L →* Circle) (hψ : Continuous ψ) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Ideles L, IsFinIdele u → u ∈ unitIdl L → ψ u ^ m = 1 := by
  obtain ⟨-, -, -, m, hm, h⟩ := GlobalTheory.CharFin.finite_order_of_small (R := AdeleRing (𝓞 L) L)
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (RingHom.snd _ _) id continuous_id (fun _ => rfl)
    (GlobalTheory.UnUnitCmp.Val.intFin L) (fun W hW => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele L W hW)
    GlobalTheory.UnUnitCmp.Val.finite_quot ψ hψ
  exact ⟨m, hm, fun u h1 h2 => h u ⟨funext h1, fun v => (h2 v).le, fun v => ((unitIdl L).inv_mem h2 v).le⟩⟩

theorem norm_ne (χ : HChar L) (x : Ideles L) : ‖((χ.1 x : ℂˣ) : ℂ)‖ ≠ 0 :=
  norm_ne_zero_iff.2 (Units.ne_zero _)

theorem continuous_norm_val (χ : HChar L) : Continuous fun x : Ideles L => ‖((χ.1 x : ℂˣ) : ℂ)‖ :=
  (Units.continuous_val.comp χ.2.1).norm

def twist (χ : HChar L) (c : ℝ) : Ideles L →* Circle where
  toFun x := Circle.exp (c * Real.log ‖((χ.1 x : ℂˣ) : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [χ.1.map_mul, Units.val_mul, norm_mul, Real.log_mul (norm_ne χ x) (norm_ne χ y), mul_add, Circle.exp_add]

theorem continuous_twist (χ : HChar L) (c : ℝ) : Continuous (twist χ c) :=
  Circle.exp.continuous.comp (continuous_const.mul ((continuous_norm_val χ).log (norm_ne χ)))

theorem norm_eq_one (χ : HChar L) (a : Ideles L) (h1 : IsFinIdele a) (h2 : a ∈ unitIdl L) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  by_contra hne
  have ht : Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖ ≠ 0 := by
    intro h0
    rcases Real.log_eq_zero.1 h0 with h | h | h
    · exact norm_ne χ a h
    · exact hne h
    · linarith [norm_nonneg ((χ.1 a : ℂˣ) : ℂ)]
  set t := Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖ with htdef
  obtain ⟨m, hm, h⟩ := circle_pow (twist χ (2 * Real.pi * √2 / t)) (continuous_twist χ _)
  have e := h a h1 h2
  have e1 : twist χ (2 * Real.pi * √2 / t) a = Circle.exp (2 * Real.pi * √2) := by
    change Circle.exp (2 * Real.pi * √2 / t * Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖) = _
    rw [← htdef, div_mul_cancel₀ _ ht]
  rw [e1, ← Circle.exp_nsmul] at e
  have e2 := congrArg (fun z : Circle => (z : ℂ)) e
  simp only [Circle.coe_exp, Circle.coe_one] at e2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 e2
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e3 : (m : ℂ) * (√2 : ℝ) = n := by
    have : ((m : ℂ) * (√2 : ℝ)) * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I) := by
      rw [← hn]; push_cast; simp only [nsmul_eq_mul]; push_cast; ring
    exact mul_right_cancel₀ (by simp [hpi, Complex.I_ne_zero]) this
  have e4 : (m : ℝ) * √2 = n := by exact_mod_cast e3
  exact (irrational_sqrt_two.natCast_mul hm.ne').ne_int n e4

def unitPart (χ : HChar L) : Ideles L →* Circle where
  toFun x := ⟨((χ.1 x : ℂˣ) : ℂ) / ‖((χ.1 x : ℂˣ) : ℂ)‖, by
    simp [Submonoid.unitSphere, norm_ne χ x]⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    change ((χ.1 (x * y) : ℂˣ) : ℂ) / ‖((χ.1 (x * y) : ℂˣ) : ℂ)‖ =
      (((χ.1 x : ℂˣ) : ℂ) / ‖((χ.1 x : ℂˣ) : ℂ)‖) * (((χ.1 y : ℂˣ) : ℂ) / ‖((χ.1 y : ℂˣ) : ℂ)‖)
    rw [χ.1.map_mul, Units.val_mul, norm_mul]
    push_cast
    rw [mul_div_mul_comm]

theorem continuous_unitPart (χ : HChar L) : Continuous (unitPart χ) := by
  refine Continuous.subtype_mk ?_ _
  exact (Units.continuous_val.comp χ.2.1).div (Complex.continuous_ofReal.comp (continuous_norm_val χ))
    (fun x => by simpa using norm_ne χ x)

theorem finite_order : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (a : Ideles L), IsFinIdele a →
    (∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → ∃ n : ℕ, 0 < n ∧ χ.1 a ^ n = 1 := by
  intro L _ _ χ a h1 h2
  have h2' : a ∈ unitIdl L := h2
  obtain ⟨m, hm, h⟩ := circle_pow (unitPart χ) (continuous_unitPart χ)
  refine ⟨m, hm, Units.ext ?_⟩
  have e := congrArg (fun z : Circle => (z : ℂ)) (h a h1 h2')
  have e1 : ((unitPart χ a : Circle) : ℂ) = ((χ.1 a : ℂˣ) : ℂ) := by
    change ((χ.1 a : ℂˣ) : ℂ) / ‖((χ.1 a : ℂˣ) : ℂ)‖ = _
    rw [norm_eq_one χ a h1 h2']; simp
  simpa [e1] using e

end GlobalTheory.HeckeFin
end
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetProdMapProductEqProdProd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLettersHarmMemHHa
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctio

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRelation

theorem relation_conj {K C X : Type} [Field K] [AddCommGroup C] [Module K C] (σ : K →+* ℂ) (Φ : C →ₛₗ[σ] (X → ℂ))
    (hΦ : ∀ (m : ℕ) (b : Fin m → C), LinearIndependent K b → LinearIndependent ℂ fun k => Φ (b k))
    (τ : ℂ ≃+* ℂ) (hτ : ∀ x, τ (σ x) = σ x) {n : ℕ} (a : Fin n → ℂ) (f : Fin n → C)
    (h : ∀ g, (0 : ℂ) = ∑ k, a k * Φ (f k) g) (g : X) : (0 : ℂ) = ∑ k, τ (a k) * Φ (f k) g := by
  let S := Submodule.span K (Set.range f)
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range f)
  let b := Module.finBasis K S
  have hb := hΦ _ (fun l => (b l : C)) (b.linearIndependent.map' S.subtype (Submodule.ker_subtype _))
  let c : Fin n → Fin (Module.finrank K S) → K := fun k l => b.repr ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩ l
  have hf : ∀ k, f k = ∑ l, c k l • (b l : C) := fun k => by
    have h1 := congrArg S.subtype (b.sum_repr ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    exact h1.symm
  have key : ∀ (a' : Fin n → ℂ) (x : X), ∑ k, a' k * Φ (f k) x = ∑ l, (∑ k, a' k * σ (c k l)) * Φ (b l) x := by
    intro a' x
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf k, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smulₛₗ, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have h0 : ∀ l, ∑ k, a k * σ (c k l) = 0 := by
    refine Fintype.linearIndependent_iff.1 hb _ ?_
    funext x
    rw [Finset.sum_apply]
    exact ((h x).trans (key a x)).symm
  rw [key]
  refine (Finset.sum_eq_zero fun l _ => ?_).symm
  have h1 := congrArg τ (h0 l)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hτ, map_zero] at h1
  rw [h1, zero_mul]

theorem exists_semilinear {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    ∃ Φ : T.R j →ₛₗ[σ] (GA D W → ℂ), (∀ f, Φ f = phiC T hV a f) ∧ ∀ f g, Φ f g =
      ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * adel W (castDict hV (T.dict j σ))
        (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ)) (rdU (T.U j σ) f) g := by
  subst hV
  exact ⟨(((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) • adel (T.V j σ) (T.dict j σ)
    (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ))).comp (rdU (T.U j σ)), fun _ => rfl, fun _ _ => rfl⟩


set_option maxHeartbeats 1000000 in
theorem expands_zero_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ τ : ℂ ≃+* ℂ, (∀ a : T.Q.c.F, τ (a : ℂ) = (a : ℂ)) → ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n), Expands M (κ i) (fun _ => 0) a f → Expands M (κ i) (fun _ => 0) (fun k => τ (a k)) f := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hfw i Tp tup M _ τ hτ n a f h
  obtain ⟨fw⟩ := hfw
  have hσ : GoodEmb T.Q.c M.s0 := T.toCore.good_σ₀
  have hex := exists_semilinear T M.hV (wtA (κ i))
  obtain ⟨Φ, h1, h2⟩ := hex
  have hI := GlobalTheory.PhiIndep.phiC_indep D T κ fw.laws i M.s0 hσ M.hV
  intro g
  have hr := relation_conj M.s0 (Φ.comp (T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype)
    (fun m b hb => (funext fun k => h1 (b k : T.R ((i : ℕ) + 1))).symm ▸ hI m b hb) τ hτ a f
    (fun x => (h x).trans (Finset.sum_congr rfl fun k _ => congrArg (a k * ·) (h2 _ x).symm)) g
  exact hr.trans (Finset.sum_congr rfl fun k _ => congrArg (τ (a k) * ·) (h2 _ g))

end GlobalTheory.ConjRelation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_linear_relation_defined_over_core_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ τ : ℂ ≃+* ℂ, (∀ a : T.Q.c.F, τ (a : ℂ) = (a : ℂ)) → ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n), Expands M (κ i) (fun _ => 0) a f → Expands M (κ i) (fun _ => 0) (fun k => τ (a k)) f := by
  first | exact @GlobalTheory.ConjRelation.expands_zero_conj | exact GlobalTheory.ConjRelation.expands_zero_conj | (intros; apply GlobalTheory.ConjRelation.expands_zero_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTwistFactorEqUnitMulFlatFourier
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTwistFactorEqUnitMulFlatFourier
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatFourierQ

theorem unitOff_mul' {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_prod' {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_of_dvd {N q m : ℕ} {C : ℂ} (hq : q ∣ N) (h0 : C ≠ 0) (hC : IsIntegral ℤ C)
    (hCq : IsIntegral ℤ ((q : ℂ) ^ m * C⁻¹)) : UnitOff N C := by
  obtain ⟨d, rfl⟩ := hq
  have hint : ∀ a : ℕ, IsIntegral ℤ (a : ℂ) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (a : ℤ))
  refine ⟨h0, m, ((hint _).pow m).mul hC, ?_⟩
  have e : ((q * d : ℕ) : ℂ) ^ m * C⁻¹ = (d : ℂ) ^ m * ((q : ℂ) ^ m * C⁻¹) := by push_cast; ring
  rw [e]; exact ((hint d).pow m).mul hCq

theorem dite_prod' {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_eq_unit_mul_flat_transform : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n N : ℕ), 0 < N → (∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1 ∧ Nat.card (kP PP) ∣ N) → ∃ Gc : ℂ, UnitOff N Gc ∧ ∀ ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) ub = Gc * ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)), omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) * ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  intro D _ Q ξ ψP r n N _ hQ
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  have hloc : ∀ PP : ↥Q, ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧
      IsIntegral ℤ ((Nat.card (kP PP.1) : ℂ) ^ m * C⁻¹) ∧
      ∀ u : Matrix (Fin n) (Fin r) (kP PP.1),
        (∑ y : Matrix (Fin r) (Fin n) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C * fq PP.1 u := by
    intro PP
    letI := Ideal.Quotient.field PP.1.asIdeal
    obtain ⟨C, m, h0, h1, h2, h3⟩ :=
      GlobalTheory.T.fourier_flat_character_datum_finiteField (kP PP.1) (ψP PP.1) (ξ PP.1) r n (hQ _ PP.2).1 (hQ _ PP.2).2.1
    exact ⟨C, m, h0, h1, by rw [Nat.card_eq_fintype_card]; exact h2, h3⟩
  choose C m hC0 hCi hCm hCe using hloc
  refine ⟨(∏ PP : ↥Q, C PP)⁻¹, ?_, fun ub => ?_⟩
  · have hu : UnitOff N (∏ PP : ↥Q, C PP) :=
      unitOff_prod' _ _ fun PP _ => unitOff_of_dvd (hQ _ PP.2).2.2 (hC0 PP) (hCi PP) (hCm PP)
    obtain ⟨h0, e, h1, h2⟩ := hu
    exact ⟨inv_ne_zero h0, e, h2, by rw [inv_inv]; exact h1⟩
  · have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
      rw [← Finset.attach_eq_univ]
      unfold omegaQ
      convert dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
      intro y
      have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP),
          omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
        intro Y
        unfold omegaFlat
        convert dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
      rw [e0, Finset.attach_eq_univ]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [dif_pos PP.2, Subtype.coe_eta]
    simp only [hf, ← Finset.prod_mul_distrib]
    have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin n) (kP PP.1))))
      (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin n) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
    rw [Fintype.piFinset_univ] at hs
    rw [← hs]
    simp only [hCe]
    rw [Finset.prod_mul_distrib, hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatFourierQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTwistFactorEqUnitMulFlatFourierStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueTwistFactor_eq_unit_mul_flat_fourier : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n N : ℕ), 0 < N → (∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1 ∧ Nat.card (kP PP) ∣ N) → ∃ Gc : ℂ, UnitOff N Gc ∧ ∀ ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) ub = Gc * ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)), omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) * ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  first | exact @GlobalTheory.FlatFourierQ.omegaQ_eq_unit_mul_flat_transform | exact GlobalTheory.FlatFourierQ.omegaQ_eq_unit_mul_flat_transform | (intros; apply GlobalTheory.FlatFourierQ.omegaQ_eq_unit_mul_flat_transform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfNotAntitoneInt
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WhitTorus

theorem eq_zero_of_not_antitone_int (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (ψ : AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w)
    (W : GL (Fin n) (w.adicCompletion E) → ℂ)
    (hWN : ∀ u ∈ unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g)
    (hWK : ∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (l : Fin n → ℤ) (hl : ¬ Antitone l)
    (D : GL (Fin n) (w.adicCompletion E))
    (hDv : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ ^ l a : (w.adicCompletion E)ˣ) : w.adicCompletion E)) :
    W D = 0 := by
  obtain ⟨i, j, hij, hlt⟩ : ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i < l j := by
    by_contra h
    push_neg at h
    apply hl
    cases n with
    | zero => exact fun a => a.elim0
    | succ m =>
      rw [Fin.antitone_iff_succ_le]
      intro k
      exact h k.castSucc k.succ (by simp)
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt' : i < j := Fin.lt_def.2 (by omega)
  have hnot : ((ϖ : w.adicCompletion E))⁻¹ ∉ Ov E w := by
    intro h
    change Valued.v (((ϖ : w.adicCompletion E))⁻¹) ≤ 1 at h
    rw [map_inv₀, hϖ, ← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe] at h
    exact absurd (Multiplicative.ofAdd_le.1 (h.trans_eq (ofAdd_zero).symm)) (by norm_num)
  obtain ⟨y, hy, hψy⟩ : ∃ y ∈ Ov E w, ψ (((ϖ : w.adicCompletion E))⁻¹ * y) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hψ _).1 h)
  set x : w.adicCompletion E := ((ϖ : w.adicCompletion E))⁻¹ * y with hx
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  set m : ℕ := (l j - l i).toNat with hm
  have hlj : l j = l i + (m : ℤ) := by omega
  have hm1 : 1 ≤ m := by omega
  have hdj : ((ϖ ^ l j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      ((ϖ ^ l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * (ϖ : w.adicCompletion E) ^ m := by
    rw [hlj, _root_.zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  set c : w.adicCompletion E := (ϖ : w.adicCompletion E) ^ m * x with hc
  have hcO : c ∈ Ov E w := by
    have hϖO : (ϖ : w.adicCompletion E) ∈ Ov E w := mem_Ov_of_isUnifV hϖ
    have : c = (ϖ : w.adicCompletion E) ^ (m - 1) * y := by
      rw [hc, hx, ← mul_assoc, show m = (m - 1) + 1 by omega, pow_succ, mul_assoc _ (ϖ : w.adicCompletion E),
        mul_inv_cancel₀ hϖ0, mul_one, Nat.add_sub_cancel]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hϖO _) hy
  let T : w.adicCompletion E → GL (Fin n) (w.adicCompletion E) := fun a =>
    ⟨Matrix.transvection i j a, Matrix.transvection i j (-a),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩
  have hT : ∀ a, ((T a : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.transvection i j a := fun a => rfl
  have hentry : ∀ {R : Type} [CommRing R] (a : R) (p q : Fin n), Matrix.transvection i j a p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) := by
    intro R _ a p q
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
  have hu : T x ∈ unipB (w.adicCompletion E) (Fin n) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hT, hentry, if_neg (fun h => by rw [h] at hqp; exact lt_irrefl _ hqp), if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hqp hlt'
    · rw [hT, hentry, if_pos rfl, if_neg, add_zero]
      rintro ⟨rfl, h⟩
      exact hne h.symm
  have hsd : superDiag (T x) = x := by
    unfold GlobalTheory.Whittaker.superDiag
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [hT, hentry, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
      · intro b hb hbj
        have hb' := (Finset.mem_filter.1 hb).2
        rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hbj h.2.symm), add_zero]
      · intro hj
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, hij⟩) hj
    · intro a _ hai
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' := (Finset.mem_filter.1 hb).2
      rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hai h.1.symm), add_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hk : T c ∈ KGL w (n := n) := by
    refine ⟨⟨Matrix.transvection i j ⟨c, hcO⟩, Matrix.transvection i j (-⟨c, hcO⟩),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩, ?_⟩
    apply Units.ext
    ext p q
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hT]
    rw [hentry, hentry]
    split_ifs <;> simp
  have hkey : D * T c = T x * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDv, hT, hT]
    ext p q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hentry, hentry]
    by_cases hpq : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [if_neg hne, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, zero_add, zero_add, hc, hdj]
      ring_nf
    · simp only [if_neg hpq, add_zero]
      split_ifs with h
      · subst h
        simp
      · simp
  have h1 := hWK D (T c) hk
  rw [hkey, hWN (T x) hu D, hsd] at h1
  have h2 : (ψ x - 1) * W D = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hψy)

end GlobalTheory.WhitTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportedAdelicPointEqOneWhereIdempotentVanishes
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportedAdelicPointEqOneWhereIdempotentVanishes
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

theorem GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (V : HSp D) (e : AE D) (g : GA D V), SuppAt e V g → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (e + cA D e)) Q = 0 → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V g).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  intro D ι V e g hS Q hQ i j
  have hent : ∀ i j, ((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
      = finPart D (Formalism.L2.Theta.mt V g i j) := fun i j => rfl
  have h1 := congrArg (fun x => ι (finPart D x) Q) (hS i j)
  simp only [map_mul] at h1
  have hm : (ι (finPart D (e + cA D e)) * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j))) Q
      = ι (finPart D (e + cA D e)) Q * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j)) Q := rfl
  rw [hm, hQ, zero_mul] at h1
  have h2 : ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q
      = ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := by
    have hs : (Formalism.L2.Theta.mt V g - 1) i j = Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := rfl
    rw [hs, map_sub, map_sub] at h1
    have hsub : (ι (finPart D (Formalism.L2.Theta.mt V g i j)) - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j))) Q
        = ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := rfl
    rw [hsub] at h1
    exact (sub_eq_zero.mp h1.symm)
  show ι (((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j) Q = _
  rw [hent, h2]
  by_cases hij : i = j
  · subst hij; simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne hij]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportedAdelicPointEqOneWhereIdempotentVanishesStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (V : HSp D) (e : AE D) (g : GA D V), SuppAt e V g → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (e + cA D e)) Q = 0 → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V g).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  first | exact @GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero | exact GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero | (intros; apply GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentAddConjSupportFinitePrimeToP
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentAddConjSupportFinitePrimeToP
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

namespace GlobalTheory

theorem idemSum_add_conj_support_finite : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q)) → ∀ (p : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite ∧ (∀ Q ∈ S, (p : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ∀ Q ∉ S, ι (finPart D (e + cA D e)) Q = 0 := by
  intro D ι hid hcj p e P he hp
  classical
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
      ∀ Q z, ev Q z = ι (finPart D z) Q :=
    ⟨fun Q => ((GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  simp only [← hev] at hid hcj ⊢
  obtain ⟨⟨es, hes, hsum⟩, horth⟩ := he
  have e2 : ∀ Q, Q ∉ P → ev Q e = 0 := fun Q hQ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 Q fun hh => hQ (hh ▸ h')
  refine ⟨↑P ∪ GlobalTheory.IdemSupport.cP '' ↑P, P.finite_toSet.union (P.finite_toSet.image _), ?_, ?_⟩
  · rintro Q (hQ | ⟨Q', hQ', rfl⟩)
    · exact hp Q hQ
    · rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact hp Q' hQ'
  · intro Q hQ
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_image, not_or, not_exists, not_and] at hQ
    have h1 : Q ∉ P := hQ.1
    have h2 : GlobalTheory.IdemSupport.cP Q ∉ P := fun h => hQ.2 _ h (GlobalTheory.ClassScalarValue.cP_cP Q)
    have a := hcj e (GlobalTheory.IdemSupport.cP Q)
    rw [e2 _ h2, map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at a
    rw [map_add (f := _), e2 Q h1, a, add_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentAddConjSupportFinitePrimeToPStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q)) → ∀ (p : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite ∧ (∀ Q ∈ S, (p : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ∀ Q ∉ S, ι (finPart D (e + cA D e)) Q = 0 := by
  first | exact @GlobalTheory.idemSum_add_conj_support_finite | exact GlobalTheory.idemSum_add_conj_support_finite | (intros; apply GlobalTheory.idemSum_add_conj_support_finite <;> assumption)
end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StdAtPrime

theorem bnd_inv_of_hLat_std (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (V : HSp D) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (p : ℕ) (k : Bridge.Gf V)
    (hk : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank) :
    Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom k.1)⁻¹.1 := by
  refine ⟨1, Nat.coprime_one_left p, fun i j Q => ?_⟩
  have hx : (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V k := by
    rw [hk]
    refine Submodule.mem_pi.2 fun i' _ => ?_
    by_cases h : i' = j
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have := (GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL k _).1 hx i Q
  have e : (fun j' => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
      ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) j')) = Pi.single j 1 := by
    funext j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [e, Matrix.mulVec_single_one] at this
  rw [Nat.cast_one, one_mul]
  exact this


end GlobalTheory.StdAtPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryDetCharacterEqProdResidueGoodBaseFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterProductFormula
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwistDetStab

open Classical

variable {D : D7}

theorem infPart_idemAt (P : Pl D.host.E) (e : AE D) (h : Formalism.L2.NTheta.IsIdemAt e P) : infPart D e = 0 := by
  obtain ⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩ := h
  have k1 := congrArg (infPart D) h1
  have k2 := congrArg (infPart D) h2
  have k3 := congrArg (infPart D) h3
  simp only [RingHom.map_mul, RingHom.map_add (f := _), RingHom.map_zero] at k1 k2 k3
  have k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    simp [infPart, Algebra.TensorProduct.algebraMap_apply]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [k4] at k3
  linear_combination -k1 + infPart D e * k3 - k2

theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

theorem idem_mul_self {Q : Finset (Pl D.host.E)} (h : SplitSet Q) : idem Q * idem Q = idem Q := by
  show (∑ P ∈ Q, idemAt P) * idem Q = idem Q
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun P hP => idemAt_mul_idem h hP

theorem idem_mul_idem_of_disjoint {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q)
    (hd : Disjoint s s') : idem s * idem s' = 0 := by
  rw [idem, idem, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
    h.mul_eq_zero (hs hi) (hs' hj) fun e => Finset.disjoint_left.1 hd hi (e ▸ hj)

theorem idem_mul_conj {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q) :
    idem s * cA D (idem s') = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, idem, map_sum, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h.mul_conj (hs hi) (hs' hj)

theorem val_mul (d e₁ e₂ : AE D) (h : e₁ * e₂ = 0) :
    (e₁ * d + (1 - e₁)) * (e₂ * d + (1 - e₂)) = (e₁ + e₂) * d + (1 - (e₁ + e₂)) := by
  linear_combination (d * d - 2 * d + 1) * h

theorem prod_val (d : AE D) {Q : Finset (Pl D.host.E)} (h : SplitSet Q) :
    ∀ s ⊆ Q, ∏ P ∈ s, (idemAt P * d + (1 - idemAt P)) = idem s * d + (1 - idem s) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha, ih ((Finset.subset_insert a s).trans hs)]
    have e1 : idem (insert a s) = idemAt a + idem s := Finset.sum_insert ha
    rw [e1]
    refine val_mul d _ _ ?_
    have := idem_mul_idem_of_disjoint h (s := {a}) (s' := s)
      (Finset.singleton_subset_iff.2 (hs (Finset.mem_insert_self a s))) ((Finset.subset_insert a s).trans hs)
      (Finset.disjoint_singleton_left.2 ha)
    rwa [show idem ({a} : Finset (Pl D.host.E)) = idemAt a from Finset.sum_singleton _ _] at this

theorem detChar_eq_prod_res : ∀ {D : D7} {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A), t.Good →
    ∀ (β : GL (Fin V.rank) (Lev.EAf D)) {Q' : Finset (Pl D.host.E)}, SplitSet Q' → t.Q ⊆ Q' → ∀ {κ : GA D V},
    κ ∈ GfC V → Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ →
    detChar V t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  intro D V A _ t ht β Q' hQ' hsub κ _ hst hsupp
  have he : idem Q' * idem Q' = idem Q' := idem_mul_self hQ'
  have hce : idem Q' * cA D (idem Q') = 0 := hQ'.isIdemSum.2
  have hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := by
    have hx : IsDetAt (idem Q') V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := GlobalTheory.VecInv.isDetAt_detAt _ he V κ
    unfold IsDetAt at hx
    unfold IsDetRoot
    rw [hx]
    exact idempotent_det_conj_identity (cA D) (idem Q') he hce (mt V κ) hsupp (det_conj_mul V κ)
  rw [detChar_eq ht.real hroot]
  have hR : Q' \ t.Q ⊆ Q' := Finset.sdiff_subset
  have heR : idem (Q' \ t.Q) * idem (Q' \ t.Q) = idem (Q' \ t.Q) := idem_mul_self (hQ'.mono hR)
  have hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P := fun P hP => (hQ'.isIdemAt (hsub hP)).1.1
  have hsum : idem (Q' \ t.Q) + idem t.Q = idem Q' := Finset.sum_sdiff hsub
  have hRQ : idem (Q' \ t.Q) * idem t.Q = 0 := idem_mul_idem_of_disjoint hQ' hR hsub Finset.sdiff_disjoint
  have hsplit : GlobalTheory.VecInv.detAt (idem Q') he V κ = GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ *
      ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ := by
    ext
    rw [Units.val_mul, Units.coe_prod]
    show idem Q' * (mt V κ).det + (1 - idem Q') = (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) *
      ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))
    rw [Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)),
      prod_val _ ht.split t.Q (Finset.Subset.refl _), val_mul _ _ _ hRQ, hsum]
  have hw : t.chi (GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ) = 1 := by
    refine ht.unram _ ?_ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_mem hst _ heR))
      (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_inv_mem hst _ heR)) ?_
    · have hinf : infPart D (idem (Q' \ t.Q)) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [idem, map_sum]
        exact Finset.sum_eq_zero fun P hP => infPart_idemAt P _ (hQ'.isIdemAt (hR hP))
      show infPart D (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) = 1
      rw [map_add (f := _), map_mul, map_sub, map_one, hinf]
      ring
    · have a1 : idem t.Q * idem (Q' \ t.Q) = 0 := idem_mul_idem_of_disjoint hQ' hsub hR Finset.disjoint_sdiff
      have a2 : idem (Q' \ t.Q) * cA D (idem t.Q) = 0 := idem_mul_conj hQ' hR hsub
      show (idem t.Q + cA D (idem t.Q)) * (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) =
        idem t.Q + cA D (idem t.Q)
      linear_combination ((mt V κ).det - 1) * (a1 + a2)
  rw [hsplit, map_mul, hw, one_mul, map_prod,
    ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]
  refine Finset.prod_congr rfl fun P _ => ?_
  refine ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _
    (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (hQ'.isIdemAt (hsub P.2))).symm
  show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1
  linear_combination (1 - (mt V κ).det) * hPi P.1 P.2

end GlobalTheory.TwistDetStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryDetCharacterEqProdResidueGoodBaseFrame
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwistDetStabAll

open Classical GlobalTheory.TwistDetStab

variable {D : D7}

theorem exists_finUnit_isDetRoot {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {k : GA D V} (hk : k ∈ GfC V)
    (hst : Lev.finE V k ∈ St β) : ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ IsDetRoot V k x := by
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  obtain ⟨a, ha, -⟩ := GlobalTheory.VecInv.exists_det_int hst
  have hd : finPart D (mt V k).det ∈ intAE D := GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (ha ▸ a.2)
  have hw : (finHom V k).1.det - 1 ∈ intAE D :=
    sub_mem (hdet ▸ hd) (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (_root_.mul_one _))
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, -⟩ := GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ _ hw (one_nsmul _).symm hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_⟩
  have hk1 : infHom V k = 1 := hk
  rw [hk1, Units.val_one, Matrix.det_one] at hdet'
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)
  · change infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet', GlobalTheory.UnitDetRoot.infPart_sigR_one D _ hY1, hY1, _root_.mul_one]
  · change finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]
    exact hroot

theorem chi_detAt {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A) (ht : t.Good)
    {β : GL (Fin V.rank) (Lev.EAf D)} {κ : GA D V} (hst : Lev.finE V κ ∈ St β) (he : idem t.Q * idem t.Q = idem t.Q) :
    t.chi (GlobalTheory.VecInv.detAt (idem t.Q) he V κ) =
      ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  have hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P := fun P hP => (ht.split.isIdemAt hP).1.1
  have hsplit : GlobalTheory.VecInv.detAt (idem t.Q) he V κ =
      ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ := by
    ext
    rw [Units.coe_prod]
    show idem t.Q * (mt V κ).det + (1 - idem t.Q) = ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))
    rw [Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)),
      prod_val _ ht.split t.Q (Finset.Subset.refl _)]
  rw [hsplit, map_prod,
    ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]
  refine Finset.prod_congr rfl fun P _ => ?_
  refine ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _
    (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (ht.split.isIdemAt P.2)).symm
  show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1
  linear_combination (1 - (mt V κ).det) * hPi P.1 P.2

def offUnit {R : Type} [CommRing R] (f : R) (hf : f * f = f) (x : Rˣ) : Rˣ where
  val := f + (1 - f) * x.val
  inv := f + (1 - f) * (x⁻¹).val
  val_inv := by
    linear_combination (1 - f) ^ 2 * x.mul_inv + (2 - x.val - (x⁻¹).val) * hf
  inv_val := by
    linear_combination (1 - f) ^ 2 * x.mul_inv + (2 - x.val - (x⁻¹).val) * hf

theorem cmRing_idempotent_unitRatio_identity {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ z, c (c z) = z) (e d x : R) (h1 : e * e = e)
    (h2 : e * c e = 0) (hd : c d * d = 1) (hx : x = d * c x) :
    (e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x) =
      d * c ((e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x)) := by
  have h3 : c e * c e = c e := by rw [← map_mul, h1]
  have k : (e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x) = e * d + c e + (1 - (e + c e)) * x := by
    linear_combination (d - 1) * (1 - x) * (h1 + h2)
  rw [k]
  simp only [map_add (f := _), map_mul, map_sub, map_one, hc]
  linear_combination (1 - (e + c e)) * hx - c e * hd

theorem finPart_off_mem (f y : AE D) (hf : f * f = f) (hy : finPart D y ∈ intAE D) :
    finPart D (f + (1 - f) * y) ∈ intAE D := by
  have h1 : finPart D f ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hf])
  have h2 : finPart D (1 - f) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
    rw [← RingHom.map_mul]; congr 1; linear_combination hf)
  rw [RingHom.map_add (f := _), RingHom.map_mul]
  exact add_mem h1 (GlobalTheory.HeckeConj.mul_mem_intAE D h2 hy)

theorem detChar_eq_prod_res_of_frame {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A) (ht : t.Good)
    (β : GL (Fin V.rank) (Lev.EAf D)) {κ : GA D V} (hκ : κ ∈ GfC V) (hst : Lev.finE V κ ∈ St β) :
    detChar V t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, hx⟩ := exists_finUnit_isDetRoot hκ hst
  have he : idem t.Q * idem t.Q = idem t.Q := idem_mul_self ht.split
  have hce : idem t.Q * cA D (idem t.Q) = 0 := ht.split.isIdemSum.2
  have hcc : cA D (idem t.Q) * cA D (idem t.Q) = cA D (idem t.Q) := by rw [← RingHom.map_mul, he]
  have hf : (idem t.Q + cA D (idem t.Q)) * (idem t.Q + cA D (idem t.Q)) = idem t.Q + cA D (idem t.Q) := by
    linear_combination he + hcc + 2 * hce
  have hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem t.Q) he V κ * offUnit _ hf x) :=
    cmRing_idempotent_unitRatio_identity (cA D) GlobalTheory.DualPairCheck.cA_cA (idem t.Q) (mt V κ).det x he hce (det_conj_mul V κ) hx
  have hw : t.chi (offUnit _ hf x) = 1 := by
    refine ht.unram _ ?_ (finPart_off_mem _ _ hf hx2) (finPart_off_mem _ _ hf hx3) ?_
    · show infPart D (_ + (1 - _) * (x : AE D)) = 1
      rw [RingHom.map_add (f := _), RingHom.map_mul, hx1, RingHom.map_sub, RingHom.map_one]
      ring
    · show (idem t.Q + cA D (idem t.Q)) * ((idem t.Q + cA D (idem t.Q)) + (1 - (idem t.Q + cA D (idem t.Q))) * (x : AE D)) = _
      linear_combination (1 - (x : AE D)) * hf
  rw [detChar_eq ht.real hroot, map_mul, hw, _root_.mul_one, chi_detAt t ht hst he]

theorem detChar_eq_prod_res : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ {A : Type} [CommGroup A] (t : Twist D A),
    t.Good → ∀ {κ : GA D T}, κ ∈ GfC T → Lev.finE T κ ∈ St B.F.βT →
    detChar T t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) :=
  fun B _ _ _ t ht _ hκ hst => detChar_eq_prod_res_of_frame t ht B.F.βT hκ hst

end GlobalTheory.TwistDetStabAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryDetCharacterEqProdResidueGoodBaseFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDetCharacter_eq_prod_residue_goodBaseFrame : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ {A : Type} [CommGroup A] (t : Twist D A), t.Good → ∀ {κ : GA D T}, κ ∈ GfC T → Lev.finE T κ ∈ St B.F.βT → detChar T t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) := by
  exact @GlobalTheory.TwistDetStabAll.detChar_eq_prod_res
end
end

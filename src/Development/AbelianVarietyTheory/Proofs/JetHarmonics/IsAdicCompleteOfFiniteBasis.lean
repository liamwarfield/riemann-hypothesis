module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcAdd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ReInnerLeOnImageOfIntertwiningStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.FlatComplete

theorem mem_smul_top_iff_repr {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι]
    (b : Module.Basis ι O M) (J : Ideal O) (x : M) :
    x ∈ J • (⊤ : Submodule O M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun y => ∀ i, b.repr y i ∈ J) hx ?_ ?_
    · intro r hr y _ i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · intro y z hy hz i
      rw [map_add (f := _), Finsupp.add_apply]
      exact J.add_mem (hy i) (hz i)
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_finite_basis {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Fintype ι] (b : Module.Basis ι O M) (J : Ideal O) [hO : IsAdicComplete J O] :
    IsAdicComplete J M := by
  have hR : ∀ (n : ℕ) (r : O), r ∈ (J ^ n • ⊤ : Submodule O O) ↔ r ∈ J ^ n := fun n r => by
    rw [smul_eq_mul, Ideal.mul_top]
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (J ^ n • ⊤ : Submodule O M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (J ^ n • ⊤ : Submodule O O)] := fun n x y => by
    simp only [SModEq.sub_mem, hR, mem_smul_top_iff_repr b (J ^ n), map_sub, Finsupp.sub_apply]
  rw [isAdicComplete_iff]
  refine ⟨isHausdorff_iff.2 fun x hx => ?_, isPrecomplete_iff.2 fun f hf => ?_⟩
  · apply b.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus (inferInstance : IsHausdorff J O) _ fun n => ?_
    have := (key n x 0).1 (hx n) i
    rwa [map_zero, Finsupp.zero_apply] at this
  · have hc : ∀ i, ∃ L : O, ∀ n, b.repr (f n) i ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete J O) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    rw [← b.equivFun_apply (b.equivFun.symm L), LinearEquiv.apply_symm_apply]
    exact hL i n

theorem isAdicComplete_of_finite_flat (O : Type) [CommRing O] [IsLocalRing O] (J : Ideal O)
    (hO : IsAdicComplete J O) (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Module.Flat O A] : IsAdicComplete (J.map (algebraMap O A)) A := by
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  have := hO
  exact (IsAdicComplete.map_algebraMap_iff (I := J) (M := A)).2
    (isAdicComplete_of_finite_basis (Module.Free.chooseBasis O A) J)

end GlobalTheory.FlatComplete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfPowLeOfPowLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory

theorem _root_.GlobalTheory.isAdicComplete_of_pow_le_of_pow_le (A : Type) [CommRing A] (J J' : Ideal A) (k l : ℕ)
    (h1 : J ^ k ≤ J') (h2 : J' ^ l ≤ J) (h : IsAdicComplete J A) : IsAdicComplete J' A := by
  have hk : J ^ (k + 1) ≤ J' := le_trans (Ideal.pow_le_pow_right (Nat.le_succ k)) h1
  have hl : J' ^ (l + 1) ≤ J := le_trans (Ideal.pow_le_pow_right (Nat.le_succ l)) h2
  have hJ : ∀ m, J ^ ((k + 1) * m) ≤ J' ^ m := fun m => by
    rw [pow_mul]; exact Ideal.pow_right_mono hk m
  have hJ' : ∀ m, J' ^ ((l + 1) * m) ≤ J ^ m := fun m => by
    rw [pow_mul]; exact Ideal.pow_right_mono hl m
  exact
    { haus' := fun x hx => h.toIsHausdorff.haus' x fun m =>
        (hx ((l + 1) * m)).mono (Submodule.smul_mono_left (hJ' m))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun m => f ((l + 1) * m))
          (fun {m n} hmn => (hf (Nat.mul_le_mul_left (l + 1) hmn)).mono
            (Submodule.smul_mono_left (hJ' m)))
        refine ⟨L, fun n => ?_⟩
        have hn : n ≤ (l + 1) * ((k + 1) * n) :=
          (Nat.le_mul_of_pos_left n (Nat.succ_pos k)).trans
            (Nat.le_mul_of_pos_left _ (Nat.succ_pos l))
        exact (hf hn).trans ((hL ((k + 1) * n)).mono (Submodule.smul_mono_left (hJ n))) }

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPrimitiveIdempotentMapEqOne
open TensorProduct

namespace GlobalTheory

theorem exists_primitive_idempotent_map_eq_one {A R : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] (φ : A →+* R) :
    ∃ e : A, e * e = e ∧ e ≠ 0 ∧ (∀ f : A, f * f = f → f * e = f → f = 0 ∨ f = e) ∧ φ e = 1 := by
  let S : Set (Ideal A) := {I | ∃ e : A, e * e = e ∧ φ e = 1 ∧ I = Ideal.span {1 - e}}
  have hS : S.Nonempty := ⟨_, 1, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, hφe, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian A A)) S hS
  have key : ∀ f : A, f * f = f → f * e = f → φ f = 1 → f = e := by
    intro f hf hfe hφf
    have hle : Ideal.span {1 - e} ≤ Ideal.span {1 - f} := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨1 - e, by linear_combination hfe⟩
    have heq : Ideal.span {1 - e} = Ideal.span {1 - f} := by
      by_contra hne
      exact hmax _ ⟨f, hf, hφf, rfl⟩ (lt_of_le_of_ne hle hne)
    have hmem : 1 - f ∈ Ideal.span {1 - e} := heq ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    linear_combination e * hc - hfe + c * he
  refine ⟨e, he, ?_, ?_, hφe⟩
  · rintro rfl
    simp at hφe
  · intro f hf hfe
    have hid : IsIdempotentElem (φ f) := by
      change φ f * φ f = φ f
      rw [← map_mul, hf]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hid with h | h
    · left
      have := key (e - f) (by linear_combination he + hf - 2 * hfe)
        (by linear_combination he - hfe) (by rw [map_sub, h, hφe, sub_zero])
      linear_combination -this
    · exact Or.inr (key f hf hfe h)

theorem exists_placeU_mem_emb (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [Algebra ℤ_[p] R] (σ : OE →+* R) :
    ∃ w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE,
      σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e := by
  haveI : IsNoetherianRing (ℤ_[p] ⊗[ℤ] OE) :=
    IsNoetherianRing.of_finite ℤ_[p] _
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_primitive_idempotent_map_eq_one
    (ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (p := p) σ).toRingHom
  exact ⟨⟨e, h1, h2, h3⟩, h4⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantDerivAlongEndo
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.DerivEndo

open GlobalTheory.ChartTrans

variable {k : Type} [CommRing k] {d : ℕ}

theorem dof_endo (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (φ : Pt k 1 d) (hφ : GP φ)
    (hom : comp1 φ F = addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u (ev (n := 1) ![φ] g) = ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have key : ev (n := 2) ![F] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![F] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F := hom
    rw [this]
  rw [dof_eq _ hF hu, dof_eq F hF hu, key, ChartTrans.ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ChartTrans.ev_C_mul _ (single_point_zero_constant hφ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dof_smul_dir (F : Fin d → PS k 2 d) (c : k) (u : Fin d → k) (g : PS k 1 d) :
    Dof F (c • u) g = C c * Dof F u g := by
  unfold Dof
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem iterate_dof_C_mul (F : Fin d → PS k 2 d) (u : Fin d → k) (n : ℕ) (c : k) (g : PS k 1 d) :
    (Dof F u)^[n] (C c * g) = C c * (Dof F u)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul]

theorem dmonOf_endo (F : Fin d → PS k 2 d) (φ : Pt k 1 d) (hφ : GP φ) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (α : ι → k)
    (h : ∀ l g, Dof F (u l) (ev (n := 1) ![φ] g) = C (α l) * ev (n := 1) ![φ] (Dof F (u l) g))
    (m : ι →₀ ℕ) (g : PS k 1 d) :
    DmonOf F u m (ev (n := 1) ![φ] g) = C (∏ l, α l ^ m l) * ev (n := 1) ![φ] (DmonOf F u m g) := by
  have hit : ∀ (l : ι) (n : ℕ) (g : PS k 1 d), (Dof F (u l))^[n] (ev (n := 1) ![φ] g) =
      C (α l ^ n) * ev (n := 1) ![φ] ((Dof F (u l))^[n] g) := by
    intro l n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul, h, pow_succ,
        map_mul, mul_assoc]
  rw [← Finset.prod_map_toList]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, iterate_dof_C_mul, hit, List.map_cons, List.prod_cons,
      map_mul]
    ring

end GlobalTheory.DerivEndo

namespace GlobalTheory

open DerivEndo QuadDeriv

theorem invariantDeriv_along_endo : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (a : O), (∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) = ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g)) ∧ ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (α : ι → k), (∀ l, (dAct k B a).mulVec (u l) = α l • u l) → ∀ (m : ι →₀ ℕ) (g : PS k 1 d), constantCoeff (DmonOf (B.FK k) u m (ev (n := 1) ![B.actK k a] g)) = (∏ l, α l ^ m l) * constantCoeff (DmonOf (B.FK k) u m g) := by
  intro R _ d O _ _ k _ _ _ B a
  have hF : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const
  have hw : GP (B.actK k a) := constantCoeff_mapP_eq_zero _ _ (B.A.const a)
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k a) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k a) (pt k (n := 2) d 0))
      (comp1 (B.actK k a) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom a)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const a) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const a) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have h1 : ∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) =
      ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g) :=
    dof_endo (B.FK k) hF (congrFun hU) (B.actK k a) hw hom
  refine ⟨h1, fun ι _ u α hα m g => ?_⟩
  rw [dmonOf_endo (B.FK k) (B.actK k a) hw u α (fun l g => by
    rw [h1, hα, dof_smul_dir, ChartTrans.ev_C_mul _ (single_point_zero_constant hw)]), map_mul, constantCoeff_C,
    constSt k d (B.actK k a) hw]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelNegTAndQdet
open Formalism.REAL Finset

namespace GlobalTheory.CapelliNegT

theorem _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), _root_.Formalism.REAL.GlRel E →
      _root_.Formalism.REAL.GlRel (fun a b => -E b a) ∧
        ∀ u : ℂ, _root_.Formalism.REAL.qdet (fun a b => -E b a) u = ((-1 : ℂ) ^ n) • _root_.Formalism.REAL.qdet E ((n : ℂ) - 1 - u) := by
  intro A _ _ n E hE
  refine ⟨?_, fun u => ?_⟩
  · unfold _root_.Formalism.REAL.GlRel at hE ⊢
    intro a b c d
    have h := hE b a d c
    rw [neg_mul_neg, neg_mul_neg, h]
    simp only [@eq_comm _ a d, @eq_comm _ c b]
    split_ifs <;> abel
  · have hrow : ∀ v : ℂ, _root_.Formalism.REAL.qdet E v = _root_.PI.qminorRow E id id v := by
      intro v
      have key : _root_.PI.RowForm := _root_.quantum_minor_row_form
      unfold _root_.PI.RowForm at key
      exact key A n n E hE id id v
    have hM : ∀ (x : ℂ) (a b : Fin n),
        _root_.Formalism.REAL.Tm (fun a b => -E b a) x a b = -_root_.Formalism.REAL.Tm E (-x) b a := by
      intro x a b
      unfold _root_.Formalism.REAL.Tm
      by_cases h : a = b
      · subst h
        simp only [if_true, map_neg]
        abel
      · simp only [h, Ne.symm h, if_false]
        abel
    have hneg : ∀ g : Fin n → A, (List.ofFn fun k => -g k).prod = (-1) ^ n * (List.ofFn g).prod := by
      intro g
      have hl : (List.ofFn fun k => -g k) = (List.ofFn g).map Neg.neg := by
        rw [List.map_ofFn]
        rfl
      rw [hl, List.prod_map_neg, List.length_ofFn]
    have harg : ∀ k : Fin n, -(u - ((k : ℕ) : ℂ)) = (n : ℂ) - 1 - u - n + 1 + ((k : ℕ) : ℂ) := by
      intro k
      ring
    rw [hrow]
    unfold _root_.Formalism.REAL.qdet _root_.Formalism.REAL.qminor _root_.PI.qminorRow
    rw [Algebra.smul_def, map_pow, map_neg, map_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hM, hneg, harg, id]
    rw [← mul_assoc, ← mul_assoc, ((Commute.neg_one_right _).pow_right n).eq]

end GlobalTheory.CapelliNegT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermLinearPartCoordinatePointZero
section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.LogExpAdaptedGauge
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge

section Chart

variable {k : Type} [CommRing k] {d : ℕ}

def linMap (U : Matrix (Fin d) (Fin d) k) : Pt k 1 d :=
  fun i => ∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)

end Chart

section Gauges

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

variable {O : Type} [CommRing O] [StarRing O]

end Gauges

section Integrality

variable {C : Type} [NormedField C] {d : ℕ}

end Integrality

section Letters

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Letters

end GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge
end
end

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.GermDerivativeLinearMaps

section Calc

variable {k : Type} [CommRing k] {d : ℕ}

theorem dLin_comp (φ ψ : Pt k 1 d) (hψ : GP ψ) : dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  ext i j
  refine (FormalCalc.coeff_single_subst (a := fun p : Fin 1 × Fin d => (![ψ] : Fin 1 → Pt k 1 d) p.1 p.2)
    (fun p => single_point_zero_constant hψ p.1 p.2) (φ i) _).trans ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mul_apply]
  rfl

theorem germComp_matrixLinearMap_apply {n : ℕ} (U : Matrix (Fin d) (Fin d) k) (a : Pt k n d) (ha : GP a) (i : Fin d) :
    comp1 (LogExpAdaptedGauge.linMap U) a i = ∑ j, C (U i j) * a j := by
  have hz : FormalLog.CZ (![a] : Fin 1 → Pt k n d) := fun j l => single_point_zero_constant ha j l
  show ev ![a] (∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)) = _
  rw [FormalLog.ev_sum hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FormalLog.ev_mul hz, FormalLog.ev_C hz, FormalLog.ev_X hz]
  rfl

theorem gp_linMap (U : Matrix (Fin d) (Fin d) k) : GP (LogExpAdaptedGauge.linMap U) := fun i => by
  simp [LogExpAdaptedGauge.linMap]

theorem dLin_linMap (U : Matrix (Fin d) (Fin d) k) : dLin (LogExpAdaptedGauge.linMap U) = U := by
  classical
  ext i j
  simp [dLin, LogExpAdaptedGauge.linMap, coeff_C_mul, coeff_X, Finsupp.single_left_inj]

theorem linMap_one {n : ℕ} (a : Pt k n d) (ha : GP a) : comp1 (LogExpAdaptedGauge.linMap (1 : Matrix (Fin d) (Fin d) k)) a = a := by
  classical
  funext i
  rw [germComp_matrixLinearMap_apply _ _ ha, Finset.sum_eq_single i] <;> simp +contextual [Matrix.one_apply, eq_comm]

end Calc

section Log

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

theorem additive_at {n : ℕ} (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ψ : Pt k 1 d)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1))
    (a b : Pt k n d) (ha : GP a) (hb : GP b) : comp1 ψ (addOf F a b) = comp1 ψ a + comp1 ψ b := by
  have hV := pair_points_zero_constant ha hb
  have e := congrArg (evP ![a, b]) hψ
  have e2 : ∀ u v : Pt k 2 d, evP ![a, b] (u + v) = evP ![a, b] u + evP ![a, b] v := fun u v =>
    funext fun i => gt_ev_add _ hV _ _
  rw [e2, evP_comp1 _ hV _ _ (gp_addOf F hF _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_comp1 _ hV _ _ (gp_pt 0),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV] at e
  exact e

theorem germLinearPart_coordinatePoint_zero : dLin (pt k (n := 1) d 0) = 1 := by
  rw [← linMap_one (pt k (n := 1) d 0) (gp_pt 0), gt_comp1_pt_right, dLin_linMap]

theorem additive_eq_lin (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ℓ ε ψ : Pt k 1 d)
    (h1 : dLin ℓ = 1) (hℓ : comp1 ℓ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1)) (hi : IsInvPair ℓ ε) (h0 : GP ψ)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1)) :
    ψ = comp1 (LogExpAdaptedGauge.linMap (dLin ψ)) ℓ := by
  classical
  have hε : GP ε := hi.2.1
  have hℓ0 : GP ℓ := hi.1
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 := gp_comp1 _ _ hε p0
  have q1 := gp_comp1 _ _ hε p1
  have ps : GP (pt k (n := 2) d 0 + pt k (n := 2) d 1) := fun i => by simp [pt]
  have e1 : comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      addOf F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) := by
    rw [← gt_comp_inv' hi _ (gp_addOf F hF _ _ q0 q1), additive_at F hF ℓ hℓ _ _ q0 q1,
      gt_comp_inv hi _ p0, gt_comp_inv hi _ p1]
  have e2 : comp1 (comp1 ψ ε) (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 (comp1 ψ ε) (pt k (n := 2) d 0) + comp1 (comp1 ψ ε) (pt k (n := 2) d 1) := by
    rw [gt_comp1_comp1 _ _ hε _ ps, gt_comp1_comp1 _ _ hε _ p0, gt_comp1_comp1 _ _ hε _ p1, e1,
      additive_at F hF ψ hψ _ _ q0 q1]
  have hdε : dLin ε = 1 := by
    have := dLin_comp ℓ ε hε
    rwa [hi.2.2.1, germLinearPart_coordinatePoint_zero, h1, one_mul, eq_comm] at this
  have e3 : comp1 ψ ε = LogExpAdaptedGauge.linMap (dLin ψ) := by
    have hd : dLin (comp1 ψ ε) = dLin (LogExpAdaptedGauge.linMap (dLin ψ)) := by
      rw [dLin_comp _ _ hε, hdε, mul_one, dLin_linMap]
    funext i
    ext e
    by_cases he : e.degree = 1
    · obtain ⟨⟨s, j⟩, rfl⟩ : ∃ s, e = Finsupp.single s 1 := by
        exact (Finsupp.sum_eq_one_iff e).1 he
      obtain rfl : s = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun hd i) j
    · rw [addition_linear k d _ (congrFun e2 i) e he]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LogExpAdaptedGauge.linMap, map_sum, coeff_C_mul, coeff_X]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [if_neg, mul_zero]
      rintro rfl
      simp at he
  rw [← e3, gt_comp1_comp1 _ _ hε _ hℓ0, hi.2.2.2, gt_comp1_pt_right]

end Log

section Predicates

variable {C : Type} [NormedField C] [IsUltrametricDist C] {d : ℕ}

end Predicates

section Predicates2

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
  {O : Type} [CommRing O] [StarRing O]

end Predicates2

section Letters

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Letters

section Frame

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Frame

end GlobalTheory.GermDerivativeLinearMaps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeTensorOperatorRaise
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormAddSqLeOfBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormAddSqLeOfBounds
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_norm_add_sq_le_of_bounds :
    ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  intro V ι _ _ u v c s N hc hs hN hu hv
  have hcs : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hv0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (c * s * N) ^ 2 := by
    calc _ ≤ _ := hcs
      _ ≤ (c ^ 2 * N) * (s ^ 2 * N) := mul_le_mul hu hv hv0 (by positivity)
      _ = _ := by ring
  have h2 : ∑ i, ‖u i‖ * ‖v i‖ ≤ c * s * N :=
    (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun i _ => by positivity) (by positivity)
      two_ne_zero).1 h1
  have h3 : ∑ i, ‖u i + v i‖ ^ 2 ≤ ∑ i, (‖u i‖ ^ 2 + 2 * (‖u i‖ * ‖v i‖) + ‖v i‖ ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖u i + v i‖ ^ 2 ≤ (‖u i‖ + ‖v i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ = _ := by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h3
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormAddSqLeOfBoundsStatement
open Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_norm_add_sq_le_add_sq_mul : ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  first | exact @GlobalTheory.sum_norm_add_sq_le_of_bounds | exact GlobalTheory.sum_norm_add_sq_le_of_bounds | (intros; apply GlobalTheory.sum_norm_add_sq_le_of_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeTensorOperatorRaise
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.TensOp

def tensAct {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    (E : Module.End ℂ V) (A : Matrix ι ι ℂ) : Module.End ℂ (PiLp 2 (fun _ : ι => V)) where
  toFun x := WithLp.toLp 2 (fun i => E (x i) + ∑ j, A i j • x j)
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib]
    abel
  map_smul' r x := by
    ext i
    simp [Finset.smul_sum, smul_smul, mul_comm]

theorem tensAct_apply {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    (E : Module.End ℂ V) (A : Matrix ι ι ℂ) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct E A x i = E (x i) + ∑ j, A i j • x j := rfl

def sumMap {V N ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] (φ : ι → V →ₗ[ℂ] N) :
    PiLp 2 (fun _ : ι => V) →ₗ[ℂ] N where
  toFun x := ∑ j, φ j (x j)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum]

theorem sumMap_apply {V N ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] (φ : ι → V →ₗ[ℂ] N) (x : PiLp 2 (fun _ : ι => V)) :
    sumMap φ x = ∑ j, φ j (x j) := rfl

theorem kunit_tensAct {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι] {n : ℕ}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (A : Fin n → Fin n → Matrix ι ι ℂ)
    (hE : KUnit ε E) (hA : ∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) :
    KUnit ε (fun a b => tensAct (E a b) (A a b)) := by
  intro a b hab x y
  simp only [PiLp.inner_apply, tensAct_apply, inner_add_left, inner_add_right, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.sum_add_distrib, hE a b hab]
  congr 1
  rw [Finset.sum_comm, ← hA a b hab]
  simp [Matrix.conjTranspose_apply]

theorem core (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (N ι : Type) [NormedAddCommGroup N]
    [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N)
    (φ : ι → V →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ) (hE : KUnit ε E) (hF : KUnit ε F)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hA : ∀ a b, ε a = ε b → (A a b).conjTranspose = A b a)
    (hAs : ∀ x : ι → V, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0)
      ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2)
    (hφ : ∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w)
    (hb : ∀ x : V, (∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0) ≤ c ^ 2 * ‖x‖ ^ 2)
    (w : V) (j : ι) : CasKLe ε F (c + s) (φ j w) := by
  set K : Fin n → Fin n → Module.End ℂ (PiLp 2 (fun _ : ι => V)) := fun a b => tensAct (E a b) (A a b) with hK
  have hKu : KUnit ε K := kunit_tensAct ε E A hE hA
  have hint : ∀ a b, ε a = ε b → ∀ x, F a b (sumMap φ x) = sumMap φ (K a b x) := by
    intro a b hab x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hK, sumMap_apply, tensAct_apply, map_sum, map_add (f := _), map_smul, hφ a b hab,
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
  have hcas : ∀ x, sumMap φ (CasK ε K x) = CasK ε F (sumMap φ x) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CasK, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · simp only [Module.End.mul_apply]
      rw [hint b a hab.symm, hint a b hab]
    · simp
  have hbound : ∀ x, (⟪x, CasK ε K x⟫_ℂ).re ≤ (c + s) ^ 2 * ‖x‖ ^ 2 := by
    intro x
    rw [(GlobalTheory.T.casK_isSymmetric_and_inner_re_eq _ n ε K hKu).2 x]
    have h := GlobalTheory.T.sum_norm_add_sq_le_add_sq_mul V (Fin n × Fin n × ι)
      (fun p => if ε p.1 = ε p.2.1 then E p.1 p.2.1 (x p.2.2) else 0)
      (fun p => if ε p.1 = ε p.2.1 then ∑ j, A p.1 p.2.1 p.2.2 j • x j else 0) c s (‖x‖ ^ 2) hc hs
      (by positivity) ?_ ?_
    · refine le_trans (le_of_eq ?_) h
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with hab
      · rw [PiLp.norm_sq_eq_of_L2]; rfl
      · simp
    · rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ => hb (x i))
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm (s := (univ : Finset ι))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm (s := (univ : Finset ι))]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · rw [PiLp.norm_sq_eq_of_L2]
      refine le_trans (le_of_eq ?_) (hAs (fun i => x i))
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
  refine ⟨LinearMap.range (sumMap φ), inferInstance, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨x, rfl⟩
    exact ⟨K a b x, (hint a b hab x).symm⟩
  · refine ⟨WithLp.toLp 2 (Pi.single j w), ?_⟩
    rw [sumMap_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · simp
  · rintro _ ⟨x, rfl⟩
    exact GlobalTheory.T.re_inner_le_on_image_of_intertwining' _ N (sumMap φ) (CasK ε K) (CasK ε F) _ (GlobalTheory.T.casK_isSymmetric_and_inner_re_eq _ n ε K hKu).1
      (GlobalTheory.T.casK_isSymmetric_and_inner_re_eq _ n ε F hF).1 hcas hbound x

theorem casKLe_tensor_operator : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N ι : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N) (φ : ι → M →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ), KUnit ε E → KUnit ε F → 0 ≤ c → 0 ≤ s → (∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) → (∀ x : ι → M, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0) ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2) → (∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w) → ∀ w, CasKLe ε E c w → ∀ j, CasKLe ε F (c + s) (φ j w) := by
  intro M _ _ n ε E N ι _ _ _ _ F φ A c s hE hF hc hs hA hAs hφ w hw j
  obtain ⟨S, hfd, hst, hwS, hb⟩ := hw
  let E' : Fin n → Fin n → Module.End ℂ S := fun a b =>
    if h : ε a = ε b then (E a b).restrict (hst a b h) else 0
  have hE' : ∀ a b, ε a = ε b → ∀ x : S, (E' a b x : M) = E a b x := by
    intro a b h x
    simp [E', h]
  have := core S n ε E' N ι F (fun i => (φ i).comp S.subtype) A c s ?_ hF hc hs hA ?_ ?_ ?_ ⟨w, hwS⟩ j
  · exact this
  · intro a b h x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hE' a b h, hE' b a h.symm, hE a b h]
  · intro x
    have h := hAs (fun i => (x i : M))
    simpa only [Submodule.coe_norm, Submodule.coe_sum, Submodule.coe_smul] using h
  · intro a b h i x
    simp [hE' a b h, hφ a b h]
  · intro x
    have h := hb x x.2
    rw [(GlobalTheory.T.casK_isSymmetric_and_inner_re_eq _ n ε E hE).2] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · rw [← hE' a b hab]; rfl
    · rfl

end GlobalTheory.TensOp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeTensorOperatorRaiseStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCasimirLe_tensorOperator_raise : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N ι : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N) (φ : ι → M →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ), KUnit ε E → KUnit ε F → 0 ≤ c → 0 ≤ s → (∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) → (∀ x : ι → M, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0) ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2) → (∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w) → ∀ w, CasKLe ε E c w → ∀ j, CasKLe ε F (c + s) (φ j w) := by
  first | exact @GlobalTheory.TensOp.casKLe_tensor_operator | exact GlobalTheory.TensOp.casKLe_tensor_operator | (intros; apply GlobalTheory.TensOp.casKLe_tensor_operator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfDisjointCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AdicColimit

theorem _root_.GlobalTheory.AdicColimit.isAdicColimit_of_disjoint_cover (R : Type) [CommRing R] (I : Ideal R)
    (T : Over (Spec (CommRingCat.of R))) (𝒰 : T.left.OpenCover.{0})
    (hd : ∀ i j, i ≠ j → Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j)))
    (h : ∀ i, _root_.GlobalTheory.AdicColimit.IsAdicColimit I (Over.mk (𝒰.f i ≫ T.hom))) :
    _root_.GlobalTheory.AdicColimit.IsAdicColimit I T := by
  obtain ⟨r, hr⟩ : ∃ r : ∀ i, Over.mk (𝒰.f i ≫ T.hom) ⟶ T, ∀ i, (r i).left = 𝒰.f i :=
    ⟨fun i => Over.homMk (𝒰.f i) rfl, fun i => rfl⟩
  intro X f hf

  have hfi : ∀ i, ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (𝒰.f i ≫ T.hom)) ≫
      (_root_.GlobalTheory.AdicColimit.thickHom I (e + 1) (r i) ≫ f (e + 1)) = _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e := by
    intro i e
    rw [_root_.GlobalTheory.AdicColimit.thickMap_thickHom_assoc, hf]
  choose g hg hgu using fun i => h i X (fun e => _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e) (hfi i)
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have : pullback.fst (𝒰.f i) (𝒰.f i) = pullback.snd (𝒰.f i) (𝒰.f i) :=
        (cancel_mono (𝒰.f i)).1 pullback.condition
      rw [this]
    · haveI : IsEmpty ↥(pullback (𝒰.f i) (𝒰.f j)) := ⟨fun x =>
        Set.disjoint_left.1 (hd i j hij) ⟨pullback.fst (𝒰.f i) (𝒰.f j) x, rfl⟩
          ⟨pullback.snd (𝒰.f i) (𝒰.f j) x, by
            rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨𝒰.glueMorphisms g hglue, fun e => ?_, fun y hy => ?_⟩
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ (_root_.GlobalTheory.AdicColimit.thickι I e T)) _ _ fun i => ?_
    change pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _ =
      pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc, Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]
    let φ : pullback (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ⟶
        (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj R I e (Over.mk (𝒰.f i ≫ T.hom))).left :=
      pullback.lift (pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i))
        (pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e))
        (by
          show pullback.snd _ _ ≫ 𝒰.f i ≫ T.hom = _
          rw [← Category.assoc, ← pullback.condition]
          simp only [Category.assoc]
          exact congrArg (fun k => pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ k)
            (pullback.condition (f := T.hom) (g := _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)))
    have hφ₁ : φ ≫ _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (𝒰.f i ≫ T.hom)) =
        pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) := pullback.lift_fst _ _ _
    have hφ₂ : φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i) = pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) := by
      apply pullback.hom_ext
      · change (φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T =
          pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T
        rw [Category.assoc, _root_.GlobalTheory.AdicColimit.thickHom_ι, ← Category.assoc, hφ₁]
        erw [hr i]
        exact pullback.condition.symm
      · have hw := Over.w ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)).map (r i))
        change (φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) = _
        rw [Category.assoc]
        erw [hw]
        exact pullback.lift_snd _ _ _
    rw [← hφ₁, Category.assoc]
    erw [hg i e]
    rw [← Category.assoc, hφ₂]
  · refine 𝒰.hom_ext _ _ fun i => ?_
    rw [Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]
    refine hgu i _ fun e => ?_
    have hcomp := _root_.GlobalTheory.AdicColimit.thickHom_ι_assoc I e (r i) y
    rw [hr] at hcomp
    rw [← hcomp, hy]

end GlobalTheory.AdicColimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitFiniteHenselianOfLocal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.AdicColimit

theorem smodEq_smul_top_map {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (f : M →ₗ[A] N) {x y : M} (h : x ≡ y [SMOD (J • ⊤ : Submodule A M)]) :
    f x ≡ f y [SMOD (J • ⊤ : Submodule A N)] := by
  rw [SModEq.sub_mem] at h ⊢
  rw [← map_sub]
  have : (J • ⊤ : Submodule A M).map f ≤ J • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨_, h, rfl⟩

theorem isAdicComplete_of_retract {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (s : N →ₗ[A] M) (p : M →ₗ[A] N) (hps : ∀ x, p (s x) = x)
    (h : IsAdicComplete J M) : IsAdicComplete J N := by
  refine { toIsHausdorff := ⟨?_⟩, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    have : s x = 0 := IsHausdorff.haus h.toIsHausdorff (s x) fun n => by
      simpa using smodEq_smul_top_map _ s (hx n)
    rw [← hps x, this, map_zero]
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => s (f n)) fun {m n} hmn =>
      smodEq_smul_top_map _ s (hf hmn)
    exact ⟨p L, fun n => by simpa [hps] using smodEq_smul_top_map _ p (hL n)⟩

theorem isAdicComplete_map_eval {A ι : Type} [CommRing A] (T : ι → Type) [∀ i, CommRing (T i)]
    (e : A ≃+* Π i, T i) (J : Ideal A) (h : IsAdicComplete J A) (i : ι) :
    IsAdicComplete (J.map ((Pi.evalRingHom T i).comp e.toRingHom)) (T i) := by
  classical
  letI : Algebra A (T i) := ((Pi.evalRingHom T i).comp e.toRingHom).toAlgebra
  let s : T i →ₗ[A] A :=
    { toFun t := e.symm (Pi.single i t)
      map_add' x y := by rw [Pi.single_add, map_add (f := _)]
      map_smul' a t := by
        apply e.injective
        rw [RingHom.id_apply, smul_eq_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply,
          ← Pi.single_mul_right]
        rfl }
  refine (IsAdicComplete.map_algebraMap_iff J (T i)).2
    (isAdicComplete_of_retract J s (Algebra.linearMap A (T i)) (fun t => ?_) h)
  change e (e.symm (Pi.single i t)) i = t
  rw [e.apply_symm_apply, Pi.single_eq_same]

theorem isAdicColimit_finite_henselian_of_local :
    (∀ (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A] [IsLocalRing A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ)))) → (∀ (R : Type) [CommRing R] (I : Ideal R) (T : Over (Spec (CommRingCat.of R))) (𝒰 : T.left.OpenCover.{0}), (∀ i j, i ≠ j → Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j))) → (∀ i, IsAdicColimit I (Over.mk (𝒰.f i ≫ T.hom))) → IsAdicColimit I T) → ∀ (R : Type) [CommRing R] (I : Ideal R) (O : Type) [CommRing O] [HenselianLocalRing O] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  intro hloc hcov R _ I O _ _ A _ _ _ φ hc
  classical
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O A
  let π (i : ι) : A →+* T i := (Pi.evalRingHom T i).comp e.toRingEquiv.toRingHom
  have hopen (i : ι) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (π i))) := by
    have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
      inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance
  let 𝒰 : (Spec (CommRingCat.of A)).OpenCover := Scheme.Cover.mkOfCovers ι
    (fun i => Spec (CommRingCat.of (T i))) (fun i => Spec.map (CommRingCat.ofHom (π i))) (fun x => by
      obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
        (PrimeSpectrum.comap e.toRingEquiv.symm.toRingHom x)
      refine ⟨i, q, ?_⟩
      change PrimeSpectrum.comap e.toRingEquiv.toRingHom (PrimeSpectrum.comap (Pi.evalRingHom T i) q) = x
      rw [hq]
      ext a
      change e.symm (e a) ∈ x.asIdeal ↔ _
      rw [e.symm_apply_apply]) hopen
  refine hcov R I (Over.mk (Spec.map (CommRingCat.ofHom φ))) 𝒰 (fun i j hij => ?_) fun i => ?_
  · rw [Set.disjoint_left]
    rintro x ⟨p, rfl⟩ ⟨q, hq⟩
    change ι at i j
    change PrimeSpectrum (T i) at p
    change PrimeSpectrum (T j) at q
    change PrimeSpectrum.comap (π j) q = PrimeSpectrum.comap (π i) p at hq
    have h1 : e.symm (Pi.single i 1) ∈ (PrimeSpectrum.comap (π j) q).asIdeal := by
      change e (e.symm (Pi.single i 1)) j ∈ q.asIdeal
      rw [e.apply_symm_apply, Pi.single_eq_of_ne (i := i) (i' := j) (fun h => hij h.symm)]
      exact zero_mem _
    rw [hq] at h1
    change e (e.symm (Pi.single i 1)) i ∈ p.asIdeal at h1
    rw [e.apply_symm_apply, Pi.single_eq_same] at h1
    exact p.isPrime.one_notMem h1
  · change ι at i
    have := (hT i).1
    have key := hloc R I (T i) ((π i).comp φ) (by
      rw [← Ideal.map_map]
      exact isAdicComplete_map_eval T e.toRingEquiv _ hc i)
    rw [CommRingCat.ofHom_comp, Spec.map_comp] at key
    exact key

end GlobalTheory.AdicColimit
end

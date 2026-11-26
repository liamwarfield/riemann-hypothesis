module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsPreconnectedBlockUnits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriangularMul
namespace GlobalTheory.LowerTriangularMul

theorem lowerTriangular_mul {S : Type} [CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), i < j → A i j = (0 : S))
    (hB : ∀ (i j : Fin n), i < j → B i j = (0 : S)) :
    ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with hik | hki
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (lt_of_le_of_lt hki hij), mul_zero]

theorem main : ∀ {S : Type} [inst : CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S), (∀ (i j : Fin n), i < j → A i j = (0 : S)) → (∀ (i j : Fin n), i < j → B i j = (0 : S)) → ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) :=
  fun A B hA hB => lowerTriangular_mul A B hA hB

end GlobalTheory.LowerTriangularMul
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

section Tri

variable {S : Type} [CommRing S] {n : ℕ}

theorem lowerTri_mul (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) : ∀ i j, i < j → (A * B) i j = 0 := by
  first
  | exact @_root_.GlobalTheory.LowerTriangularMul.main
  | exact _root_.GlobalTheory.LowerTriangularMul.main
  | (apply _root_.GlobalTheory.LowerTriangularMul.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LowerTriangularMul.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LowerTriangularMul.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LowerTriangularMul.main ..)

theorem lowerTri_mul_diag (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hB k i h, mul_zero]
  · rw [hA i k h, zero_mul]

theorem lowerTri_isUnit_det (A : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hd : ∀ i, IsUnit (A i i)) : IsUnit A.det := by
  have h : A.BlockTriangular OrderDual.toDual := fun i j hij => hA i j hij
  rw [Matrix.det_of_lowerTriangular A h]
  exact IsUnit.prod_univ_iff.mpr hd

theorem lowerTri_inv (A : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hd : IsUnit A.det) : ∀ i j, i < j → A⁻¹ i j = 0 := by
  have h : A.BlockTriangular OrderDual.toDual := fun i j hij => hA i j hij
  letI := Matrix.invertibleOfIsUnitDet A hd
  have h' := Matrix.blockTriangular_inv_of_blockTriangular h
  exact fun i j hij => h' hij

end Tri

theorem frBor_iff_frChg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ) :
    FrBor t y y' ↔ ∃ g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S),
      (∀ τ i j, i < j → g τ i j = 0) ∧ (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧
        FrChg g (t none : S) y y' := by
  have hid : spMap (RingHom.id S) = 𝟙 _ := by
    show Spec.map (𝟙 (CommRingCat.of S)) = _
    exact Spec.map_id _
  constructor
  · rintro ⟨hx, hu, pm, h1, h2, h3⟩
    choose cf hd hz hc using hu
    refine ⟨fun τ => Matrix.of (cf τ), fun τ i j h => hz τ i j h, hd, hx, hc, pm, h1, ?_, h3⟩
    rw [hid]
    exact h2.trans (Category.comp_id _).symm
  · rintro ⟨g, hz, hd, hx, hc, pm, h1, h2, h3⟩
    refine ⟨hx, fun τ i => ⟨g τ i, hd τ i, hz τ i, hc τ i⟩, pm, h1, ?_, h3⟩
    rw [hid] at h2
    exact h2.trans (Category.comp_id _)

theorem frBor_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), (∀ t : Ix Dw → Sˣ, FrBor t y y' ↔ ∃ g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S), (∀ τ i j, i < j → g τ i j = 0) ∧ (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ FrChg g (t none : S) y y') ∧ (y'.x = y.x → (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → S, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt y.x (y.u τ) cf (y'.u τ i)) → ∃ t : Ix Dw → Sˣ, FrBor t y y') ∧ (∀ t t' : Ix Dw → Sˣ, FrBor t y y' → FrBor t' y' y'' → FrBor (t' * t) y y'') ∧ (∀ t : Ix Dw → Sˣ, FrBor t y y' → FrBor t⁻¹ y' y) := by
  intro E _ _ _ H Dw l Xo c S _ _ y y' y''
  refine ⟨frBor_iff_frChg y y', fun hx hu => ?_, fun t t' h h' => ?_, fun t h => ?_⟩
  · obtain ⟨g₀, a, -, -, -, hs⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c S y y').1 hx
    choose cf hd hz hc using hu
    refine ⟨fun k => match k with
      | none => a
      | some ⟨τ, i⟩ => (hd τ i).unit, (frBor_iff_frChg y y' _).2
        ⟨fun τ => Matrix.of (cf τ), fun τ i j h => hz τ i j h, fun τ i => ?_, hx, hc, hs⟩⟩
    exact (hd τ i).unit_spec.symm
  · obtain ⟨g, hz, hd, hc⟩ := (frBor_iff_frChg y y' t).1 h
    obtain ⟨g', hz', hd', hc'⟩ := (frBor_iff_frChg y' y'' t').1 h'
    refine (frBor_iff_frChg y y'' _).2 ⟨fun τ => g' τ * g τ,
      fun τ => lowerTri_mul _ _ (hz' τ) (hz τ), fun τ i => ?_, ?_⟩
    · show (g' τ * g τ) i i = _
      rw [lowerTri_mul_diag _ _ (hz' τ) (hz τ), hd, hd', Pi.mul_apply, Units.val_mul]
    · rw [Pi.mul_apply, Units.val_mul]
      exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S y y' y'').2 g g' _ _ hc hc'
  · obtain ⟨g, hz, hd, hc⟩ := (frBor_iff_frChg y y' t).1 h
    have hdet : ∀ τ, IsUnit (g τ).det := fun τ =>
      lowerTri_isUnit_det _ (hz τ) fun i => by rw [hd]; exact Units.isUnit _
    have hinv : ∀ τ, (g τ)⁻¹ * g τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet τ)
    have hzi : ∀ τ i j, i < j → (g τ)⁻¹ i j = 0 := fun τ => lowerTri_inv _ (hz τ) (hdet τ)
    obtain ⟨z, hzc, -⟩ := GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S y' (fun τ => (g τ)⁻¹) (t none)⁻¹
      fun τ => Matrix.isUnit_nonsing_inv_det _ (hdet τ)
    have h1 := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S y y' z).2 g _ _ _ hc hzc
    simp only [hinv, Units.inv_mul] at h1
    have h0 := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S y y y).1
    have hzy : z = y := (GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S y (fun _ => 1) 1 (fun τ => by simp)).unique h1 h0
    subst hzy
    refine (frBor_iff_frChg y' z _).2 ⟨fun τ => (g τ)⁻¹, hzi, fun τ i => ?_, hzc⟩
    have h2 := lowerTri_mul_diag _ _ (hzi τ) (hz τ) i
    rw [hinv, Matrix.one_apply_eq, hd] at h2
    rw [Pi.inv_apply]
    exact Units.eq_inv_of_mul_eq_one_right h2.symm

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.Relab

theorem relab_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0) ∧ (∀ τ, relab c σ (conjEmb τ) = conjEmb (relab c σ τ)) ∧ ∀ (Dw : Datum H) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  intro E _ _ _ H l c σ hσ
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ' : E →+* ℂ, (relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0) := by
    intro τ'
    have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
    have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
    · refine ⟨fun _ => hx, fun _ => ?_⟩
      rw [hval, ← hσ0]
      exact congrArg σ (Subtype.ext hx)
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · exfalso
        have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
          rw [← map_neg]
          exact congrArg σ (Subtype.ext hx)
        rw [← hval, h, hσ0] at h1
        exact h0 (by linear_combination h1 / 2)
      · exfalso
        exact h0 (by linear_combination (h.symm.trans hx) / 2)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  refine ⟨⟨hinj, hsurj⟩, hrel, ?_, ?_⟩
  · intro τ
    ext a
    have key : ∀ (ρ : E →+* ℂ) (x : E), conjEmb ρ x = ρ (IsCMField.complexConj E x) := fun ρ x =>
      (IsCMField.complexEmbedding_complexConj E ρ x).symm
    rw [key]
    exact congrArg σ (Subtype.ext (key τ a))
  · intro Dw g e τ
    obtain ⟨τ₀, rfl⟩ := hsurj τ
    have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
      have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
        Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
      have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
        e.subtypeEquiv (fun _ => Iff.rfl)
      have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} ≃ Fin (Dw.mult τ₀) := Equiv.sigmaSubtype τ₀
      rw [Nat.card_congr (e1.trans (e2.trans e3)), Nat.card_eq_fintype_card, Fintype.card_fin]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hcard]
      unfold Datum.mult
      rw [if_pos ((hrel τ₀).1 h)]
    · rw [hcard]
      unfold Datum.mult
      rw [if_neg (fun h' => h ((hrel τ₀).2 h'))]

end GlobalTheory.Relab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompatStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0) ∧ (∀ τ, relab c σ (conjEmb τ) = conjEmb (relab c σ τ)) ∧ ∀ (Dw : Datum H) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  first | exact @GlobalTheory.Relab.relab_good | exact GlobalTheory.Relab.relab_good | (intros; apply GlobalTheory.Relab.relab_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem isDerivAt0_ex_isTanAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → (∀ w v, IsDerivAt0 (fun z => (F.ex k P z).left) w v → IsTanAt (F.u k P) v) ∧ (∀ w, ∃! v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsDerivAt0 (fun z => (F.ex k P z).left) w v) ∧ ∀ v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsTanAt (F.u k P) v → ∃! w, IsDerivAt0 (fun z => (F.ex k P z).left) w v := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P hP
  have h0 := (F.ex_ker k P hP 0).2 (zero_mem _)
  refine ⟨fun w v hv => ⟨((HolHom.isDerivAt0_iff _ _ _).1 hv).over, ?_⟩, fun w => ?_, fun v hv => ?_⟩
  · exact hv.1.trans (congrArg (·.left) h0)
  · obtain ⟨v, hv, -⟩ := (F.ex_diff k P hP).1 w
    exact ⟨v.left, hv, fun v' hv' =>
      ((HolHom.isDerivAt0_iff _ _ _).1 hv').unique ((HolHom.isDerivAt0_iff _ _ _).1 hv)⟩
  · exact (F.ex_diff k P hP).2 (Over.homMk v hv.1) (hv.2.trans (congrArg (·.left) h0).symm)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangentStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_derivative_at_zero_isTangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → (∀ w v, IsDerivAt0 (fun z => (F.ex k P z).left) w v → IsTanAt (F.u k P) v) ∧ (∀ w, ∃! v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsDerivAt0 (fun z => (F.ex k P z).left) w v) ∧ ∀ v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsTanAt (F.u k P) v → ∃! w, IsDerivAt0 (fun z => (F.ex k P z).left) w v := by
  first | exact @GlobalTheory.isDerivAt0_ex_isTanAt | exact GlobalTheory.isDerivAt0_ex_isTanAt | (intros; apply GlobalTheory.isDerivAt0_ex_isTanAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExpChain

theorem isDerivAt0_comp_linear {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem isHolTo_slice {g m : ℕ} {X : Scheme.{0}} (e : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : IsHolTo (Set.univ ×ˢ Set.univ) e) : IsHolTo Set.univ (fun z => e (0, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hj : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin m → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage hj.continuous
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, true_and] using h3
  · exact h2.comp hj.differentiableOn fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩

theorem isHolTo_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) :
    IsHolTo Set.univ (fun z => (F.ex k P z).left) := by
  have h := (F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have h2 := isHolTo_slice _ h
  simp only at h2
  exact h2

theorem isDerivAt0_ex_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → ∀ (k' : Fin F.n) (P' : (F.Di k').La →+ (Fin g → ℂ)) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsPeriod (F.Di k') ty P' → (∀ z, (F.ex k' P' (L z)).left = (F.ex k P z).left) → ∀ w (v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)), IsDerivAt0 (fun z => (F.ex k P z).left) w v ↔ IsDerivAt0 (fun z => (F.ex k' P' z).left) (L w) v := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P _ k' P' L hP' hL w v
  rw [← isDerivAt0_comp_linear _ (isHolTo_ex F k' P' hP') L w v]
  simp only [hL]

end GlobalTheory.ExpChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitFrames

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

section Mat

variable {n : ℕ}

theorem psgn_sq (p0 k : ℕ) : psgn p0 k = 1 ∨ psgn p0 k = -1 := by
  induction k with
  | zero => left; simp [psgn]
  | succ k ih =>
    rw [psgn_succ]
    rcases ih with h | h <;> rcases sgn_sq p0 k with h' | h' <;> simp [h, h']

theorem lminor_signature (p0 : ℕ) (i : Fin (n + 1)) :
    lminor (Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) i
      = ((psgn p0 i : ℝ) : ℂ) := by
  rw [lminor_diagonal, psgn, Complex.ofReal_prod, Finset.prod_range]
  rfl

theorem uMat_conj_eq_signature (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re)
    (h1 : ∀ i : Fin (n + 1), ‖lminor A i‖ = 1) :
    (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ)
      = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by
  have hdet : ∀ c : Fin n, (blk A c).det ≠ 0 := by
    intro c h0
    have h := h1 ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ := by
      ext a c; simp [Matrix.conjTranspose_apply]
    rw [hB, e]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hdiag : B = Matrix.diagonal fun k => B k k := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB,
        uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), lminor A i
      = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have e : lminor B i = lminor A i := by
      rw [hB, lminor_conj (uMat_upper _) i]
      simp only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← e]
    exact (congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)
  have hre : ∀ k, (B k k).im = 0 := fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)
  have hval : ∀ i : Fin (n + 1), lminor A i = ((psgn p0 i : ℝ) : ℂ) := by
    intro i
    have him : (lminor A i).im = 0 := by
      rw [hprod i]
      refine Complex.conj_eq_iff_im.1 ?_
      rw [map_prod]
      exact Finset.prod_congr rfl fun j _ => Complex.conj_eq_iff_im.2 (hre _)
    have hd : lminor A i = (((lminor A i).re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    have hn := h1 i
    have hp := hs i
    rw [hd, Complex.norm_real, Real.norm_eq_abs] at hn
    rw [hd, Complex.ofReal_inj]
    rcases psgn_sq p0 i with h | h <;> rw [h] at hp ⊢
    · rw [abs_of_pos (by linarith)] at hn; exact hn
    · rw [abs_of_neg (by linarith)] at hn; linarith
  rw [hdiag]
  congr 1
  funext k
  have hsucc : lminor A k.succ = lminor A k.castSucc * B k k := by
    rw [hprod k.succ, hprod k.castSucc]
    exact prod_castLE_succ (f := fun k => B k k) k.isLt
  rw [hval, hval, Fin.val_succ, Fin.val_castSucc, psgn_succ, Complex.ofReal_mul] at hsucc
  have hne : ((psgn p0 k : ℝ) : ℂ) ≠ 0 := by
    rcases psgn_sq p0 k with h | h <;> simp [h]
  exact (mul_left_cancel₀ hne hsucc).symm

theorem det_uMat (A : Matrix (Fin n) (Fin n) ℂ) : (uMat A).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (uMat_upper _)]
  simp only [uMat_diag, Finset.prod_const_one]

theorem inv_uMat_upper (A : Matrix (Fin n) (Fin n) ℂ) : (uMat A)⁻¹.BlockTriangular id := by
  haveI := Matrix.invertibleOfIsUnitDet (uMat A) (by rw [det_uMat]; exact isUnit_one)
  exact Matrix.blockTriangular_inv_of_blockTriangular (uMat_upper A)

theorem inv_uMat_diag (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : (uMat A)⁻¹ i i = 1 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (uMat A)
    (by rw [det_uMat]; exact isUnit_one)) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, uMat_diag, mul_one, Matrix.one_apply_eq] at h
  · exact h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [inv_uMat_upper A h', zero_mul]
    · rw [uMat_upper A h', mul_zero]
  · simp

end Mat

theorem unit_frame_eq_orthonormal_mul_triangular :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  intro E _ _ _ r p0 Ψ Gm hG
  refine ⟨fun x hx h1 => ?_, fun x₀ h => ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩,
    fun τ u x₀ hu => ?_⟩
  · refine ⟨fun τ => (mat x τ * uMat (gram τ.1 Gm (mat x τ)) : Matrix _ _ ℂ),
      fun τ => ((uMat (gram τ.1 Gm (mat x τ)))⁻¹ : Matrix _ _ ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩,
      fun τ => ?_, fun τ i => ?_, ?_⟩
    · show ((uMat (gram τ.1 Gm (mat x τ)))⁻¹).det ≠ 0
      rw [Matrix.det_nonsing_inv, det_uMat]
      simp
    · exact inv_uMat_upper _ hca
    · show gram τ.1 Gm (mat x τ * uMat (gram τ.1 Gm (mat x τ))) = _
      rw [FrameDegreeData.gram_mul]
      exact uMat_conj_eq_signature p0 _ (gram_isHermitian τ.1 hG _) (hx τ).2 (h1 τ)
    · show ‖(uMat (gram τ.1 Gm (mat x τ)))⁻¹ i i‖ = 1
      rw [inv_uMat_diag, norm_one]
    · funext τ
      show mat x τ = (mat x τ * uMat (gram τ.1 Gm (mat x τ))) * (uMat (gram τ.1 Gm (mat x τ)))⁻¹
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ (by rw [det_uMat]; exact isUnit_one)]
  · intro h0
    have h2 := congrArg Matrix.det (h τ)
    rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
      Matrix.det_diagonal] at h2
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
    rcases sgn_sq p0 k with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature, Complex.ofReal_re]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [FrameDegreeData.gram_mul, FrameDegreeData.gram_eq τ Gm u, hu, FrameDegreeData.gram_eq]

end GlobalTheory.UnitFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangularStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  first | exact @GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | exact GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | (intros; apply GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ThetaHalf

theorem exists_real_of_half {g : ℕ} {c : Fin g → ℂ} (hc : ∀ i, c i = 0 ∨ c i = 1 / 2) :
    ∃ a : Fin g → ℝ, c = fun i => (a i : ℂ) := by
  refine ⟨fun i => if c i = 0 then 0 else 1 / 2, funext fun i => ?_⟩
  rcases hc i with h | h
  · show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_pos h, h, Complex.ofReal_zero]
  · have h0 : c i ≠ 0 := by rw [h]; norm_num
    show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_neg h0, h]
    norm_num

theorem thetaChar_holomorphic_ne_zero : ∀ (g : ℕ) (c₁ c₂ : Fin g → ℂ), (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → (∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → (τ.map Complex.im).PosDef → Differentiable ℂ (thetaChar τ c₁ c₂) ∧ ∃ z, thetaChar τ c₁ c₂ z ≠ 0) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B ∧ DifferentiableOn ℂ (fun b => τ b i j) B) → DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2)) (B ×ˢ Set.univ) := by
  intro g c₁ c₂ h₁ h₂
  obtain ⟨a, rfl⟩ := exists_real_of_half h₁
  obtain ⟨b, rfl⟩ := exists_real_of_half h₂
  refine ⟨fun τ hs hp => ⟨GlobalTheory.CanTh.differentiable_thetaChar (GlobalTheory.CanTh.mem_thetaDomain hp) a b, ?_⟩, ?_⟩
  · by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact GlobalTheory.CanTh.thetaChar_ne_zero hs hp a b (funext hcon)
  · intro m B h τ _ hτ hdiff
    have hT : ∀ i j, DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => τ w.1 i j) (B ×ˢ Set.univ) :=
      fun i j => (hdiff i j).2.comp differentiableOn_fst fun w hw => hw.1
    have hZ : DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => h w.1 *ᵥ w.2) (B ×ˢ Set.univ) := by
      rw [differentiableOn_pi]
      intro i
      simp only [Matrix.mulVec, dotProduct]
      have hj : ∀ j, DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => h w.1 i j) (B ×ˢ Set.univ) :=
        fun j => (hdiff i j).1.comp differentiableOn_fst fun w hw => hw.1
      refine DifferentiableOn.fun_sum fun j _ => (hj j).mul ?_
      have hs : Differentiable ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => w.2 j) := by fun_prop
      exact hs.differentiableOn
    have hdom : ∀ w ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)), τ w.1 ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin g) :=
      fun w hw => GlobalTheory.CanTh.mem_thetaDomain (hτ w.1 hw.1).2
    exact GlobalTheory.CanTh.differentiableOn_thetaChar hT hZ hdom a b

end GlobalTheory.ThetaHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamiliesStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_half_differentiable_ne_zero_families : ∀ (g : ℕ) (c₁ c₂ : Fin g → ℂ), (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → (∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → (τ.map Complex.im).PosDef → Differentiable ℂ (thetaChar τ c₁ c₂) ∧ ∃ z, thetaChar τ c₁ c₂ z ≠ 0) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B ∧ DifferentiableOn ℂ (fun b => τ b i j) B) → DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2)) (B ×ˢ Set.univ) := by
  first | exact @GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero | exact GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero | (intros; apply GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DerivEig

open GlobalTheory.HolHom

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem fst_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.fst (epsMul s x) = x.fst := by
  simp [epsMul]

theorem snd_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.snd (epsMul s x) = s * x.snd := by
  simp [epsMul]

theorem isDerivAt_epsMul {c : V → (Sp ℂ ⟶ X)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt c z w v)
    (s : ℂ) : HolHom.IsDerivAt c z (s • w) (spMap (epsMul s) ≫ v) := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← h.1]
    congr 2
    ext1
    exact RingHom.ext fun x => fst_epsMul s x
  · rw [valR_spMap _ _ _ ((le_preimage_dual_iff h.1 U).2 hU), snd_epsMul, h.2 U hU, map_smul, smul_eq_mul]

theorem isDerivAt_of_comp_linear {c : V → (Sp ℂ ⟶ X)} (hc : HolAt c 0) (L : V →L[ℂ] V) {w : V}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt (fun t => c (L t)) 0 w v) : HolHom.IsDerivAt c 0 (L w) v := by
  have h0 : c (L 0) = c 0 := by rw [map_zero]
  refine ⟨h.1.trans h0, fun U hU f => ?_⟩
  rw [h.2 U (by beta_reduce; rw [h0]; exact hU) f]
  have h1 : HasFDerivAt (fun t => valAt' (c t) U f) (fderiv ℂ (fun t => valAt' (c t) U f) 0) (L 0) := by
    rw [map_zero]; exact ((hc U hU).2 f).hasFDerivAt
  exact congrArg (· w) (h1.comp 0 L.hasFDerivAt).fderiv

end General

theorem eq_of_relab_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) {τ τ' : E →+* ℂ}
    (h : ∀ a : 𝓞 E, relab c σ τ (a : E) = relab c σ τ' (a : E)) : τ = τ' := by
  refine IsLocalization.ringHom_ext (𝓞 E)⁰ (RingHom.ext fun a => ?_)
  exact congrArg Subtype.val (σ.injective (h a))

end GlobalTheory.DerivEig

open GlobalTheory.HolHom GlobalTheory.DerivEig in
theorem GlobalTheory.isEigAt_iff_of_isDerivAt0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∀ (w : Fin g → ℂ) (v : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)) (τ : E →+* ℂ), IsDerivAt0 (fun z => (F.ex k P z).left) w v → (IsEigAt c τ v ↔ ∀ j, w j ≠ 0 → (e j).1 = τ) := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP w v τ hv
  have hhol : HolAt (fun z => (F.ex k P z).left) 0 := holAt_of_isHolTo (isHolTo_ex F k hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  have hact : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (fun j => relab c σ (e j).1 (a : E) * w j) (v ≫ (Xo.univ.t.act.act a).left) := by
    intro a
    let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
      ContinuousLinearMap.pi fun j => relab c σ (e j).1 (a : E) • ContinuousLinearMap.proj j
    have h1 := hv'.comp (Xo.univ.t.act.act a).left
    have h2 : (fun t => (F.ex k P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (F.ex k P (L t)).left := by
      funext t
      rw [← Over.comp_left, ← F.ex_lin k P hP a t]
      rfl
    rw [h2] at h1
    exact isDerivAt_of_comp_linear hhol L h1
  have hsc : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (relab c σ τ (a : E) • w) (spMap (epsMul (algebraMap c.F (CAt σ) (embK c τ a))) ≫ v) :=
    fun a => isDerivAt_epsMul hv' _
  constructor
  · intro h j hj
    refine eq_of_relab_eq c σ fun a => ?_
    have h1 := hact a
    have h2 : HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)
        (v ≫ (Xo.univ.t.act.act a).left) :=
      Eq.mpr (congrArg (HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)) (h a)) (hsc a)
    have h3 := eq_of_forall_fderiv_eq hhol (F.ex_diff k P hP).2 fun U hU f =>
      (h1.2 U hU f).symm.trans (h2.2 U hU f)
    exact mul_right_cancel₀ hj (congrFun h3 j)
  · intro h a
    have h1 := hact a
    have h3 : (fun j => relab c σ (e j).1 (a : E) * w j) = relab c σ τ (a : E) • w := by
      funext j
      by_cases hj : w j = 0
      · simp [hj]
      · rw [h j hj]; rfl
    rw [h3] at h1
    exact h1.unique (hsc a)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.IsoExt

theorem exists_gl_of_equiv {E : Type} [Field E] [NumberField E] {r : ℕ} {L L' : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (φ' : L' →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hφ' : Function.Injective φ') (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (gam : L ≃ₗ[𝓞 E] L') : ∃ γ : GL (Fin r) E,
      ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ' (gam v) := by
  obtain ⟨A, hA⟩ := GlobalTheory.FrameFibre.exists_matrix φ hφ hspan (φ' ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := GlobalTheory.FrameFibre.exists_matrix φ' hφ' hspan' (φ ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v, A *ᵥ φ v = φ' (gam v) := hA
  have hB' : ∀ v, B *ᵥ φ' v = φ (gam.symm v) := hB
  have hAB : A * B = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan' fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB', hA',
      Matrix.one_mulVec, LinearEquiv.apply_symm_apply]
  exact ⟨⟨A, B, hAB, mul_eq_one_comm.1 hAB⟩, hA'⟩

theorem exists_unitary_of_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (gam : D.La ≃ₗ[𝓞 E] D'.La), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) → (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) → ∃ γ : GL (Fin r) E, (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ ∀ a, φ' (gam a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' gam _ hl hl' hiso
  obtain ⟨γ, hγ⟩ := exists_gl_of_equiv φ φ' hl.1 hl.2.1 hl'.1 hl'.2.1 gam
  refine ⟨γ, ?_, fun a => (hγ a).symm⟩
  by_cases hξ : ξ = 0
  · have h0 : ∀ x : D.La, x = 0 := fun x => by
      apply D.unimod.1
      rw [map_zero]
      refine LinearMap.ext fun y => ?_
      have h := hl.2.2.2.2 x y
      rw [hξ, zero_mul, map_zero] at h
      exact_mod_cast h
    have h1 : ∀ u : Fin r → E, u = 0 := fun u => by
      have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hl.2.1]; trivial
      have hle : Submodule.span E (Set.range φ) ≤ ⊥ := Submodule.span_le.2 (by
        rintro _ ⟨x, rfl⟩
        rw [h0 x, map_zero]
        exact Submodule.zero_mem _)
      exact hle hu
    intro u v
    rw [h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u), h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v), h1 u,
      h1 v]
  · exact GlobalTheory.FrameFibre.herm_of_trace φ hl.2.1 Gm γ ξ hξ fun v w => by
      rw [hγ, hγ, ← hl.2.2.2.2, ← hl'.2.2.2.2, hiso]

end GlobalTheory.IsoExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometryStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_matrix_of_lattice_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (gam : D.La ≃ₗ[𝓞 E] D'.La), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) → (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) → ∃ γ : GL (Fin r) E, (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ ∀ a, φ' (gam a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  first | exact @GlobalTheory.IsoExt.exists_unitary_of_isometry | exact GlobalTheory.IsoExt.exists_unitary_of_isometry | (intros; apply GlobalTheory.IsoExt.exists_unitary_of_isometry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
namespace GlobalTheory.LocalQuad

theorem landherrSt_of_hasseNormSt : GlobalTheory.Published.HasseNormSt → GlobalTheory.Published.LandherrSt :=
  fun H => GlobalTheory.Published.landherrSt_of_landherr (landherr_of_hasseNormSt H)

end GlobalTheory.LocalQuad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProjByBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
noncomputable section
namespace GlobalTheory.AbLaw.BaseChange

theorem cst_comp_specMap {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {X : Scheme.{0}}
    (f' : X ⟶ Spec (CommRingCat.of R')) (W : X.Opens) (r : R) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) W r = cst f' W (g r) := by
  have h := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).hom r)
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom] at h ⊢
  rw [h]

theorem ap_top_eq_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {W : X.Opens} (h : W ≤ f ⁻¹ᵁ ⊤) (d : Γ(Spec (CommRingCat.of R), ⊤)) :
    ∃ r, ap f h d = cst f W r := by
  obtain ⟨r, rfl⟩ := (cst_bijective (𝟙 (Spec (CommRingCat.of R))) (W := ⊤) rfl).2 d
  exact ⟨r, by rw [ap_cst, Category.comp_id]⟩

end GlobalTheory.AbLaw.BaseChange

open GlobalTheory.AbLaw.BaseChange in
theorem GlobalTheory.AbLaw.isProjBy_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsProjBy f → IsProjBy f' := by
  intro R R' _ _ g X X' f p q sq hf
  obtain ⟨H, hH, m, s, hs, hs'⟩ := hf
  have hloc : ∀ a, nonzeroLocus (boxSec p q (s a) (oneSec _)) = p ⁻¹ᵁ nonzeroLocus (s a) ⊓ q ⁻¹ᵁ ⊤ := fun a => by
    rw [nonzeroLocus_boxSec, nonzeroLocus_oneSec]
  have hbox : (box p q H (Inh.trivLB _)).IsLB := by
    have hK : (Inh.trivLB (Spec (CommRingCat.of R'))).IsLB := by
      refine ⟨?_, ?_, ?_⟩
      · simp [Inh.trivLB]
      · intro i
        exact (res _).map_one
      · intro i j k
        exact (congrArg₂ (· * ·) (res _).map_one (res _).map_one).trans
          ((_root_.one_mul _).trans (res _).map_one.symm)
    refine ⟨?_, ?_, ?_⟩
    · refine top_le_iff.1 fun y _ => ?_
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ i, (Inh.trivLB _).U i by rw [hK.cover]; trivial)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
    · intro a
      refine Units.ext ((rs_mul p q _ _ _ _ _).trans ?_)
      rw [ap_g_self p hH, ap_g_self q hK, _root_.mul_one, Units.val_one]
    · intro a b c
      refine Units.ext ((congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).trans
        (Eq.trans ?_ (rs_mul p q _ _ _ _ _).symm))
      exact (mul_mul_mul_comm _ _ _ _).trans
        (congrArg₂ (· * ·) (ap_cocycle p hH _ _ _ _ _ _).symm (ap_cocycle q hK _ _ _ _ _ _).symm)
  refine ⟨box p q H (Inh.trivLB _), hbox, m,
    fun a => boxSec p q (s a) (oneSec _), ?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [hloc]
    exact ⟨hi, trivial⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' a
  have aff₂ : IsAffineOpen (⊤ : (Spec (CommRingCat.of R')).Opens) := isAffineOpen_top _
  have loc := hloc a
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  refine ⟨?_, fun b => ap p l₁ (r₁ b), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_ap p _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg (· * _) (ap_ratio p (hr₁ b k.1) _ _)).trans (_root_.mul_assoc _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C (g c), by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w, GlobalTheory.AbLaw.BaseChange.cst_comp_specMap]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X i, ?_⟩
        simp only [MvPolynomial.eval₂Hom_X']
    · change ap q l₂ _ ∈ _
      obtain ⟨r, hr⟩ := GlobalTheory.AbLaw.BaseChange.ap_top_eq_cst q l₂ d
      exact ⟨MvPolynomial.C r, by rw [MvPolynomial.eval₂Hom_C, hr]⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem isIntegral_rat_zeta_of_coeff (n : ℕ) : IsIntegral ℚ (zeta n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : zeta 0 = 1 := by simp [zeta]
    rw [this]; exact isIntegral_one
  · have h := Complex.isPrimitiveRoot_exp n hn.ne'
    exact (h.isIntegral hn).tower_top

theorem exists_coeff_containing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (s : Finset ℂ), (∀ z ∈ s, IsAlgebraic ℚ z) → ∃ c : Coeff l, ∀ z ∈ s, z ∈ c.F := by
  intro E _ _ _ H l s hs
  classical
  let b := Module.finBasis ℚ E
  let S : Set ℂ := (s : Set ℂ) ∪ Set.range (fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2)) ∪
    {zeta l.M', H.rt0, zeta l.A}
  have hfin : S.Finite := ((s.finite_toSet).union (Set.finite_range _)).union (Set.toFinite _)
  haveI : Finite S := hfin.to_subtype
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x ((hx | ⟨p, rfl⟩) | hx)
    · exact (hs x hx).isIntegral
    · exact (Algebra.IsIntegral.isIntegral (R := ℚ) (b p.2)).map p.1.toRatAlgHom
    · rcases hx with rfl | rfl | rfl
      · exact isIntegral_rat_zeta_of_coeff _
      · refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
        rw [H.sqrt_neg_disc_sq]
        exact (isIntegral_natCast _).neg
      · exact isIntegral_rat_zeta_of_coeff _
  have hsub : S ⊆ IntermediateField.adjoin ℚ S := IntermediateField.subset_adjoin _ _
  refine ⟨⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint, ?_, ?_, ?_⟩, ?_⟩
  · intro τ a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr a, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _ (hsub (Or.inl (Or.inr ⟨(τ, i), rfl⟩)))
  · exact hsub (Or.inr (by simp))
  · refine IntermediateField.adjoin.mono _ _ _ ?_
    intro x hx
    exact Or.inr (Or.inr hx)
  · intro z hz
    exact hsub (Or.inl (Or.inl hz))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPeriodMulVec
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PeriodLin

theorem _root_.GlobalTheory.PeriodLin.exists_period_mulVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P → IsUnit h₀.det → (∀ j j', h₀ j j' ≠ 0 → ty j = ty j') → ∃ P' : D.La →+ (Fin g → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' ∧ ∀ a, P' a = h₀ *ᵥ P a := by
  intro E _ _ _ H D g ty P h₀ hP hu hty
  refine ⟨(h₀.mulVecLin).toAddMonoidHom.comp P,
    _root_.GlobalTheory.PeriodConn.isPeriod_mulVec hP (isUnit_iff_ne_zero.mp hu) fun i j hij => ?_,
    fun a => rfl⟩
  by_contra hne
  exact hij (hty i j hne)

end GlobalTheory.PeriodLin
end

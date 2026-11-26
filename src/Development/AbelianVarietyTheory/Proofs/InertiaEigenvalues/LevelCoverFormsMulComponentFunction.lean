module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsIndicatingComp
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsIndicatingComp
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRead

theorem exists_idempotents_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : U.Comp → Rul Xo c, (∀ k, χ k ∈ sec Xo c 0 0) ∧ (∀ k, χ k * χ k = χ k) ∧ (∀ k k', k ≠ k' → χ k * χ k' = 0) ∧ ∑ k, χ k = 1 ∧ ∀ k k' x, x ∈ (U.X k').dom → (k' = k → rdU U (χ k) k' x = 1) ∧ (k' ≠ k → rdU U (χ k) k' x = 0) := by
  intro E _ _ _ H Dw l Xo c σ r U hr hσ hU hF
  obtain ⟨g, e, F, ik, φ, hφ, hP⟩ := hU.2.2.2.2.2
  have hb : Function.Bijective ik := by
    refine GlobalTheory.T.framedUniformisation_components_periodSpaces_bijective E H Dw l Xo c σ r U hr hσ hU g e F ik φ hφ (fun k x => ?_)
    obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hP k x
    exact ⟨Pm, h1, h2, h3, h4⟩
  obtain ⟨χ, h0, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotentSections_periodSpaces E H Dw l Xo c σ g _ F hF
  refine ⟨fun k => χ (ik k), fun k => h0 _, fun k => h1 _, fun k k' h => h2 _ _ (fun h' => h (hb.1 h')), ?_, ?_⟩
  · rw [← h3]
    exact hb.sum_comp χ
  · intro k k' x hx
    obtain ⟨Pm, -, hp, hu, -⟩ := hP k' ⟨x, hx⟩
    have hv := h4 (U.un k' ⟨x, hx⟩) (ik k) (ik k') Pm hp hu
    have hr : rdU U (χ (ik k)) k' x = toC (evR Xo c (χ (ik k)) (U.un k' ⟨x, hx⟩)) := dif_pos hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hr, hv, if_pos (congrArg ik h)]
    · rw [hr, hv, if_neg (fun h' => h (hb.1 h'))]

end GlobalTheory.CompRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsIndicatingCompStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_idempotent_sections_indicating_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : U.Comp → Rul Xo c, (∀ k, χ k ∈ sec Xo c 0 0) ∧ (∀ k, χ k * χ k = χ k) ∧ (∀ k k', k ≠ k' → χ k * χ k' = 0) ∧ ∑ k, χ k = 1 ∧ ∀ k k' x, x ∈ (U.X k').dom → (k' = k → rdU U (χ k) k' x = 1) ∧ (k' ≠ k → rdU U (χ k) k' x = 0) := by
  first | exact @GlobalTheory.CompRead.exists_idempotents_rdU | exact GlobalTheory.CompRead.exists_idempotents_rdU | (intros; apply GlobalTheory.CompRead.exists_idempotents_rdU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRatFinCongOfMarks
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompRead

open GlobalTheory.CharRead

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}


set_option maxHeartbeats 800000 in
theorem exists_rat_finCong_of_marks (l : Level H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (t : Dw.La → La)
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : La ≃ₗ[𝓞 D.host.E] Λ) (φ' : La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (t a) : Fin V.rank → D.host.E) - (finHom V g).1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (t a) : Fin V.rank → D.host.E) - (finHom V g').1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hΛ hΛ'
  obtain ⟨r1, -, r3, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := exists_unitary_of_trace_eq _ _ (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.1 (GlobalTheory.T.adelicElementLattice_full_and_completion D V g').2.1
    φ φ' _ ξ hξ htr
  obtain ⟨γ, hγ⟩ := r3 δ hδ3
  obtain ⟨m1, m2⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ δ g hγ
  have hlat : latG V (γ * g) = latG V g' := by
    ext v
    have hv : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
        (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have a1 := m1 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    have a2 := hδ2 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    rw [hv] at a1 a2
    exact a1.symm.trans a2
  have hc : FinCong V l.M ((γ * g)⁻¹ * g') := by
    refine finCong_of_marks l V io hio _ _ hlat (fun a => finVec V (φ' (t a) : Fin V.rank → D.host.E)) ?_ hM'
    intro a ha
    obtain ⟨w, hw, e⟩ := hM a ha
    refine ⟨_, (m2 w).1 hw, ?_⟩
    have e2 := congrArg (fun z => (finHom V γ).1 *ᵥ z) e
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
    rw [(r5 _ δ hγ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hδ1] at e2
    exact e2
  have hu : gLat V ((γ * g)⁻¹ * g') = latHat V := by
    refine gLat_eq_of_finCong V _ ((GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat) ?_
    have e0 : ((γ * g)⁻¹ * g')⁻¹ = g'⁻¹ * (γ * g) := by group
    rw [e0]
    exact (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat.symm
  exact ⟨γ, (r1 γ).2 ⟨δ, hγ⟩, _, hu, hc, (mul_inv_cancel_left _ _).symm⟩

theorem exists_rat_finCong_of_index {l : Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {n : ℕ}
    {ty : Fin n → D.host.E →+* ℂ}
    (F : FamilyUnif Xo s ty) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) (i i' : Fin F.n) (hi : i = i')
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] Λ) (φ' : (F.Di i').La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)))
    (htr' : ∀ a b, (((F.Di i').EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (F.t i a) : Fin V.rank → D.host.E) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (F.t i' a) : Fin V.rank → D.host.E) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hi
  exact exists_rat_finCong_of_marks l V io hio (F.t i) g g' Λ Λ' hΛ hΛ' φ φ' ξ hξ
    (fun a b => (htr a b).symm.trans (htr' a b)) hM hM'


end GlobalTheory.CompRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RdUMulApply
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory

theorem rdU_mul_apply : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (f f' : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r), rdU U (f * f') k x = rdU U f k x * rdU U f' k x := by
  intro E _ _ _ H Dw l Xo c σ r U f f' k x
  classical
  by_cases h : x ∈ (U.X k).dom
  · have e := evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
    exact e
  · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h, mul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompMulMemHolSub
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRat

theorem compMul_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (w : Comp → ℂ) {P : FDSec X}
    (hP : P ∈ holSub X la) : (fun k x => w k * P k x) ∈ holSub X la := by
  unfold holSub at hP
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    exact holCusp_mem_holSub X la fun k =>
      (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 (w k) (Q k) (hQ k)
  | zero =>
    have : (fun k x => w k * (0 : FDSec X) k x) = (0 : FDSec X) := by
      funext k x; simp
    rw [this]; exact Submodule.zero_mem _
  | add Q R _ _ hQ hR =>
    have : (fun k x => w k * (Q + R) k x) =
        ((fun k x => w k * Q k x) + (fun k x => w k * R k x) : FDSec X) := by
      funext k x; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hQ hR
  | smul a Q _ hQ =>
    have : (fun k x => w k * (a • Q) k x) = (a • (fun k x => w k * Q k x) : FDSec X) := by
      funext k x; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ hQ

theorem holSub_compMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (w : Comp → ℂ) (P : FDSec X), (P ∈ holSub X la → (fun k x => w k * P k x) ∈ holSub X la) ∧ (P ∈ holSub0 X la → (fun k x => w k * P k x) ∈ holSub0 X la) := by
  intro E _ _ _ r Comp X la w P
  refine ⟨compMul_mem_holSub X la w, fun h => ⟨compMul_mem_holSub X la w h.1, fun k x hx => ?_⟩⟩
  have h0 : P k x = 0 := h.2 k x hx
  show w k * P k x = 0
  rw [h0, mul_zero]

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsMulStableWeberValues
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionMulAdelicFunctionLevelCover
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorComponentsOfAdelicInvariantFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorComponentsOfAdelicInvariantFunction
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompFactor


set_option maxHeartbeats 1000000 in
theorem exists_factor_comp : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∃ v : U.Comp → c.F, ∀ h : GA D V, w h = v (dict h).1 := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio _ _ _ hW hD _ w _ h2 h3
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h h', ik (dict h).1 = ik (dict h').1 → w h = w h' := by
    intro h h' hi
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    obtain ⟨γ', hγ', hΛ', hm', -⟩ := hD.2 h'
    have hξ : -(-D.host.xi0) ≠ 0 := by
      rw [← (hW (dict h).1).2]
      exact neg_ne_zero.2 (U.X _).ξ0_ne
    obtain ⟨δ, hδ, u, hu, hc, eu⟩ := GlobalTheory.CompRead.exists_rat_finCong_of_index F V io hio.emb _ _ hi _ _ _ _
      (SetLike.ext' (hΛ.trans (Set.image_id _))) (SetLike.ext' (hΛ'.trans (Set.image_id _))) (φ _) (φ _) _ hξ
      (htr _) (htr _) hm hm'
    rw [← h2 γ' hγ' h', eu, h3 u hu hc, h2 δ hδ, h2 γ hγ]
  have hv : ∀ k : U.Comp, ∃ a : c.F, ∀ h, (dict h).1 = k → w h = a := by
    intro k
    by_cases hex : ∃ h, (dict h).1 = k
    · obtain ⟨h, hi⟩ := hex
      exact ⟨w h, fun h' hi' => key h' h (congrArg ik (hi'.trans hi.symm))⟩
    · exact ⟨0, fun h hi => absurd ⟨h, hi⟩ hex⟩
  choose v hv using hv
  exact ⟨v, fun h => hv _ h rfl⟩

end GlobalTheory.CompFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorComponentsOfAdelicInvariantFunctionStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_components_of_adelic_invariant_function : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∃ v : U.Comp → c.F, ∀ h : GA D V, w h = v (dict h).1 := by
  first | exact @GlobalTheory.CompFactor.exists_factor_comp | exact GlobalTheory.CompFactor.exists_factor_comp | (intros; apply GlobalTheory.CompFactor.exists_factor_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionMulAdelicFunctionLevelCover
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompRat


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem exists_sec_mul_adelic_fun : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → FnAlgClosed (Xo := Xo) (c := c) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio hpq hA hσ hW hL hdom hU hF w hfin hQ hK a n f hf
  classical
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.T.exists_factor_components_of_adelic_invariant_function D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio hpq hA hσ hW hL hdom
    w hfin hQ hK
  have hr1 : 1 ≤ r := hU.1 ▸ hpq
  obtain ⟨χ, hχ, hid, -, -, hrd⟩ := GlobalTheory.T.exists_orthogonal_idempotent_sections_indicating_components D.host.E H Dw l Xo c σ r U hr1 hσ hU hF
  let v : U.Comp → c.F := fun k => if ∃ h : GA D V, (dict h).1 = k then v₀ k else 0
  have hv : ∀ h : GA D V, v (dict h).1 = w h := fun h => by
    simp only [v]
    rw [if_pos ⟨h, rfl⟩, hv₀ h]
  have he : (∑ k, v k • χ k) ∈ sec Xo c 0 0 :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hχ k)
  have hval : ∀ k x, x ∈ (U.X k).dom → rdU U (∑ k, v k • χ k) k x = σ (v k) := by
    intro k x hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single k]
    · rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, (hrd k k x hx).1 rfl, smul_eq_mul, mul_one]
    · intro k' _ hk
      rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, (hrd k' k x hx).2 hk.symm, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hmul : rdU U ((∑ k, v k • χ k) * f) = fun k x => σ (v k) * rdU U f k x := by
    funext k x
    rw [GlobalTheory.rdU_mul_apply D.host.E H Dw l Xo c σ r U]
    by_cases hx : x ∈ (U.X k).dom
    · rw [hval k x hx]
    · rw [rdU_mem_offZero U f k x hx, mul_zero, mul_zero]
  refine ⟨(∑ k, v k • χ k) * f, ?_, fun h => ?_, fun la hla => ?_, fun lam hw hint => ?_⟩
  · have := sec_mul Xo c 0 a 0 n he hf
    simpa only [zero_add] using this
  · rw [hmul, ← hv h]
  · rw [hmul]
    exact (GlobalTheory.CompRat.holSub_compMul D.host.E r U.Comp U.X la (fun k => σ (v k)) (rdU U f)).2 hla
  · have hvi : ∀ k, lam.valuation c.F (v k) ≤ 1 := by
      intro k
      by_cases hk : ∃ h : GA D V, (dict h).1 = k
      · obtain ⟨h, rfl⟩ := hk
        rw [hv h]
        exact hw h
      · simp only [v]
        rw [if_neg hk, map_zero]
        exact zero_le_one
    let ε := (Fintype.equivFin U.Comp).symm
    rw [← ε.sum_comp (fun k => v k • χ k)]
    exact GlobalTheory.T.integralComb_idempotentSections_nonneg_over_place D.host.E H Dw l Xo c lam _ (fun i => χ (ε i)) (fun i => v (ε i))
      (fun i => ⟨hχ _, hid _⟩) (fun i => hvi _) f hint

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionMulAdelicFunctionLevelCoverStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_mul_adelic_function_level_cover : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → FnAlgClosed (Xo := Xo) (c := c) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  first | exact @GlobalTheory.CompRat.exists_sec_mul_adelic_fun | exact GlobalTheory.CompRat.exists_sec_mul_adelic_fun | (intros; apply GlobalTheory.CompRat.exists_sec_mul_adelic_fun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsMulStableWeberValues
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat
open GlobalTheory.FinalJoin

namespace GlobalTheory.CompMul

theorem sec_mul_of_weberIn : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l : Level Q.H) (Xo : Moduli (Q.Dw j) l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK (Q.Dw j) V io → 1 ≤ (Q.Dw j).p + (Q.Dw j).q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → ∀ N : ℕ, 0 < N → l.M' ∣ N → (WeberIn Q.H c.F N ∨ CurveOver Q.H c.F N) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  intro D Q hQ j hj l Xo c σ V r hr U dict io g e F ik φ th x₀ h1 h2 h3 h4 h5 h6 h7 h8 N hN hd hW
  exact GlobalTheory.T.exists_section_mul_adelic_function_level_cover D Q.H (Q.Dw j) l Xo c σ V r hr U dict io g e F ik φ th x₀ h1 h2 h3 h4 h5 h6 h7 h8
    (GlobalTheory.T.geometricallyIrreducible_components_weberValues D Q hQ j hj l Xo c N hN hd hW)

end GlobalTheory.CompMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsMulStableWeberValuesStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat
open GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverSections_mul_stable_weberValues : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l : Level Q.H) (Xo : Moduli (Q.Dw j) l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK (Q.Dw j) V io → 1 ≤ (Q.Dw j).p + (Q.Dw j).q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → ∀ N : ℕ, 0 < N → l.M' ∣ N → (WeberIn Q.H c.F N ∨ CurveOver Q.H c.F N) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  first | exact @GlobalTheory.CompMul.sec_mul_of_weberIn | exact GlobalTheory.CompMul.sec_mul_of_weberIn | (intros; apply GlobalTheory.CompMul.sec_mul_of_weberIn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverComp

theorem forms_mul_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ N : ℕ, 0 < N → C.d.l₂.M ∣ N → (WeberIn T.Q.H C.d.c₂.F N ∨ CurveOver T.Q.H C.d.c₂.F N) → ∀ w : GA D (T.V j σ) → C.d.c₂.F, (∀ h h' : GA D (T.V j σ), finHom (T.V j σ) h = finHom (T.V j σ) h' → w h = w h') → (∀ γ ∈ GQ (T.V j σ), ∀ h, w (γ * h) = w h) → (∀ u : GA D (T.V j σ), gLat (T.V j σ) u = latHat (T.V j σ) → FinCong (T.V j σ) C.d.l₂.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ φ ∈ C.ratForms a n, (fun h => C.σ₂ (w h) * φ h) ∈ C.ratForms a n) ∧ ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), (∀ la ∈ S, ∀ h, la.valuation C.d.c₂.F (w h) ≤ 1) → ∀ φ ∈ C.intForms a n S, (fun h => C.σ₂ (w h) * φ h) ∈ C.intForms a n S := by
  intro D T hL j hj σ hσ C hU N hN hMN hW w hw1 hw2 hw3 a n
  obtain ⟨hlev, hA, hinc, hUnf, hdom, hr, g, e, F, ik, φ, th, hmod, hth, hdict⟩ := hU
  have hpq := (GlobalTheory.Member.exists_iotaOK D T.Q hL.pins j hj).2
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hio := (GlobalTheory.TupleCover.iotaOK_and_frame T hL j hj σ hσ (T.V j σ) rfl hr).1
  have hgood : GoodEmb C.d.c₂ C.σ₂ := by
    have h1 := hσ
    rw [← hinc] at h1
    exact h1
  have hMN' : C.d.l₂.M' ∣ N := by
    simpa [Level.M', hA] using hMN
  have key := GlobalTheory.T.coverSections_mul_stable_weberValues D T.Q hL.pins j hj C.d.l₂ C.d.Xo₂ C.d.c₂ C.σ₂ (T.V j σ) D.R.r hr C.U₂ C.dict₂
    (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) g e F ik φ th (T.x₀ j σ) hio hpos hA hgood hmod hdict hdom
    hUnf N hN hMN' hW w hw1 hw2 hw3 a n
  have hrd : ∀ f f' : Rul C.d.Xo₂ C.d.c₂,
      (∀ h, rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2 = C.σ₂ (w h) * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2) →
      C.rd a f' = fun h => C.σ₂ (w h) * C.rd a f h := by
    intro f f' hff
    funext h
    simp only [Cover.rd, Pi.smul_apply, smul_eq_mul]
    change _ * (_ * rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2) = _ * (_ * (_ * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2))
    rw [hff h]
    ring
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, ⟨hf, hc⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, -⟩ := key f hf
    exact ⟨f', ⟨hf', h2 _ hc⟩, hrd f f' h1⟩
  · rintro S hS _ ⟨f, ⟨⟨hf, hc⟩, hv⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, h3⟩ := key f hf
    exact ⟨f', ⟨⟨hf', h2 _ hc⟩, fun la hla v hvv => h3 la (hS la hla) (hv la hla) v hvv⟩, hrd f f' h1⟩

end GlobalTheory.CoverComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunctionStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_forms_mul_componentFunction : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ N : ℕ, 0 < N → C.d.l₂.M ∣ N → (WeberIn T.Q.H C.d.c₂.F N ∨ CurveOver T.Q.H C.d.c₂.F N) → ∀ w : GA D (T.V j σ) → C.d.c₂.F, (∀ h h' : GA D (T.V j σ), finHom (T.V j σ) h = finHom (T.V j σ) h' → w h = w h') → (∀ γ ∈ GQ (T.V j σ), ∀ h, w (γ * h) = w h) → (∀ u : GA D (T.V j σ), gLat (T.V j σ) u = latHat (T.V j σ) → FinCong (T.V j σ) C.d.l₂.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ φ ∈ C.ratForms a n, (fun h => C.σ₂ (w h) * φ h) ∈ C.ratForms a n) ∧ ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), (∀ la ∈ S, ∀ h, la.valuation C.d.c₂.F (w h) ≤ 1) → ∀ φ ∈ C.intForms a n S, (fun h => C.σ₂ (w h) * φ h) ∈ C.intForms a n S := by
  first | exact @GlobalTheory.CoverComp.forms_mul_comp | exact GlobalTheory.CoverComp.forms_mul_comp | (intros; apply GlobalTheory.CoverComp.forms_mul_comp <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyThetaDataFlagDomainModels
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompNonemptyFiniteGenFrTrdeg
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeve
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPtStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNormalisedFramedPointOnEachComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNormalisedFramedPointOnEachComponent
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem normConst_pos_of_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) :
    0 < normConst ty ξ₀ := by
  unfold normConst
  refine Real.sqrt_pos.mpr (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))
  have := norm_pos_iff.mpr ((map_ne_zero (ty j)).mpr h)
  positivity

theorem exists_isNormUn : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∃ un, IsNormUn T un := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T
  have key : ∀ x : (M.X k).dom, ∃ y : FrPt Xo c (CAt σ), ∃ κ : ℂ,
      κ ^ 2 = (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det ∧
        IsThetaPt T (T.co.symm x.1) κ y := by
    intro x
    have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
      simpa using x.2
    have hne : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (normConst_pos_of_ne_zero _ (M.X k).ξ0_ne).ne')
        (T.norm _ hb).1.ne_zero
    obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq
      ((normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det) (n := 2) two_pos
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      exact hne (by rw [← hκ]; simp)
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_isThetaPt' hS E H Dw l Xo c σ g e F r M k T _ hb κ hκ0
    exact ⟨y, κ, hκ, hy⟩
  choose un hun using key
  exact ⟨un, hun⟩

end GlobalTheory.FrameUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNormalisedFramedPointOnEachComponentStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedFramedPoint_on_each_component : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∃ un, IsNormUn T un := by
  first | exact @GlobalTheory.FrameUnif.exists_isNormUn | exact GlobalTheory.FrameUnif.exists_isNormUn | (intros; apply GlobalTheory.FrameUnif.exists_isNormUn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_framesOK : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∃ un, FramesOK e F M un := by
  intro hB hT E _ _ _ H Dw l Xo c σ g e F r M hσ hM hξ
  have T : ∀ k, ThetaData e F M k := fun k =>
    (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F r M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F r M k (T k)
  exact ⟨un,
    fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F r M k (T k) (un k) hσ hM hξ (hun k),
    fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
    fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
    fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F r M un k (T k) (hun k) a n han f hf⟩

end GlobalTheory.FrameUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnifStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoints_all_normalisations_familyUnif : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∃ un, FramesOK e F M un := by
  first | exact @GlobalTheory.FrameUnif.exists_framesOK | exact GlobalTheory.FrameUnif.exists_framesOK | (intros; apply GlobalTheory.FrameUnif.exists_framesOK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.MarkUniq

lemma nsmul_cancel (F : Type) [Field F] {M : Type} [AddCommGroup M] [Module F M] {N : ℕ} (hN : (N : F) ≠ 0)
    {x y : M} (h : N • x = N • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  exact smul_right_injective _ hN h

lemma sub_eq_nsmul_sub {M : Type} [AddCommGroup M] {N : ℕ} {x y z w w' : M} (h : x - z = N • w) (h' : y - z = N • w') :
    x - y = N • (w - w') := by
  rw [smul_sub, ← h, ← h']; abel

lemma exists_of_finVec_eq_nsmul {D : D7} (V : HSp D) (g : GA D V) (N : ℕ) (hN : N ≠ 0)
    (u : Fin V.rank → D.host.E) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ latGHat V g)
    (h : finVec V u = N • w) : ∃ x ∈ latG V g, u = N • x := by
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V g
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hu : u = N • ((N : D.host.E)⁻¹ • u) := by
    rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
  refine ⟨(N : D.host.E)⁻¹ • u, ?_, hu⟩
  refine ((GlobalTheory.T.adelicCompletion_rational_points_and_approximation D.host.F D.host.E V.rank (latG V g) h1 h2).1 _).1 ?_
  have e : N • finVec V ((N : D.host.E)⁻¹ • u) = N • w := by
    rw [← h]
    conv_rhs => rw [hu]
    funext i
    simp only [finVec, Pi.smul_apply]
    exact (map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) N _).symm
  have e' := nsmul_cancel D.host.F hNF e
  rw [h5, ← e'] at hw
  exact hw

lemma finVec_sub {D : D7} (V : HSp D) (u v : Fin V.rank → D.host.E) :
    finVec V (u - v) = finVec V u - finVec V v := by
  funext i
  simp only [finVec, Pi.sub_apply, TensorProduct.tmul_sub]

lemma half_surj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : Level H) {A B : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (t : A →ₗ[𝓞 E] B) (ht : ∀ b, ∃ a e, b = t a + l.M • e) (b : B)
    (hb : b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) B)) :
    ∃ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) A), ∃ e, b = t a + l.M • e := by
  obtain ⟨a, e, hae⟩ := ht b
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have h2 : x • b ∈ Ideal.span {(l.M : 𝓞 E)} • (⊤ : Submodule (𝓞 E) B) := by
    rw [← l.prod, mul_smul]
    exact Submodule.smul_mem_smul hx hb
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨e', -, he'⟩ := h2
  refine ⟨y • a, Submodule.smul_mem_smul hy trivial, e' + y • e, ?_⟩
  rw [Nat.cast_smul_eq_nsmul] at he'
  have : b = x • b + y • b := by rw [← add_smul, hxy, one_smul]
  rw [this, ← he', map_smul, smul_add, smul_comm l.M y e]
  conv_lhs => rw [hae]
  rw [smul_add]
  abel

lemma matched {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} (C : Ctx Xo c σ V V.rank) (h : GA D V) (k k' : Fin C.F.n)
    (γ γ' : GA D V) (hm : C.Mark h k γ) (hm' : C.Mark h k' γ') :
    ∃ δ : GL (Fin V.rank) D.host.E, IsRat V (γ' * γ⁻¹) δ ∧
      (∀ v, v ∈ (C.M.X k).Λ ↔ (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ (C.M.X k').Λ) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ (C.M.X k').Λ,
          (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) =
            (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E) + l.M • w := by
  obtain ⟨r1, -, -, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨hγ, hΛ, hk⟩ := hm
  obtain ⟨hγ', hΛ', hk'⟩ := hm'
  obtain ⟨δ, hδ⟩ := (r1 _).1 ((GQ V).mul_mem hγ' ((GQ V).inv_mem hγ))
  obtain ⟨m1, m2⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 _ δ (γ * h) hδ
  have hg : γ' * γ⁻¹ * (γ * h) = γ' * h := by group
  rw [hg] at m1 m2
  have hL : (C.M.X k).Λ = latG V (γ * h) := SetLike.ext' (hΛ.trans (Set.image_id _))
  have hL' : (C.M.X k').Λ = latG V (γ' * h) := SetLike.ext' (hΛ'.trans (Set.image_id _))
  refine ⟨δ, hδ, fun v => by rw [hL, hL']; exact m1 v, fun a ha => ?_⟩
  obtain ⟨w, hw, e⟩ := hk a ha
  obtain ⟨w', hw', e'⟩ := hk' a ha
  change finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _ at e
  change finVec V (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E) - _ = _ at e'
  have e2 := congrArg (fun z => (finHom V (γ' * γ⁻¹)).1 *ᵥ z) e
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
  rw [(r5 _ δ hδ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hg] at e2
  obtain ⟨x, hx, hx'⟩ := exists_of_finVec_eq_nsmul V (γ' * h) l.M (by have := l.three_le; omega)
    ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) -
      (C.M.φ k' (C.F.t k' a) : Fin V.rank → D.host.E)) ((finHom V (γ' * γ⁻¹)).1 *ᵥ w - w')
    (sub_mem ((m2 w).1 hw) hw') ((finVec_sub V _ _).trans (sub_eq_nsmul_sub e2 e'))
  exact ⟨x, hL' ▸ hx, by rw [← hx']; abel⟩

theorem mark_unique : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h, (∀ k k' γ γ', C.Mark h k γ → C.Mark h k' γ' → k = k') ∧ ∀ k γ γ', C.Mark h k γ → C.Mark h k γ' → ∃ δ ∈ (C.M.X k).Γ, C.fr (γ' * h) k = lact δ (C.fr (γ * h) k) := by
  intro D H Dw l Xo c σ V r C hC h
  obtain rfl : V.rank = r := C.hr
  obtain ⟨-, r2, -, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  have hG : ∀ k, (C.M.X k).Gm = -V.gramᵀ := fun k => (hC.modelW k).1
  refine ⟨fun k k' γ γ' hm hm' => ?_, fun k γ γ' hm hm' => ?_⟩
  · obtain ⟨δ, hδ, hΛ, hmk⟩ := matched C h k k' γ γ' hm hm'
    refine GlobalTheory.ClassUniq.eq_of_matched GlobalTheory.T.thetaUniformisation_complexAbelianVariety GlobalTheory.firstFiveLaws.1 _ H Dw l Xo _ C.g _ C.F _ C.M k k' δ
      hC.pos hC.good ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat _ H l c σ hC.good).2.2.2 Dw C.g C.e) hC.base
      ((hG k').trans (hG k).symm) ((hC.modelW k').2.trans (hC.modelW k).2.symm)
      (by rw [hG k]; exact r2 _ δ hδ) hΛ hmk (fun a => ?_)
    refine ⟨_ - _, sub_mem ((hΛ _).1 (C.M.φ k (C.F.t k a)).2) (C.M.φ k' (C.F.t k' a)).2, ?_⟩
    rw [hC.lA, one_smul]; abel
  · obtain ⟨δ, hδ, hΛ, hmk⟩ := matched C h k k γ γ' hm hm'
    have hφ : ∀ w ∈ (C.M.X k).Λ, ∃ b, (C.M.φ k b : Fin V.rank → D.host.E) = w := fun w hw =>
      ⟨(C.M.φ k).symm ⟨w, hw⟩, by rw [LinearEquiv.apply_symm_apply]⟩
    refine ⟨δ, (hC.base.gam k δ).2 ⟨⟨by rw [hG k]; exact r2 _ δ hδ, hΛ⟩, fun b hb => ?_, fun a => ?_⟩, ?_⟩
    · have hM : l.M' = l.M := by rw [Level.M', hC.lA, Nat.lcm_one_right]
      obtain ⟨a, ha, e, rfl⟩ := half_surj l (C.F.t k) (fun b => hM ▸ C.F.t_surj k b) b hb
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      obtain ⟨b', hb'⟩ := hφ _ (sub_mem (add_mem hw ((hΛ _).1 (C.M.φ k e).2)) (C.M.φ k e).2)
      refine ⟨b', ?_⟩
      rw [hb', map_add (f := _), map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul, Matrix.mulVec_add,
        Matrix.mulVec_smul, hw', smul_sub, smul_add]
      abel
    · obtain ⟨b', hb'⟩ := hφ _ (sub_mem ((hΛ _).1 (C.M.φ k a).2) (C.M.φ k a).2)
      refine ⟨b', ?_⟩
      rw [hb', hC.lA, one_smul]; abel
    · funext τ
      have hg : γ' * h = γ' * γ⁻¹ * (γ * h) := by group
      have e := ((GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf).1 τ.1).2.1 (γ' * γ⁻¹) (γ * h)
      rw [← hg, (r5 _ δ hδ).2 τ.1 _ (hC.inf τ.1)] at e
      change archM V (C.θ τ.1) (γ' * h) * C.x₀ τ.1 =
        (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 * (archM V (C.θ τ.1) (γ * h) * C.x₀ τ.1)
      rw [e, Matrix.mul_assoc]

end GlobalTheory.MarkUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroupStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h, (∀ k k' γ γ', C.Mark h k γ → C.Mark h k' γ' → k = k') ∧ ∀ k γ γ', C.Mark h k γ → C.Mark h k γ' → ∃ δ ∈ (C.M.X k).Γ, C.fr (γ' * h) k = lact δ (C.fr (γ * h) k) := by
  first | exact @GlobalTheory.MarkUniq.mark_unique | exact GlobalTheory.MarkUniq.mark_unique | (intros; apply GlobalTheory.MarkUniq.mark_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem onto_dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem onto_adelic_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L Λ : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hLs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hΛ : Λ.FG) (hΛs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    {A B : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (ι : A ≃ₗ[𝓞 E] L) (φ : B ≃ₗ[𝓞 E] Λ) (EA : A → A → ℤ) (EB : B → B → ℤ) (f : ℕ → A →ₗ[𝓞 E] B)
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ξ : E) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hJ : ∀ z : E, z ∈ J ↔ ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (ξ * (a * z)) = m)
    (hA : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) =
      -(EA x y : ℚ))
    (hB : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (φ x : Fin n → E) a * G a b * c ((φ y : Fin n → E) b)) =
      -(EB x y : ℚ))
    (h1 : ∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ e, f (N * m) a = f N a + N • e)
    (h2 : ∀ N : ℕ, 0 < N → (∀ a, (∃ e, f N a = N • e) ↔ ∃ e, a = N • e) ∧ ∀ a', ∃ a e, a' = f N a + N • e)
    (h3 : ∀ N : ℕ, 0 < N → ∀ a a', (N : ℤ) ∣ EB (f N a) (f N a') - EA a a') :
    ∃ g : GL (Fin n) (GlobalTheory.AdLat.RA F E),
      (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) =
        GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ∧
      (∀ N : ℕ, 0 < N → ∀ a : A, ∃ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
        (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ GlobalTheory.AdLat.fv F (ι a : Fin n → E) =
          GlobalTheory.AdLat.fv F (φ (f N a) : Fin n → E) + N • w) ∧
      ∀ x y, GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ y) = GlobalTheory.AdLat.hermA c G x y := by
  let f' : ℕ → (L →ₗ[𝓞 E] Λ) := fun N => φ.toLinearMap ∘ₗ f N ∘ₗ ι.symm.toLinearMap
  have hf' : ∀ N a, f' N (ι a) = φ (f N a) := fun N a => by simp [f']
  have hlin : ∀ (s : 𝓞 E) (x y : Fin n → E), (s : E) * ∑ a, ∑ b, x a * G a b * c (y b) =
      ∑ a, ∑ b, (s • x) a * G a b * c (y b) := by
    intro s x y
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change _ = ((s : E) * x a) * _ * _
    ring
  obtain ⟨g, hg1, hg2, hg3⟩ := GlobalTheory.AdLat.exists_adelic_matrix_of_tower F E n L Λ f' hL hLs hΛ hΛs
    (fun N m hN hm a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      obtain ⟨e, he⟩ := h1 N m hN hm a
      exact ⟨φ e, by rw [hf', hf', he, map_add (f := _), map_nsmul]⟩)
    (fun N hN => ⟨fun a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      rw [hf']
      constructor
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).1 ⟨φ.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨ι e, by rw [he, map_nsmul]⟩
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).2 ⟨ι.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨φ e, by rw [he, map_nsmul]⟩, fun a' => by
      obtain ⟨a', rfl⟩ := φ.surjective a'
      obtain ⟨a, e, he⟩ := (h2 N hN).2 a'
      exact ⟨ι a, φ e, by rw [hf', he, map_add (f := _), map_nsmul]⟩⟩)
  refine ⟨g, hg1, fun N hN a => by rw [← hf']; exact hg2 N hN (ι a), hg3 c G J ?_ ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx'⟩ := φ.surjective ⟨x, hx⟩
    obtain ⟨y', hy'⟩ := φ.surjective ⟨y, hy⟩
    rw [hJ]
    intro s
    refine ⟨-EB (s • x') y', ?_⟩
    rw [hlin, Int.cast_neg, ← hB, map_smul, hx', hy']
    rfl
  · intro N hN x y
    obtain ⟨x, rfl⟩ := ι.surjective x
    obtain ⟨y, rfl⟩ := ι.surjective y
    have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [hf', hf']
    refine ⟨(N : E)⁻¹ * ((∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) -
      ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)), ?_, ?_⟩
    · rw [hJ]
      intro s
      obtain ⟨m, hm⟩ := h3 N hN (s • x) y
      refine ⟨-m, ?_⟩
      have e1 := hA (s • x) y
      have e2 := hB (f N (s • x)) (f N y)
      rw [map_smul, Submodule.coe_smul, ← hlin] at e1
      rw [show (φ (f N (s • x)) : Fin n → E) = s • (φ (f N x) : Fin n → E) by
        rw [map_smul, map_smul, Submodule.coe_smul], ← hlin] at e2
      have hm' : (EB (f N (s • x)) (f N y) : ℚ) - EA (s • x) y = N * m := by exact_mod_cast hm
      generalize (∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) = u at e2 ⊢
      generalize (∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) = v at e1 ⊢
      have e3 : ξ * ((s : E) * ((N : E)⁻¹ * (u - v))) = (N : ℚ)⁻¹ • (ξ * (s * u) - ξ * (s * v)) := by
        rw [Algebra.smul_def, map_inv₀, map_natCast]; ring
      rw [e3, map_smul, map_sub, e1, e2, smul_eq_mul]
      push_cast
      field_simp
      linear_combination -hm'
    · rw [nsmul_eq_mul, mul_inv_cancel_left₀ hN0, add_sub_cancel]

theorem onto_marking_sub (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n N : ℕ}
    {u v e : Fin n → E} {z w : Fin n → GlobalTheory.AdLat.RA F E} (h : u = v + N • e)
    (hz : z = GlobalTheory.AdLat.fv F u + N • w) : GlobalTheory.AdLat.fv F v - z = N • -(GlobalTheory.AdLat.fv F e + w) := by
  rw [hz, h, GlobalTheory.AdLat.cap_fv_add, GlobalTheory.AdLat.cap_fv_nsmul, smul_neg, smul_add]
  abel

theorem exists_finite_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ k, ∃ h ∈ GfC V, C.Mark h k 1 := by
  intro D H Dw l Xo c σ V r C hC k
  obtain rfl : V.rank = r := C.hr
  have hneg := (GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding D H Dw l Xo c σ V _ rfl C.ι hC.iota hC.pos hC.lA hC.good).2.1 C hC
  obtain ⟨Pf, -, -, hPf, -⟩ := GlobalTheory.exists_framePeriods D.host.E H Dw l Xo c σ C.g C.e C.F _ C.M hC.good hC.base hneg k
  obtain ⟨x, hx⟩ := onto_dom_nonempty (C.M.X k)
  obtain ⟨f, h1, h2, h3, h4⟩ := GlobalTheory.familyUnif_lattice_genus D.host.E H Dw l Xo _ C.g _ C.F k (Pf x) (hPf x hx)
  obtain ⟨-, hfv, -, -, -, hcc, -, -, -, hT, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hL, hLs, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  let ι : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective C.ι hC.iota.emb.1).trans (LinearEquiv.ofEq _ _ hC.iota.emb.2)
  have hι : ∀ a, (ι a : Fin V.rank → D.host.E) = C.ι a := fun a => rfl
  have hherm : ∀ x y : Fin V.rank → D.host.E, (∑ a, ∑ b, x a * V.gramᵀ a b * cF D (y b)) = -herm (-V.gramᵀ) x y := by
    intro x y
    simp only [herm, hcc, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hGm : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
  have hxi : (C.M.X k).ξ0 = -D.host.xi0 := (hC.modelW k).2
  obtain ⟨g, hg1, hg2, hg3⟩ := onto_adelic_of_tower D.host.F D.host.E V.rank (latG V 1) (C.M.X k).Λ hL hLs
    (C.M.X k).Λ_fg (C.M.X k).Λ_span ι (C.M.φ k) (fun a b => Dw.EF a b) (fun a b => (C.F.Di k).EF a b) f
    (cF D) V.gramᵀ D.host.xi0 _ (GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl).1
    (fun x y => by
      have halt : Dw.EF y x = -Dw.EF x y := by
        have := Dw.alt (x + y)
        simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at this
        linear_combination this
      rw [hherm, hι, hι, ← hT, ← hC.iota.isom, halt, Int.cast_neg])
    (fun x y => by
      rw [hherm, hC.base.ef k x y, hGm, hxi, neg_neg, mul_neg, map_neg])
    h1 h2 h3
  obtain ⟨h, hh, rfl⟩ := (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.2.2.1 g hg3
  obtain ⟨-, -, hlat, hhat, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V h
  have hcap := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (C.M.X k).Λ (C.M.X k).Λ_fg
    (C.M.X k).Λ_span).1
  rw [hg1] at hhat
  refine ⟨h, hh, one_mem _, ?_, fun a ha => ?_⟩
  · rw [one_mul, hlat]
    ext v
    rw [SetLike.mem_coe, ← hcap, ← SetLike.mem_coe, ← hg1]
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  · rw [one_mul]
    obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hw'⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    refine ⟨-(GlobalTheory.AdLat.fv D.host.F (C.M.φ k e : Fin V.rank → D.host.E) + w), ?_, ?_⟩
    · have h0 := (hcap _).2 (C.M.φ k e).2
      have h5 := AddSubgroup.neg_mem _ (AddSubgroup.add_mem _ h0 hw)
      rw [← SetLike.mem_coe, ← hhat] at h5
      exact h5
    · rw [hfv, hfv, ← hι]
      change GlobalTheory.AdLat.fv D.host.F (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _
      have he' : (C.M.φ k (f l.M a) : Fin V.rank → D.host.E) =
          (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) + l.M • (C.M.φ k e : Fin V.rank → D.host.E) := by
        rw [he, (C.M.φ k).map_add, map_nsmul (C.M.φ k)]
        rfl
      exact onto_marking_sub D.host.F he' hw'

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponentStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelic_element_marking_component : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ k, ∃ h ∈ GfC V, C.Mark h k 1 := by
  first | exact @GlobalTheory.Member.exists_finite_mark | exact GlobalTheory.Member.exists_finite_mark | (intros; apply GlobalTheory.Member.exists_finite_mark <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections
noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GeometricValues

theorem eq_zero_of_forall_algClosed {K R : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] (x : R)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (φ : R →ₐ[K] Ω), φ x = 0) : x = 0 := by
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let φ : R →ₐ[K] AlgebraicClosure (FractionRing (R ⧸ J)) :=
    (IsScalarTower.toAlgHom K (FractionRing (R ⧸ J)) (AlgebraicClosure (FractionRing (R ⧸ J)))).comp
      ((IsScalarTower.toAlgHom K (R ⧸ J) (FractionRing (R ⧸ J))).comp (Ideal.Quotient.mkₐ K J))
  have h0 := h _ φ
  have h1 : algebraMap (R ⧸ J) (FractionRing (R ⧸ J)) (Ideal.Quotient.mk J x) = 0 := by
    apply (algebraMap (FractionRing (R ⧸ J)) (AlgebraicClosure (FractionRing (R ⧸ J)))).injective
    rw [map_zero]
    exact h0
  have h2 : Ideal.Quotient.mk J x = 0 := by
    apply IsFractionRing.injective (R ⧸ J) (FractionRing (R ⧸ J))
    rw [map_zero]
    exact h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem ptsDetect_of {K : Type} [Field K] {ι : Type} [Fintype ι]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
    (hW : EvalWD pts mapR)
    (hB : ∀ (S : Type) [CommRing S] [Algebra K S] (T : Type) [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
      (y : pts S), ∃ z : pts T, mapR φ y z)
    (e : ι → ℕ) : PtsDetect pts mapR borR e := by
  intro g hg h
  funext p y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  refine eq_zero_of_forall_algClosed (K := K) (g p y) ?_
  intro Ω _ _ _ φ
  obtain ⟨z, hz⟩ := hB p.R Ω φ y
  have hT : FromTest pts mapR z := ⟨p, φ, y, hz⟩
  have h0 := h Ω z
  unfold evalAt at h0
  rw [dite_eq_left hT] at h0
  rw [← h0]
  exact hW g hg.1 Ω p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec

end GeometricValues

theorem ptsDetect_framed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n) := by
  intro E _ _ _ H Dw l Xo c a n
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  exact GeometricValues.ptsDetect_of (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (fun t y y' => FrBor t y y') (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c S T φ y) (ex Dw a n)

end GlobalTheory.Frames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffCurveOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveField

open GlobalTheory.Ex.UnifModel GlobalTheory.Ex.TorsionField

theorem exists_finset_fixed (hM : Out.MulNSt) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (P : Out.PolAV (Sp M)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset ℂ, (∀ z ∈ s, IsIntegral ℚ z) ∧ ∀ τ : ℂ →+* ℂ, (∀ x ∈ M, τ x = x) → (∀ z ∈ s, τ z = z) →
      ∀ x : Over.mk (spMap (algebraMap M ℂ)) ⟶ P.A, x ^ n = 1 → spMap τ ≫ x.left = x.left := by
  classical
  let F := algebraicClosure M ℂ
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure M ℂ).isAlgClosed
  obtain ⟨s, hs⟩ := exists_finset (F := F) hM P hn
  refine ⟨s.image Subtype.val, fun z hz => ?_, fun τ h₁ h₂ x hx => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact isIntegral_trans (A := M) _ (mem_algebraicClosure_iff'.1 y.2)
  · let k : Subfield F := RingHom.eqLocusField (τ.comp (algebraMap F ℂ)) (algebraMap F ℂ)
    obtain ⟨y, hy, hy'⟩ := exists_descend_algClosed hM P (algebraMap M F) (algebraMap F ℂ) (algebraMap M ℂ)
      (fun _ => rfl) hn x hx
    obtain ⟨z, hz⟩ := hs k k.subtype (fun c => ⟨⟨algebraMap M F c, h₁ c c.2⟩, rfl⟩)
      (fun c hc => ⟨⟨c, h₂ c (Finset.mem_image_of_mem _ hc)⟩, rfl⟩) y hy
    have e₁ : spMap (algebraMap F ℂ) ≫ spMap k.subtype = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun _ => rfl
    have e₂ : spMap τ ≫ spMap ((algebraMap F ℂ).comp k.subtype) = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun c => c.2
    rw [← hy', ← hz, reassoc_of% e₁, reassoc_of% e₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_wC_eq (H : Host E) (a : ℤ × ℤ) :
    ∃ m k : ℤ, wC H a = (m : ℂ) + k * ((1 + Complex.I * Real.sqrt H.d) / 2) := by
  have h : H.rt0 ^ 2 = (Complex.I * Real.sqrt H.d) ^ 2 := by
    rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨a.1, a.2, by rw [wC, h]⟩
  · exact ⟨a.1 + a.2, -a.2, by rw [wC, h]; push_cast; ring⟩

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) :
    u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_pow_eq_one (C : Curve H) {n : ℕ} (hn : 0 < n) (a : ℤ × ℤ) :
    (C.u.ex fun _ => C.c * (wC H a / n)) ^ n = 1 := by
  obtain ⟨m, k, h⟩ := exists_wC_eq H a
  rw [← ex_nsmul, C.u.ker]
  refine (C.lat _).2 ⟨m, k, funext fun _ => ?_⟩
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [← h, Pi.smul_apply, nsmul_eq_mul]
  field_simp

theorem exists_model (H : Host E) : ∃ (M : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ M)
    (P : Out.PolAV (Sp M)) (C : Curve H) (ψ : C.P.A.left ⟶ P.A.left),
    IsGrpPullback C.P.A P.A (spMap (algebraMap M ℂ)) ψ := by
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, -, ⟨P₀, π, -, -, ⟨hg₀, hπ, hL₀⟩, -⟩, hcm, -⟩ :=
    cmCurve_closed H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := exists_baseChange firstFiveLaws.1.polBaseChange (spMap (algebraMap M ℂ)) P₀
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all PC
  have hL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (pull_isLB P₀.isLB ψ) (pull_isLB P.isLB _) hLC
      (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀.symm)
  obtain ⟨c, hc, hΛ⟩ := hcm PC (ψ ≫ π)
    ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp fun _ => rfl) rfl, hL.symm⟩ u
  rw [hw] at hΛ
  exact ⟨M, inferInstance, P₀, ⟨PC, hgC.trans (hg₀.trans hg), u, hu, c, hc, hΛ⟩, ψ, hψ⟩

theorem exists_curveOver (H : Host E) {n : ℕ} (hn : 0 < n) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ CurveOver H F n := by
  obtain ⟨M, _, P, C, ψ, hψ⟩ := exists_model H
  obtain ⟨s, hs, hfix⟩ := exists_finset_fixed firstFiveLaws.1.mulN M P hn
  have := IntermediateField.finiteDimensional_adjoin (K := ℚ) (S := (s : Set ℂ)) hs
  refine ⟨M ⊔ IntermediateField.adjoin ℚ (s : Set ℂ), inferInstance, fun τ hτ => ?_⟩
  have h₁ : ∀ x ∈ M, (τ : ℂ →+* ℂ) x = x := fun x hx => hτ x (le_sup_left (a := M) hx)
  have h₂ : ∀ z ∈ s, (τ : ℂ →+* ℂ) z = z := fun z hz =>
    hτ z (le_sup_right (a := M) (IntermediateField.subset_adjoin ℚ _ hz))
  have e : spMap (τ : ℂ →+* ℂ) ≫ spMap (algebraMap M ℂ) = spMap (algebraMap M ℂ) :=
    spMap_comp fun c => h₁ c c.2
  have w : ψ ≫ P.A.hom = (C.P.A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap (algebraMap M ℂ) := by
    rw [Category.assoc, e, hψ.1.w]
  refine ⟨C, hψ.1.lift _ _ w, hψ.cancel (hψ.congr e.symm (hψ.1.lift_fst _ _ w).symm) (hψ.1.lift_snd _ _ w),
    fun a => ?_⟩
  have h1 : wC H (1, 0) = 1 := by simp [wC]
  rw [h1, _root_.one_mul]
  obtain ⟨ε, hε⟩ := exists_mulEquiv_of_isGrpPullback hψ (𝟙 (Sp ℂ)) (spMap (algebraMap M ℂ)) (Category.id_comp _).symm
  have hx := hfix τ h₁ h₂ (ε (C.u.ex fun _ => C.c * (wC H a / n))) (by
    rw [← map_pow]
    exact (congrArg ε (ex_pow_eq_one C hn a)).trans (map_one ε))
  rw [hε] at hx
  have ho : C.pt (wC H a / n) ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * (wC H a / n))
  refine hψ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hψ.1.lift_fst, Category.assoc]
    exact hx.symm
  · rw [Category.assoc, hψ.1.lift_snd, Category.assoc, ho, reassoc_of% ho, Category.comp_id]

theorem exists_coeff_curveOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (n : ℕ), 0 < n → ∃ c' : Coeff l, c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → CurveOver H c''.F n := by
  intro E _ _ _ H l c n hn
  obtain ⟨F, _, hF⟩ := exists_curveOver H hn
  have := c.fin
  exact ⟨⟨c.F ⊔ F, inferInstance, fun τ a => le_sup_left (b := F) (c.conj τ a), le_sup_left (b := F) c.zeta_mem,
    c.le.trans le_sup_left⟩, le_sup_left, fun c'' h τ hτ => hF τ fun x hx => hτ x (h (le_sup_right (a := c.F) hx))⟩

end GlobalTheory.CurveField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.MultiplierNorm

def InOrder (d : ℕ) (z : ℂ) : Prop := ∃ m n : ℤ, z = (m : ℂ) + n * ((1 + Complex.I * Real.sqrt d) / 2)

theorem exists_form_eq_one {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hg : 1 ≤ g)
    (u : HolUnif A L g) (Ef : LinearMap.BilinForm ℤ u.Λ) (hE : Function.Bijective Ef) :
    ∃ a b : u.Λ, Ef a b = 1 := by
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : Module.Free ℤ u.Λ := ZLattice.module_free ℝ u.Λ
  have hnt : Nontrivial u.Λ := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have hb : u.Λ = ⊥ := Submodule.eq_bot_of_subsingleton
    have := u.full
    rw [hb] at this
    simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at this
    haveI hne : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
    exact bot_ne_top this
  let B := Module.Free.chooseBasis ℤ u.Λ
  obtain ⟨i⟩ := B.index_nonempty
  obtain ⟨a, ha⟩ := hE.2 (B.coord i)
  exact ⟨a, B i, by rw [ha]; simp⟩

theorem ex_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ) (z : Fin g → ℂ) :
    u.ex z ^ n = u.ex ((n : ℂ) • z) := by
  have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [pow_succ, ih, ← u.ex_add]; congr 1; push_cast; rw [add_smul, one_smul]

theorem hermForm_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : ℂ) (v : Fin g → ℂ) :
    hermForm Hm (a • v) (b • v) = a * starRingEnd ℂ b * hermForm Hm v v := by
  rw [hermForm, hermForm, smul_dotProduct, star_smul, Matrix.mulVec_smul, dotProduct_smul, RCLike.star_def,
    smul_eq_mul, smul_eq_mul, _root_.mul_assoc]

theorem hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (v : Fin g → ℂ) :
    (hermForm Hm v v).im = 0 := by
  rw [← Complex.conj_eq_iff_im, hermForm, ← RCLike.star_def, ← Matrix.star_dotProduct_star,
    Matrix.star_mulVec, star_star, h.eq, ← Matrix.dotProduct_mulVec]

theorem weilIs_of_quadLattice (P Q : Out.PolAV (Sp ℂ)) (hP : P.g = 1) (hQ : Q.g = 1) (u : HolUnif P.A P.L P.g)
    {d : ℕ} (hd : 0 < d) {c : ℂ} (hc : c ≠ 0) (hΛ : IsQuadLattice u.Λ d c) (f : P.A ⟶ Q.A) (hf : IsMonHom f)
    (hinj : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x ≫ f = 1 → x = 1) {α β : ℂ} (hα : InOrder d α) (hβ : InOrder d β)
    {e : ℤ} (he : (e : ℝ) * (√d / 2) = (α * starRingEnd ℂ β).im) {n : ℕ} (hn : 0 < n) (ζ : ℂˣ)
    (hζ : (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (e : ℂ) / n)) :
    Out.WeilIs Q.A Q.L n (u.ex (fun _ => c * (α / n)) ≫ f) (u.ex (fun _ => c * (β / n)) ≫ f) (unitOn ζ) := by
  obtain ⟨rig, hr⟩ := Q.rigid
  obtain ⟨u₁, Hm, χ, Ef, hAH, -, -, -, -, -, hIm, hE, hw⟩ := thetaUnifAV_all Q rig hr
  obtain ⟨F, hF⟩ := exists_linear_lift_of_isMonHom_polAV P Q _ _ u u₁ f hf
  have hd' : (0 : ℝ) < √d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  let i₀ : Fin P.g := ⟨0, by omega⟩
  let v : Fin Q.g → ℂ := F fun _ => c
  have hv : ∀ z : ℂ, z • v = F fun _ => c * z := fun z => by
    rw [← map_smul]; congr 1; funext _; simp [_root_.mul_comm]
  have mem : ∀ z : ℂ, z • v ∈ u₁.Λ ↔ InOrder d z := fun z => by
    rw [← u₁.ker, hv, hF]
    constructor
    · intro h
      obtain ⟨m, k, h'⟩ := (hΛ _).1 ((u.ker _).1 (hinj _ h))
      exact ⟨m, k, mul_left_cancel₀ hc (congrFun h' i₀)⟩
    · rintro ⟨m, k, rfl⟩
      rw [(u.ker _).2 ((hΛ _).2 ⟨m, k, rfl⟩), MonObj.one_comp]
  have v0 : v ≠ 0 := fun h => by
    obtain ⟨m, k, h'⟩ := (mem (1 / 2)).1 (by rw [h, smul_zero]; exact u₁.Λ.zero_mem)
    have h1 := congrArg Complex.im h'
    have h2 := congrArg Complex.re h'
    simp at h1 h2
    have hk : k = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hd.ne'
    subst hk
    have h3 : ((2 * m : ℤ) : ℝ) = (1 : ℤ) := by push_cast at h2 ⊢; linarith
    have := Int.cast_injective h3
    omega
  have span : ∀ l : Fin Q.g → ℂ, ∃ z : ℂ, l = z • v := fun l => by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 v0
    refine ⟨l j / v j, funext fun i => ?_⟩
    have : i = j := Fin.ext (by omega)
    subst this
    simp only [Pi.zero_apply] at hj
    simp [hj]
  have hpos : 0 < (hermForm Hm v v).re := hAH.2.1 v v0
  have val : ∀ (a b : ℂ) (ha : a • v ∈ u₁.Λ) (hb : b • v ∈ u₁.Λ),
      (Ef ⟨_, ha⟩ ⟨_, hb⟩ : ℝ) = (a * starRingEnd ℂ b).im * (hermForm Hm v v).re := fun a b ha hb => by
    rw [hIm, hermForm_smul, Complex.mul_im, hermForm_self_im hAH.1, mul_zero, zero_add]
  have one : √d / 2 * (hermForm Hm v v).re = 1 := by
    have ha₀ := (mem _).2 ⟨0, 1, rfl⟩
    have hb₀ := (mem _).2 ⟨1, 0, rfl⟩
    have h₀ : (Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ : ℝ) = √d / 2 * (hermForm Hm v v).re := by
      rw [val]; simp
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_form_eq_one hQ.ge u₁ Ef hE
    obtain ⟨a, rfl⟩ := span a
    obtain ⟨b, rfl⟩ := span b
    obtain ⟨m, k, rfl⟩ := (mem a).1 ha
    obtain ⟨m', k', rfl⟩ := (mem b).1 hb
    have hdvd : Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ ∣ 1 := by
      refine ⟨k * m' - m * k', Int.cast_injective (α := ℝ) ?_⟩
      rw [Int.cast_mul, h₀, ← hab, val]
      simp [map_ofNat]
      ring
    have hp : 0 < Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ := by
      have : (0 : ℝ) < Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ := by rw [h₀]; positivity
      exact_mod_cast this
    rw [← h₀, Int.eq_one_of_dvd_one hp.le hdvd, Int.cast_one]
  have hEe : Ef ⟨_, (mem _).2 hα⟩ ⟨_, (mem _).2 hβ⟩ = e := Int.cast_injective (α := ℝ) (by
    rw [val, ← he, _root_.mul_assoc, one, _root_.mul_one])
  have H := hw n ⟨_, (mem _).2 hα⟩ ⟨_, (mem _).2 hβ⟩ ζ hn (by rw [hEe, hζ])
  have sc : ∀ a : ℂ, u₁.ex ((n : ℂ)⁻¹ • a • v) = u.ex (fun _ => c * (a / n)) ≫ f := fun a => by
    rw [smul_smul, hv, hF, ← div_eq_inv_mul]
  rw [← sc, ← sc]
  exact H

def pullPol {R R' : Type} [CommRing R] [CommRing R'] (P : Out.PolAV (Sp R)) {s : R →+* R'} {A : Over (Sp R')}
    [GrpObj A] {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A (spMap s) φ) : Out.PolAV (Sp R') :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmHost_rootComplex_eq_pm_sqrt (H : Host E) : H.rt0 = Complex.I * Real.sqrt H.d ∨ H.rt0 = -(Complex.I * Real.sqrt H.d) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp

theorem inOrder_wC (H : Host E) (a : ℤ × ℤ) : InOrder H.d (wC H a) := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨a.1, a.2, by rw [wC, h]⟩
  · exact ⟨a.1 + a.2, -a.2, by rw [wC, h]; push_cast; ring⟩

theorem four_mul_div (H : Host E) : (4 : ℂ) * ((((H.d : ℤ) + 1) / 4 : ℤ) : ℂ) = H.d + 1 := by
  have := H.d_mod
  have h : (4 : ℤ) * (((H.d : ℤ) + 1) / 4) = H.d + 1 := by omega
  exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h

theorem wC_mul (H : Host E) (s a : ℤ × ℤ) : ∃ b, wC H s * wC H a = wC H b := by
  refine ⟨(s.1 * a.1 - s.2 * a.2 * (((H.d : ℤ) + 1) / 4), s.1 * a.2 + s.2 * a.1 + s.2 * a.2), ?_⟩
  have h := four_mul_div H
  have h' := H.sqrt_neg_disc_sq
  simp only [wC, Int.cast_sub, Int.cast_mul, Int.cast_add]
  linear_combination (s.2 * a.2 / 4 : ℂ) * h + (s.2 * a.2 / 4 : ℂ) * h'

theorem wC_norm (H : Host E) (s : ℤ × ℤ) : wC H s * starRingEnd ℂ (wC H s) =
    ((s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) : ℤ) : ℂ) := by
  have hc : starRingEnd ℂ H.rt0 = -H.rt0 := by
    rcases cmHost_rootComplex_eq_pm_sqrt H with h | h <;> rw [h] <;> simp
  have h := four_mul_div H
  have h' := H.sqrt_neg_disc_sq
  simp only [wC, Int.cast_pow, Int.cast_mul, Int.cast_add, map_add (f := _), map_mul, map_div₀, map_intCast, map_one,
    map_ofNat, hc]
  linear_combination (-s.2 ^ 2 / 4 : ℂ) * h - (s.2 ^ 2 / 4 : ℂ) * h'

theorem exists_pair (H : Host E) :
    ∃ a b, ((-1 : ℤ) : ℝ) * (√H.d / 2) = (wC H a * starRingEnd ℂ (wC H b)).im := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨(1, 0), (0, 1), by simp [wC, h, map_ofNat]; ring⟩
  · exact ⟨(0, 1), (1, 0), by simp [wC, h]; ring⟩

theorem map_zeta_eq_zpow_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (io : C.P.A.left ⟶ C.P.A.left) (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → τ (zeta n) = zeta n ^ (s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4)) := by
  intro E _ _ _ H C τ _ io n s hn ⟨hp, hact⟩
  have hL := firstFiveLaws.1
  have hd := H.d_prime.pos
  obtain ⟨a, b, hab⟩ := exists_pair H
  set N : ℤ := s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) with hN
  let Q := pullPol C.P hp
  let ζ : ℂˣ := Units.mk0 (zeta n) (Complex.exp_ne_zero _)
  have hs : ∀ a, InOrder H.d (wC H s * wC H a) := fun a => by
    obtain ⟨b, hb⟩ := wC_mul H s a
    rw [hb]; exact inOrder_wC H b
  have W₀ := weilIs_of_quadLattice C.P C.P C.g_eq C.g_eq C.u hd C.c_ne C.lat (𝟙 _) inferInstance
    (fun x hx => by rwa [Category.comp_id] at hx) (inOrder_wC H a) (inOrder_wC H b) hab hn ζ
    (by simp [ζ, zeta])
  have W₁ := weilIs_of_quadLattice C.P Q C.g_eq C.g_eq C.u hd C.c_ne C.lat (𝟙 C.P.A)
    (inferInstanceAs (IsMonHom (𝟙 C.P.A)))
    (fun x hx => (Category.comp_id x).symm.trans hx) (hs a) (hs b) (e := -N) (by
      have e : wC H s * wC H a * starRingEnd ℂ (wC H s * wC H b) = (N : ℝ) * (wC H a * starRingEnd ℂ (wC H b)) := by
        rw [Complex.ofReal_intCast, hN, ← wC_norm, map_mul]; ring
      rw [e, Complex.im_ofReal_mul, ← hab]
      push_cast; ring) hn (ζ ^ N) (by
      rw [Units.val_zpow_eq_zpow_val]
      show zeta n ^ N = _
      rw [zeta, ← Complex.exp_int_mul]
      congr 1
      push_cast; ring)
  rw [Category.comp_id, Category.comp_id] at W₀
  have tor : ∀ z, InOrder H.d z → (C.u.ex fun _ => C.c * (z / n)) ^ n = 1 := by
    rintro z ⟨m, k, hz⟩
    rw [ex_pow, C.u.ker]
    refine (C.lat _).2 ⟨m, k, funext fun _ => ?_⟩
    have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [← hz, Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨r, hr, ⟨cub⟩⟩ := PolAV_exists_cubical hL.cube Q
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl Q.isLB
  have := Q.isAb.comm
  have W₂ := WeilCube.weilIs_pull cub hL.globalFns Q.isAb C.P.isLB hp w hw (T := 𝟙_ _) (T₀ := 𝟙_ _)
    (spMap (τ : ℂ →+* ℂ)) (by simp) (tor _ (hs a)) (tor _ (hs b)) (hact a).symm (hact b).symm W₀
  obtain ⟨c₀, -, hc₀⟩ := (hL.weil _ Q n _).1 _ _ (tor _ (hs a)) (tor _ (hs b))
  have W₁' : Out.WeilIs Q.A Q.L n (C.u.ex fun _ => C.c * (wC H s * wC H a / n))
      (C.u.ex fun _ => C.c * (wC H s * wC H b / n)) (unitOn (ζ ^ N)) := by
    have e₁ : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ C.P.A, x ≫ 𝟙 C.P.A = x := fun x => Category.comp_id x
    erw [e₁, e₁] at W₁
    exact W₁
  have e := (hc₀ _ W₂).trans (hc₀ _ W₁').symm
  have e' : unitOn (Units.map (τ : ℂ →+* ℂ).toMonoidHom ζ) = unitOn (ζ ^ N) := by
    refine Eq.trans (Units.ext ?_) e
    exact congrArg (fun q => q.hom (ζ : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : ℂ →+* ℂ)))
  have e'' := congrArg Units.val (H1.unitOn_injective e')
  rw [Units.val_zpow_eq_zpow_val] at e''
  exact e''

end GlobalTheory.MultiplierNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicCharacter_eq_cmMultiplier_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (io : C.P.A.left ⟶ C.P.A.left) (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → τ (zeta n) = zeta n ^ (s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4)) := by
  first | exact @GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm | exact GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm | (intros; apply GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm <;> assumption)
end
end

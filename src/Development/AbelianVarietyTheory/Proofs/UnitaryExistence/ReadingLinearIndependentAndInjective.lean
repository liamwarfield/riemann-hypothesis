module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 200000 in
theorem reading_linearIndependent_and_injective : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c a n) → LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU U (b i))) ∧ ∀ f ∈ sec Xo c a n, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → f = 0 := by
  intro hS E _ _ _ H Dw l Xo c σ r U hU a n
  have h : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ),
      ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n,
        cvalR σ (ψ (f p y)) = u * rdU U f k x.1 :=
    fun p y ψ => GlobalTheory.T.test_point_value_eq_const_mul_reading hS E H Dw l Xo c σ r U hU a n p y ψ
  have : CharZero c.F := RingHom.charZero σ
  refine ⟨fun m b hb hli => ?_, fun f hf h0 => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro w hw
    have hθ : ∀ θ : Module.Dual c.F (CAt σ), ∀ i, θ (toCAt σ (w i)) = 0 := by
      intro θ
      have hz : ∑ i, θ (toCAt σ (w i)) • b i = 0 := by
        funext p y
        have hpt := descend_cpts σ p (fun i => b i p y) w (fun ψ => by
          obtain ⟨k', x, u, hk⟩ := h p y ψ
          have e1 : ∀ i, w i * cvalR σ (ψ (b i p y)) = u * (w i * rdU U (b i) k' x.1) := by
            intro i; rw [hk (b i) (hb i)]; ring
          have e2 := congrFun (congrFun hw k') x.1
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2
          simp_rw [e1]
          rw [← Finset.mul_sum, e2, mul_zero]) θ
        simpa [Finset.sum_apply] using hpt
      exact fun i => Fintype.linearIndependent_iff.1 hli _ hz i
    intro i
    exact (Module.forall_dual_apply_eq_zero_iff c.F (toCAt σ (w i))).1 fun θ => hθ θ i
  · funext p y
    show f p y = 0
    refine eq_zero_of_cpts σ p _ fun ψ => ?_
    obtain ⟨k, x, u, hk⟩ := h p y ψ
    have e := hk f hf
    rw [h0 k x.1 x.2, mul_zero] at e
    exact e

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjectiveStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rdU_linearIndependent_and_injective : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c a n) → LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU U (b i))) ∧ ∀ f ∈ sec Xo c a n, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → f = 0 := by
  first | exact @GlobalTheory.reading_linearIndependent_and_injective | exact GlobalTheory.reading_linearIndependent_and_injective | (intros; apply GlobalTheory.reading_linearIndependent_and_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem hostCMType_neg_constant_im_neg (D : D7) (τ : D.host.E →+* ℂ)
    (hτ : τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD) : (τ (-D.host.xi0)).im < 0 := by
  have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
    rw [hφ]
    have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
    simpa using hd
  rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
  rw [map_neg, Complex.neg_im]
  linarith

theorem exists_family_models (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hσ : GoodEmb c σ) :
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (M : GlobalTheory.FrameUnif.ModelsOf F V.rank), GlobalTheory.FrameUnif.ModelBase M ∧ ∀ k, ModelW V rfl (M.X k) := by
  classical
  let e := (Fintype.equivFin (Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))).symm
  have hty := (GlobalTheory.Relab.relab_good D.host.E H l c σ hσ).2.2.2 Dw _ e
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws D.host.E H Dw l Xo
    (σ.comp (IntermediateField.inclusion c.le).toRingHom) _ (fun j => relab c σ (e j).1) hpos hσ hty
  obtain ⟨-, -, -, -, -, hcF, -, hherm, hdet, hhT, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by rw [cc, map_neg, conj_xi0_alt]
  have hsp : Submodule.span D.host.E (Set.range ι) = ⊤ := by
    rw [← LinearMap.coe_range, hι.emb.2]
    exact (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.1
  have hG : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a := fun a b => by
    rw [Matrix.neg_apply, Matrix.neg_apply, cc, map_neg, ← hherm a b, hcF, cc]
  have hd : (-V.gramᵀ).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) hdet
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := fun x y => by
    have h1 : Dw.EF x y = -Dw.EF y x := by
      have h := Dw.alt (x + y)
      simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at h
      linarith
    rw [h1, Int.cast_neg, hι.isom y x, hhT, ← map_neg]
    congr 1
    ring
  obtain ⟨M, hM, -, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ _ _ F
    V.rank (-D.host.xi0) (-V.gramᵀ) ι hξ
    (fun τ hτ => hostCMType_neg_constant_im_neg D τ (by rw [← hι.rt0, ← hι.rt, hτ])) ⟨hι.emb.1, hsp, hG, hd, hEF⟩
  exact ⟨_, e, F, M, hM, fun k => ⟨(hMG k).1, (hMG k).2⟩⟩

theorem exists_ctx : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V ι → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι) ∧ (∀ C : Ctx Xo c σ V r, C.OK → GlobalTheory.FrameUnif.NegXi C.M) ∧ ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → ∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := by
  intro D H Dw l Xo c σ V r hr ι hι hpos hA hσ
  subst hr
  obtain ⟨g, e, F, M, hM, hW⟩ := exists_family_models D H Dw l Xo c σ V ι hι hpos hσ
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have key : ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
        gram τ (-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram)ᵀ) (x₀ τ) =
          Matrix.diagonal fun a : Fin V.rank => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) →
      ∃ C : Ctx Xo c σ V V.rank, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := fun x₀ hx =>
    ⟨⟨rfl, g, e, F, M, ι, θ, x₀⟩, ⟨hι, hpos, hA, hσ, hM, hW, hθ, fun k τ hτ => by
      show gram τ (M.X k).Gm (x₀ τ) = Matrix.diagonal fun a : Fin V.rank => ((sgn (M.X k).p0 (a : ℕ) : ℝ) : ℂ)
      rw [(hW k).1, (hM.type k).1]
      exact hx τ (((hM.type k).2 τ).1 hτ)⟩, rfl, rfl⟩
  refine ⟨?_, fun C hC k τ hτ => ?_, key⟩
  · classical
    let k : Fin F.n := ⟨0, F.n_pos⟩
    obtain ⟨C, hC, h, -⟩ := key
      (fun τ => if h : τ ∈ (M.X k).Ψ then ((M.X k).signature ⟨τ, h⟩).choose else 1) fun τ hτ => by
        have h := ((hM.type k).2 τ).2 hτ
        rw [dite_eq_left h, ← (hW k).1, ← (hM.type k).1]
        exact ((M.X k).signature ⟨τ, h⟩).choose_spec.2
    exact ⟨C, hC, h⟩
  · rw [(hC.modelW k).2]
    exact hostCMType_neg_constant_im_neg D τ (by rw [← hι.rt0, ← hι.rt, ((hC.base.type k).2 τ).1 hτ])

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbeddingStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V ι → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι) ∧ (∀ C : Ctx Xo c σ V r, C.OK → GlobalTheory.FrameUnif.NegXi C.M) ∧ ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → ∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := by
  first | exact @GlobalTheory.Member.exists_ctx | exact GlobalTheory.Member.exists_ctx | (intros; apply GlobalTheory.Member.exists_ctx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordOfIsPullDegId
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SameCoord

set_option maxHeartbeats 1600000 in
theorem psiCoord_of_isPullDeg_id {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D' : DegPre R}
    (hD : IsPullDeg (RingHom.id R) D D') (x : D'.X) (r : R) (hr : PsiCoord D (hD.xe x) r) :
    ∃ u : Rˣ, PsiCoord D' x (u * r) := by
  obtain ⟨j, hj, h, hr⟩ := hr
  have hs := specOf_id R
  set Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) with hΦ
  have hc : (D'.c x).left ≫ Φ = (D.c (hD.xe x)).left := by
    rw [hΦ, hD.c_pr x]
    exact (congrArg (· ≫ (D.c (hD.xe x)).left) hs).trans (Category.id_comp _)
  obtain ⟨q, hq⟩ := exists_chart D'.P.isLB ((D'.c x).left (closedPoint R))
  have hq' : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D'.c x).left ⁻¹ᵁ D'.P.L.U q :=
    ((IsLocalRing.closedPoint_mem_iff _).1 hq).ge
  have hp : ∀ y : Spec (CommRingCat.of R), Φ ((D'.c x).left y) ∈ D.P.L.U (j PUnit.unit) := fun y =>
    (congrArg (fun g => g y ∈ D.P.L.U (j PUnit.unit)) hc).mpr (hj trivial)
  have hV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      (D'.c x).left ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => j PUnit.unit) ⊓ D'.P.L.U q) := fun y _ =>
    ⟨mem_pull.2 (hp y), hq' trivial⟩
  let u₀ : Γ(Spec (CommRingCat.of R), ⊤)ˣ := res hV (pullU (D'.c x).left _ (hD.w.s (fun _ => j PUnit.unit, q)))
  let u : Rˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom u₀
  have hu : DegPre.toOpen (R := R) ⊤ u = u₀.val := by
    show ((Spec (CommRingCat.of R)).presheaf.map (𝟙 _)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u₀.val)) = _
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (fun g => g.hom u₀.val) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
  have h' : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D'.P.L (K := PUnit) (fun _ => D'.xK x) (fun _ => -1)).U (fun _ => q) :=
    fun z _ => Set.mem_iInter.2 fun _ => hq' (x := jK R z) trivial
  refine ⟨u, fun _ => q, hq', h', ?_⟩
  apply TopCat.Presheaf.section_ext (TK R).left.sheaf
  intro z hz
  have hF : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
    simp
  have hFz : jFK (R := R) (FractionRing R) z = z := by rw [hF]; rfl
  have m₁ : Φ (D'.xK x (jFK (R := R) (FractionRing R) z)) ∈ D.P.L.U (j PUnit.unit) := by
    rw [hFz]; exact hp (jK R z)
  have m₂ : D'.xK x (jFK (R := R) (FractionRing R) z) ∈ D'.P.L.U q := by
    rw [hFz]; exact hq' (x := jK R z) trivial
  have m₃ : D.xK (hD.xe x) (jFK (R := R) (FractionRing R) z) ∈ D.P.L.U (j PUnit.unit) := by
    rw [hFz]; exact hj (x := jK R z) trivial
  have pm := pmaps_psi hD (FractionRing R) (by
    have : spMap (RingHom.id R) = 𝟙 _ := hs
    rw [this, Category.comp_id]) x _ (𝟙 _) z j (fun _ => q) (fun _ => m₁) (fun _ => m₂)
  rw [Category.comp_id, Fintype.prod_unique] at pm
  have pm' := (gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe x)) _ (D.psi (hD.xe x)) (jFK (R := R) (FractionRing R)) (𝟙 _) z j
    (Set.mem_iInter.2 fun _ => m₃)).symm.trans (pm.trans (congrArg (_ * ·)
      (gm_pullGen D'.P.L (fun _ : PUnit => D'.xK x) _ (D'.psi x) (jFK (R := R) (FractionRing R)) (𝟙 _) z (fun _ => q)
    (Set.mem_iInter.2 fun _ => m₂))))
  rw [hF, Category.comp_id, Category.id_comp, Category.id_comp, zpow_neg_one, eq_inv_mul_iff_mul_eq] at pm'
  have a₁ : gm (jK R) z ⊤ u₀ = gw hD.w (D'.xK x) z (j PUnit.unit) q :=
    (gm_res (jK R) z hV trivial _).trans (gm_pull (jK R) (D'.c x).left z _ (hV (x := jK R z) trivial) _)
  have a₂ := gm_res (𝟙 (TK R).left) z h hz ((D.psi (hD.xe x)).s j)
  have a₃ := gm_res (𝟙 (TK R).left) z h' hz ((D'.psi x).s (fun _ => q))
  have k := congrArg Units.val ((congrArg₂ (fun a b : ((TK R).left.presheaf.stalk z)ˣ => a * b) a₁ a₂).trans (pm'.trans a₃.symm))
  rw [Units.val_mul, gm_val (jK R) z ⊤ trivial, gm_val _ z _ hz, gm_val _ z _ hz] at k
  rw [map_mul, map_mul, hu, hr]
  exact (map_mul _ _ _).trans k

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

set_option maxHeartbeats 1600000 in
theorem exists_move (hU : UnifBaseChangeSt) (h5 : Laws5) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : AdmBase R I) {t t' : SAB H (Sp R)} (m : SABMap t' t (𝟙 _)) (P : PELUnif I t) :
    ∃ (P' : PELUnif I t') (hD : IsPullDeg (RingHom.id R) P.D.toPre P'.D.toPre),
      ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback t'.G t.G (specOf (RingHom.id R)) m.φ := m.cart.congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback t.G (specOf (RingHom.id R)))
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := by
    have := P.U.gen_hom
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (jK R)).obj t'.G) t.G (jK R)
      (pullback.fst t'.G.hom (jK R) ≫ m.φ) :=
    ((isGrpPullback_pullback t'.G (jK R)).comp m.cart).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (P.A.L.pull eA.hom.left) (P.U.LG.L.pull (pullback.fst t'.G.hom (jK R) ≫ bc.hom.left ≫
      pullback.fst t.G.hom (specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ P.U.gen.inv.left)
      (chartPullSame P.A.L (fun _ => eA.hom.left) (fun _ => P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame P.U.LG.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr P.bundle m.cm m.lin hbc
    (e := specOf (RingHom.id R)) (hs.trans m.base.symm)
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR P.D
  have hgen : (specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI P.D P.A t.G t.semi P.U
    Wo hψW hgen t'.G bc mbc P.A rfl eA mE wA t'.PP wL' he' gL rL
  have a₃ : ∀ x, (t'.act.act x).left ≫ m.φ = m.φ ≫ (t.act.act x).left := m.act
  have hbcact : ∀ x, t'.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (t.act.act x)).left ≫
          pullback.fst t.G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (t'.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc, a₃]
    · exact (Over.w (t'.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.act x))).symm
  have actA : ∀ x, (P.oA.act x).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (jK R)).map (t'.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (jK R)).map (t'.act.act x)).left ≫ pullback.fst t'.G.hom (jK R) =
          pullback.fst t'.G.hom (jK R) ≫ (t'.act.act x).left := pullback.lift_fst _ _ _
      show ((Over.pullback (jK R)).map (t'.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, -, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) P.D P.A t.G P.U
    t'.G bc mbc P.A D'' hD U'' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct hbcact
    P.oA extA
  exact ⟨{ D := D'', mod := mod'', oD := oD'', A := P.A, oA := P.oA, U := U'', bundle := hLG, lin := lin''
           w0 := w0'' H.w0 P.w0 }, hD, xl⟩

theorem exists_equiv_psiCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (t t' : SAB H (Sp R)) (_ : SABMap t' t (𝟙 _)) (U : PELUnif (maximalIdeal R) t) (U' : PELUnif (maximalIdeal R) t'), IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (maximalIdeal R) R → ∃ e : U.D.toPre.X ≃ₗ[𝓞 E] U'.D.toPre.X, ∀ χ r, PsiCoord U.D.toPre χ r → ∃ u : Rˣ, PsiCoord U'.D.toPre (e χ) (u * r) := by
  intro E _ _ _ H R _ _ _ _ t t' m U U' hN hC hA
  letI := H.starRing
  have hR : AdmBase R (maximalIdeal R) := ⟨hN, inferInstance, hC, hA⟩
  obtain ⟨-, -, -, h4, h5, h6⟩ := GlobalTheory.allSixLaws
  obtain ⟨P, hD₁, xl₁⟩ := exists_move h4.unifBaseChange h5 hR m U
  obtain ⟨wL, g₀, m₀⟩ := exists_iso_of_eq (U'.bundle.trans P.bundle.symm)
  obtain ⟨hD₂, -, holin⟩ := h6.unifUniq R _ hR P.D U'.D P.A U'.A t'.G t'.semi P.U U'.U wL g₀ m₀
  obtain ⟨xl₂, -⟩ := holin (𝓞 E) P.oD U'.oD P.oA U'.oA t'.act.toRingAct P.lin U'.lin
  let e₁ : P.D.toPre.X ≃ₗ[𝓞 E] U.D.toPre.X := { hD₁.xe with map_smul' := xl₁ }
  let e₂ : U'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD₂.xe with map_smul' := xl₂ }
  refine ⟨e₁.symm.trans e₂.symm, fun χ r hr => ?_⟩
  have k₁ : hD₁.xe (e₁.symm χ) = χ := e₁.apply_symm_apply χ
  have k₂ : hD₂.xe (e₂.symm (e₁.symm χ)) = e₁.symm χ := e₂.apply_symm_apply _
  obtain ⟨u₁, hu₁⟩ := psiCoord_of_isPullDeg_id hD₁ (e₁.symm χ) r (by rw [k₁]; exact hr)
  obtain ⟨u₂, hu₂⟩ := psiCoord_of_isPullDeg_id hD₂ (e₂.symm (e₁.symm χ)) _ (by rw [k₂]; exact hu₁)
  exact ⟨u₂ * u₁, by rw [Units.val_mul, mul_assoc]; exact hu₂⟩

end GlobalTheory.SameCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

private theorem nonempty_irreducibleComponents_of_point {X : Type*} [TopologicalSpace X] (x : X) :
    Nonempty (irreducibleComponents X) :=
  ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩

theorem _root_.GlobalTheory.Reg.evLaws_genFr_nonempty_comp : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Reg.EvLaws Xo c ∧ _root_.Formalism.L2.Pj.IntDiagUnit Xo c ∧ _root_.Formalism.L2.Pj.GenFrEx Xo c ∧
      (1 ≤ Dw.p + Dw.q → Nonempty (_root_.Formalism.L2.Pj.Comp Xo c)) := by
  intro E _ _ _ H Dw l Xo c
  have hsec : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := _root_.GlobalTheory.allSixLaws.1.secBaseChange
  have htw : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := _root_.GlobalTheory.allSixLaws.2.1.secTwist
  obtain ⟨-, -, hwd, hwt, hdiag, -, -⟩ :=
    _root_.GlobalTheory.Frames.algebraic_laws hsec E H Dw l Xo c
  refine ⟨⟨hwd, _root_.GlobalTheory.Frames.allTest_of_secBaseChange hsec E H Dw l Xo c, hwt, ?_⟩, hdiag,
    _root_.Formalism.L2.Pj.genFrEx_of htw, ?_⟩
  · intro S T _ _ _ _ φ y
    exact _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hsec E H Dw l Xo c S T φ y
  · intro hpq
    obtain ⟨x⟩ := (_root_.GlobalTheory.PeriodExists.typeFn_period_exist E H Dw).2.2
      _root_.GlobalTheory.closing_of_abelianSchemeLaws hpq l Xo c
    unfold _root_.Formalism.L2.Pj.Comp
    exact nonempty_irreducibleComponents_of_point x

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValueBelow
section -- merged from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.FromTestIffOfValAtCx
section -- merged from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ChosenEqOfAllRules
noncomputable section

namespace GlobalTheory.SupNormExample

open Formalism.L2.Pj

variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

def conjAt (σ : K →+* ℂ) : CAt σ →ₐ[K] CAt ((starRingEnd ℂ).comp σ) :=
  { (starRingEnd ℂ : ℂ →+* ℂ) with commutes' := fun _ => rfl }

end GlobalTheory.SupNormExample
end
end

noncomputable section

namespace GlobalTheory.SupLawProbe

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev FT {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

theorem evR_map (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT1 : FT y₁) (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) :
    evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  have hT2 : FT y₂ := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y₁ y₂ hy' hm⟩
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact hWD f hf K₂ _ _ _ _ _ _ y₂ hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y₁ y₂ hT1.choose_spec.choose_spec.choose_spec hm)

variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

section Conj

variable (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
  (σ : c.F →+* ℂ) (cj : FrPt Xo c (CAt σ) → FrPt Xo c (CAt ((starRingEnd ℂ).comp σ)))
  (hcj : ∀ y, FrMap (SupNormExample.conjAt σ) y (cj y))
  (htr : ∀ y i, |fn _ (cj y) i| = |fn σ y i|) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
  (hS : f ∈ sec Xo c a n)

end Conj

end GlobalTheory.SupLawProbe
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FrameLift
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClassSumCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem exists_frUnder {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) (y₂ : FrPt d.Xo₂ d.c₂ S)
    (hx : (y₂.x ≫ d.r) ≫ Xo.s = sOf c S) : ∃ y : FrPt Xo c S, FrOver d y₂ y := by
  have hc' : ∀ τ a, algebraMap d.c₂.F S (embK d.c₂ τ a) = algebraMap c.F S (embK c τ a) := fun τ a => by
    rw [← embK_eF, hc]
  have e : y₂.x ≫ d.r = y₂.x ≫ d.r := rfl
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s, hs⟩ := exists_up hL hL₂ hw p₁ hk hk' y₂.s
  refine ⟨⟨y₂.x ≫ d.r, hx, fun τ i => y₂.u τ i ≫ d.m.φ, fun τ i => (tan_iff d.m e (y₂.tan τ i).1).1 (y₂.tan τ i),
    fun τ i => (eig_iff d.m τ (hc' τ) (y₂.tan τ i).1).1 (y₂.eig τ i), fun τ v hv hv' => ?_, s, fun s' => ?_⟩,
    (frOver_iff d _ _).2 ⟨e, fun _ _ => rfl, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  · obtain ⟨v₂, rfl, h₂⟩ := exists_lift d.m e hv.1
    refine (existsUnique_congr fun a => ?_).1
      (y₂.basis τ v₂ ((tan_iff d.m e h₂).2 hv) ((eig_iff d.m τ (hc' τ) h₂).2 hv'))
    exact comb_iff d.m e (fun i => (y₂.tan τ i).1) a h₂
  · obtain ⟨s₂', hs'⟩ := exists_down hL hL₂ hw p₁ s'
    refine (existsUnique_congr fun a => ?_).1 (y₂.gen s₂')
    exact (scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans
      ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans
        (scal_iff (fst (Over.mk (y₂.x ≫ d.r)) Xo.univ.t.G).left (toΓ S a) s s').symm)

theorem rel_unique {A A₂ Y Y₂ : Scheme.{0}} {L : LB A} {L₂ : LB A₂} {φ : A₂ ⟶ A} (hL₂ : L₂.IsLB)
    {w : LB.Iso L₂ (L.pull φ)} {q₂ : Y₂ ⟶ A₂} {q : Y ⟶ A} {p : Y₂ ⟶ Y} (hp : p ≫ q = q₂ ≫ φ) {k : Y ⟶ Y₂}
    (hk : k ≫ p = 𝟙 _) {s₂ : LB.Sec (LOne L₂ q₂)} {s s' : LB.Sec (LOne L q)} (H : Rel w p s₂ s)
    (H' : Rel w p s₂ s') : s = s' := by
  have : s.f = s'.f := funext fun i => by
    obtain ⟨i, rfl⟩ := exists_const i
    refine fn_ext fun z hz => ?_
    obtain ⟨j, hj⟩ := exists_chart hL₂ (q₂ (k z))
    have hi' : φ (q₂ (k z)) ∈ L.U i :=
      (congrArg (· ∈ L.U i) (pt_eq hp (k z))).mp ((congrArg (fun t => q t ∈ L.U i) (pt_eq hk z)).mpr (mem_ch.1 hz))
    have a := (H Y k z i j hi' hj).trans (H' Y k z i j hi' hj).symm
    rw [hk] at a
    exact a
  cases s; cases s'
  congr

theorem frUnder_unique {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] {y₂ : FrPt d.Xo₂ d.c₂ S}
    {y z : FrPt Xo c S} (h : FrOver d y₂ y) (h' : FrOver d y₂ z) : y = z := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, H⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', H'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns (UnivPol.pol d.Xo₂)
    Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _ hw.2 hw'.2
  obtain ⟨x, xo, u, t, ei, b, s, g⟩ := y
  obtain ⟨x', xo', u', t', ei', b', s', g'⟩ := z
  dsimp only at e e' hu hu' p p' p₁ p₂ p₁' p₂' H H'
  obtain rfl : x = x' := e.symm.trans e'
  obtain rfl : u = u' := funext fun τ => funext fun i => (hu τ i).symm.trans (hu' τ i)
  obtain rfl : p = p' := pm_ext (p₁.trans p₁'.symm) (p₂.trans p₂'.symm)
  obtain ⟨q, k, q₁, q₂, hk, -⟩ := exists_pm_iso d.m e
  obtain rfl : p = q := pm_ext (p₁.trans q₁.symm) (p₂.trans q₂.symm)
  obtain rfl : s = s' := rel_unique d.Xo₂.univ.t.PP.isLB p₁ hk H H'
  rfl

end GlobalTheory.ClassSumCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRule
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRule
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.NormUnBor

theorem diag_ne_zero {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.det ≠ 0)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (j : Fin g) : A j j ≠ 0 := by
  have hdet : A.det = ∏ i, A i i := by
    rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin g))]
    · simp
    · intro s _ hs
      by_contra hne
      have hp : ∏ i, A (s i) i ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
      have hall : ∀ i, A (s i) i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hp i (Finset.mem_univ i)
      have hsum : ∑ i, ((e (s i)).2 : ℕ) = ∑ i, ((e i).2 : ℕ) :=
        Equiv.sum_comp s (fun i => ((e i).2 : ℕ))
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => (htri _ _ (hall i)).2)).1 hsum
      apply hs
      ext i
      have h1 := (htri _ _ (hall i)).1
      have h2 := heq i (Finset.mem_univ i)
      have : e (s i) = e i := Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
      simp [e.injective this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdet] at hA
  exact Finset.prod_ne_zero_iff.1 hA j (Finset.mem_univ j)

theorem col_eq_sum {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (τ : T) (i : Fin (m τ)) :
    ∑ i' : Fin (m τ), A (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i'⟩) (1 : ℂ) : Fin g → ℂ) =
      A *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 := by
  funext p
  obtain ⟨⟨τ', i'⟩, rfl⟩ := e.symm.surjective p
  rw [Matrix.mulVec_single_one, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  by_cases hτ : τ' = τ
  · subst hτ
    rw [Finset.sum_eq_single i']
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      exact hj (sigma_mk_injective (β := fun τ => Fin (m τ)) (e.symm.injective h)).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h0 : A (e.symm ⟨τ', i'⟩) (e.symm ⟨τ, i⟩) = 0 := by
      by_contra hne
      have := (htri _ _ hne).1
      rw [e.apply_symm_apply, e.apply_symm_apply] at this
      exact hτ this
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    exact hτ (congrArg Sigma.fst (e.symm.injective h))

theorem normConst_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) :
    (normConst ty ξ₀ : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (div_pos (by positivity) ?_)).ne'
  exact Finset.prod_pos fun j _ => mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero _).2 h))

theorem normUn_bor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hG hB hN hU x b hb h
  obtain ⟨h₀, hdet, hP, htri, -, -, hw⟩ :=
    GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k T.Pf T.per x.1 x.2 b hb
  obtain ⟨κ, hκ, hy⟩ := hU x
  obtain ⟨κ', hκ', hy'⟩ := hU ⟨_, h⟩
  have hx : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using x.2
  have hx' : T.co.symm (rmul x.1 b) ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using h
  obtain ⟨hxx, hder, t₀, hsec, ht₀⟩ := GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap hS E H Dw l Xo c σ g e F r M k T _ hx _ hx' κ κ' _ _
    (LinearEquiv.refl _ _) h₀ hy hy'
    ⟨fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩⟩
    (fun a => by
      simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.refl_apply]
      exact hP a)
  have hsq : toC (t₀ : CAt σ) ^ 2 * h₀.det = 1 := by
    have hc := normConst_ne_zero (fun j => relab c σ (e j).1) (M.X k).ξ0_ne
    have h1 := (T.norm _ hx).1.ne_zero
    have h2 := (T.norm _ hx').1.ne_zero
    rw [hκ, hκ'] at ht₀
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hc h1) h2)
    linear_combination ht₀
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := diag_ne_zero e h₀⁻¹ hinv htri
  let d : Fin g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (e.symm p))
  refine ⟨t, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [e.apply_symm_apply, e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy.1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k _ (T.isPer _ hx) _ _ _ (hy.2.1 τ) _ _).2 ?_
    rw [col_eq_sum e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hsec
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n hD
    rw [← hw un a n (toC (t₀ : CAt σ)) hD.2 hsq]
    show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) = _
    rw [Fintype.prod_option, mul_comm]
    congr 1
    rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (e.symm (e j)) (e.symm (e j)) ^ a ((e j).1, (e j).2) = _
    rw [e.symm_apply_apply]

end GlobalTheory.NormUnBor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRuleStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU laU IsUnf ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b := by
  first | exact @GlobalTheory.NormUnBor.normUn_bor | exact GlobalTheory.NormUnBor.normUn_bor | (intros; apply GlobalTheory.NormUnBor.normUn_bor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.WeightZeroValue

open GlobalTheory.Frames GlobalTheory.NonDominant Polynomial

theorem poly_const (P Q : ℂ[X]) (h : ∀ c : ℂ, c ≠ 0 → P.eval c = Q.eval c⁻¹) (s : ℂ) : P.eval s = P.eval 0 := by
  have h0 : P - C (Q.coeff 0) = 0 := by
    refine poly_eq_zero _ Q.divX 1 one_pos 1 fun c hc => ?_
    have e := congrArg (eval c⁻¹) (Polynomial.X_mul_divX_add Q)
    rw [eval_add, eval_mul, eval_X, eval_C] at e
    rw [eval_sub, eval_C, h c hc, ← e]
    field_simp
    ring
  rw [sub_eq_zero.1 h0, eval_C, eval_C]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def Keeps (σ : c.F →+* ℂ) (f : Rul Xo c) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) : Prop :=
  ∀ y y' : FrPt Xo c (CAt σ), FrChg (S := CAt σ) g 1 y y' → evR Xo c f y' = evR Xo c f y

theorem Keeps.mul {f : Rul Xo c} {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ}
    (hg : Keeps σ f g) (hg' : Keeps σ f g') (hu : ∀ τ, IsUnit (g τ).det) (hu' : ∀ τ, IsUnit (g' τ).det) :
    Keeps σ f fun τ => g τ * g' τ := fun y y' h => by
  obtain ⟨y₁, h₁, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) y g' 1 hu'
  obtain ⟨y₂, h₂, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) y₁ g 1 hu
  have h₃ := (frChg_refl_and_comp E H Dw l Xo c _ y y₁ y₂).2 _ _ _ _ h₁ h₂
  rw [Units.val_one, _root_.mul_one] at h₃
  have e : y₂ = y' := (existsUnique_frChg E H Dw l Xo c (CAt σ) y (fun τ => (g τ * g' τ : Matrix _ _ ℂ)) 1
    (fun τ => show IsUnit (g τ * g' τ).det by rw [Matrix.det_mul]; exact (hu τ).mul (hu' τ))).unique h₃ h
  rw [← e, hg _ _ h₂, hg' _ _ h₁]

theorem evR_bor {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {t : Ix Dw → (CAt σ)ˣ} {y y' : FrPt Xo c (CAt σ)}
    (h : FrBor t y y') : evR Xo c f y' = evR Xo c f y := by
  have e : ex Dw 0 0 = 0 := funext fun i => by cases i <;> rfl
  rw [evR_weight hf h, e]
  simp [wchar]

theorem keeps_lower {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ} (h0 : ∀ τ i j, i < j → g τ i j = 0)
    (hd : ∀ τ i, g τ i i ≠ 0) : Keeps σ f g := fun y y' h => by
  let t : Ix Dw → ℂˣ := fun i => match i with
    | none => 1
    | some p => Units.mk0 _ (hd p.1 p.2)
  exact evR_bor (t := t) hf (((frBor_calculus E H Dw l Xo c _ y y' y').1 t).2 ⟨g, h0, fun _ _ => rfl, h⟩)

open Classical in
def only {R : Type} [CommRing R] (τ : E →+* ℂ) (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) :
    ∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) R := Function.update (fun _ => 1) τ M

section Only

variable {R : Type} [CommRing R] {τ : E →+* ℂ}

theorem only_self (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) : only τ M τ = M := by simp [only]

theorem only_of_ne (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) {ρ : E →+* ℂ} (h : ρ ≠ τ) :
    only τ M ρ = 1 := by
  unfold only
  exact @Function.update_of_ne _ _ (fun a b => Classical.propDecidable (a = b)) _ _ h _ _

theorem only_det {M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R} (hM : IsUnit M.det) (ρ : E →+* ℂ) :
    IsUnit (only τ M ρ).det := by
  by_cases h : ρ = τ
  · subst h; rwa [only_self]
  · simp [only_of_ne _ h]

theorem only_mul (M N : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) :
    (fun ρ => only τ M ρ * only τ N ρ) = only τ (M * N) := funext fun ρ => by
  by_cases h : ρ = τ
  · subst h; simp [only_self]
  · simp [only_of_ne _ h]

theorem only_map (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R[X]) (s : R) :
    (fun ρ => (only τ M ρ).map (eval s)) = only τ (M.map (eval s)) := funext fun ρ => by
  by_cases h : ρ = τ
  · subst h; simp [only_self]
  · simp [only_of_ne _ h]

end Only

theorem keeps_only_lower {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {τ : E →+* ℂ}
    {M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ} (h0 : ∀ i j, i < j → M i j = 0) (hd : ∀ i, M i i ≠ 0) :
    Keeps σ f (only τ M) := by
  refine keeps_lower hf (fun ρ i j hij => ?_) fun ρ i => ?_
  · by_cases h : ρ = τ
    · subst h; rw [only_self]; exact h0 i j hij
    · rw [only_of_ne _ h, Matrix.one_apply_ne hij.ne]
  · by_cases h : ρ = τ
    · subst h; rw [only_self]; exact hd i
    · simp [only_of_ne _ h]

theorem keeps_upper {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {τ : E →+* ℂ} {i j : Fin (Dw.mult τ)} (hij : i < j)
    (r : ℂ) : Keeps σ f (only τ (Matrix.transvection i j r)) := fun y y' hy' => by
  have hT : ∀ s : CAt σ, (Matrix.transvection i j (X : (CAt σ)[X])).map (eval s) = Matrix.transvection i j s :=
    fun s => by
      ext k m
      simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        eval_add]
      split_ifs <;> simp
  have hsw : ∀ {R : Type} [CommRing R], IsUnit (Matrix.swap R i j).det := fun {R} _ =>
    (Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ (Matrix.swap_mul_self i j))
  have hTd : ∀ {R : Type} [CommRing R] (s : R), IsUnit (Matrix.transvection i j s).det := fun s => by
    rw [Matrix.det_transvection_of_ne _ _ hij.ne]; exact isUnit_one
  obtain ⟨P, hP⟩ := exists_poly hf y (only τ (Matrix.transvection i j X)) (only_det (hTd _))
  obtain ⟨w, hw, -⟩ := existsUnique_frChg E H Dw l Xo c _ y (only τ (Matrix.swap _ i j)) 1 (only_det hsw)
  obtain ⟨Q, hQ⟩ := exists_poly hf w (only τ (Matrix.transvection i j X)) (only_det (hTd _))
  simp only [only_map, hT] at hP hQ
  have hc := poly_const P Q (fun s hs => by
    obtain ⟨B, hB, hBd, hBe⟩ := transvection_eq hij s hs
    obtain ⟨y₁, hy₁, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) w
      (only τ (Matrix.transvection i j (s⁻¹ : ℂ))) 1 (only_det (hTd _))
    have hBu : IsUnit B.det := by
      have := hTd s
      rw [← hBe, Matrix.det_mul] at this
      exact isUnit_of_mul_isUnit_left this
    obtain ⟨y₂, hy₂, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) y₁ (only (R := CAt σ) τ B) 1 (only_det hBu)
    have e3 := keeps_only_lower (σ := σ) hf hB (fun k => by
      rw [hBd k]; split_ifs <;> simp [hs]) y₁ y₂ hy₂
    have h1 := (frChg_refl_and_comp E H Dw l Xo c _ y w y₁).2 _ _ _ _ hw hy₁
    rw [only_mul (R := CAt σ) (Matrix.transvection i j (s⁻¹ : ℂ))] at h1
    have h2 := (frChg_refl_and_comp E H Dw l Xo c _ y y₁ y₂).2 _ _ _ _ h1 hy₂
    rw [only_mul (R := CAt σ) B, Units.val_one, _root_.mul_one, _root_.mul_one] at h2
    have e1 : evR Xo c f y₂ = P.eval s :=
      hP s y₂ ((congrArg (fun M => FrChg (only (R := CAt σ) τ M) 1 y y₂) hBe).mp h2)
    have e2 : evR Xo c f y₁ = Q.eval (s⁻¹ : ℂ) := hQ _ y₁ hy₁
    exact e1.symm.trans (e3.trans e2)) r
  have h0 := hP 0 y (by
    have : only τ (Matrix.transvection i j (0 : CAt σ)) = fun _ => 1 := by simp [only]
    rw [this]
    exact (frChg_refl_and_comp E H Dw l Xo c _ y y y).1)
  exact (hP r y' hy').trans (hc.trans h0.symm)

theorem keeps_only {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {τ : E →+* ℂ}
    (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hM : M.det ≠ 0) : Keeps σ f (only τ M) := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => Keeps σ f (only τ M)) M hM
    (fun d hd => ?_) (fun t => ?_) fun A B hA hB kA kB => ?_
  · rw [Matrix.det_diagonal] at hd
    exact keeps_only_lower hf (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne) fun i => by
      rw [Matrix.diagonal_apply_eq]; exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ i)
  · rcases lt_or_gt_of_ne t.hij with h | h
    · exact keeps_upper hf h t.c
    · refine keeps_only_lower hf (fun k m hkm => ?_) fun k => ?_
      · rw [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hkm.ne,
          Matrix.single_apply_of_ne, add_zero]
        rintro ⟨rfl, rfl⟩
        exact absurd h (not_lt.2 hkm.le)
      · rw [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq,
          Matrix.single_apply_of_ne, add_zero]
        · exact one_ne_zero
        · rintro ⟨h1, h2⟩
          exact t.hij (h1.trans h2.symm)
  · rw [← only_mul]
    exact kA.mul kB (only_det hA.isUnit) (only_det hB.isUnit)

theorem keeps_all {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hg : ∀ τ, IsUnit (g τ).det) :
    Keeps σ f g := by
  classical
  have key : ∀ s : Finset (E →+* ℂ), Keeps σ f fun ρ => if ρ ∈ s then g ρ else 1 := fun s => by
    induction s using Finset.induction_on with
    | empty => exact keeps_lower hf (fun τ i j hij => by simp [Matrix.one_apply_ne hij.ne]) fun τ i => by simp
    | insert τ s hτ ih =>
      have := (keeps_only (σ := σ) hf (g τ) (hg τ).ne_zero).mul ih (only_det (hg τ)) fun ρ => by
        split_ifs
        · exact hg ρ
        · simp
      convert this using 2 with ρ
      by_cases h : ρ = τ
      · subst h; simp [only_self, hτ]
      · simp [only_of_ne _ h, h]
  simpa using key Finset.univ

theorem evR_eq_of_same_point {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {y y' : FrPt Xo c (CAt σ)} (h : y'.x = y.x) :
    evR Xo c f y' = evR Xo c f y := by
  obtain ⟨g, s, hg, hzw⟩ := (frChg_exists_unique E H Dw l Xo c _ y y').1 h
  obtain ⟨z1, h1, -⟩ := existsUnique_frChg E H Dw l Xo c _ y g 1 hg
  obtain ⟨z2, h2, -⟩ := existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
  have h3 := (frChg_refl_and_comp E H Dw l Xo c _ y z1 z2).2 _ _ _ _ h1 h2
  simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
  have e : z2 = y' := (existsUnique_frChg E H Dw l Xo c _ y g s hg).unique h3 hzw
  let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
    | none => s
    | some _ => 1
  rw [← e, evR_bor (t := t) hf (((frBor_calculus E H Dw l Xo c _ z1 z2 z2).1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩)]
  exact keeps_all hf g hg y z1 h1

theorem evR_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (τ : ℂ ≃+* ℂ), ∀ f ∈ sec Xo c 0 0, ∀ (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((τ : ℂ →+* ℂ).comp σ))), y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x → Formalism.L2.PjFree.toC (evR Xo c f y') = τ (Formalism.L2.PjFree.toC (evR Xo c f y)) := by
  intro E _ _ _ H D l Xo c σ τ f hf y y' h
  let φ : CAt σ →ₐ[c.F] CAt ((τ : ℂ →+* ℂ).comp σ) := { (τ : ℂ →+* ℂ) with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo c _ _ φ y
  rw [evR_eq_of_same_point hf (h.trans hz.1.symm), evR_map hf φ hz]
  rfl

end GlobalTheory.WeightZeroValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightZeroSection_value_conj_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (τ : ℂ ≃+* ℂ), ∀ f ∈ sec Xo c 0 0, ∀ (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((τ : ℂ →+* ℂ).comp σ))), y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x → Formalism.L2.PjFree.toC (evR Xo c f y') = τ (Formalism.L2.PjFree.toC (evR Xo c f y)) := by
  first | exact @GlobalTheory.WeightZeroValue.evR_conj | exact GlobalTheory.WeightZeroValue.evR_conj | (intros; apply GlobalTheory.WeightZeroValue.evR_conj <;> assumption)
end
end

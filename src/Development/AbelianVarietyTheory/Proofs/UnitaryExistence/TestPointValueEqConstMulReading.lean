module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RatioSqEqDetJAut
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmUnitPowFourIdempotentModEight
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU gxFst gxSnd ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem test_value_eq_const_mul_reading : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n, toC (ψ (f p y)) = u * rdU U f k x.1 := by
  intro hSB E _ _ _ H Dw l Xo c σ r U hU a n p y ψ
  obtain ⟨-, -, hWD, -, -, -, hBor⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hSB E H Dw l Xo c
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hSB E H Dw l Xo c p.R (CAt σ) ψ y
  obtain ⟨-, -, hcov, -⟩ := hU
  obtain ⟨k, x, t, ht⟩ := hcov z
  have hred : _root_.IsReduced (CAt σ) := by
    unfold CAt
    exact isReduced_of_noZeroDivisors
  refine ⟨k, x, toC (wchar (ex Dw a n) t), ?_⟩
  intro f hf
  have hf' := hf
  unfold sec secW at hf'
  obtain ⟨hN, -⟩ := hf'
  have h1 : evR Xo c f z = ψ (f p y) := by
    have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, y, hz⟩
    unfold evR evalAt
    rw [dif_pos hT]
    exact hWD f hN _ _ _ _ _ _ _ _ hT.choose_spec.choose_spec.choose_spec hz
  have h2 : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := by
    unfold rdU
    exact dif_pos x.2
  have h3 := hBor (CAt σ) hred a n f hf t (U.un k x) z ht
  rw [← h1, h2, h3]
  rfl

end GlobalTheory.FrameUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReadingStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU gxFst gxSnd ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_point_value_eq_const_mul_reading : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n, toC (ψ (f p y)) = u * rdU U f k x.1 := by
  first | exact @GlobalTheory.FrameUnif.test_value_eq_const_mul_reading | exact GlobalTheory.FrameUnif.test_value_eq_const_mul_reading | (intros; apply GlobalTheory.FrameUnif.test_value_eq_const_mul_reading <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
noncomputable section

namespace GlobalTheory.FrameUnif

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU gxFst gxSnd ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem cover_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : ∀ k x, FrameOK e F M k x (un k x))
    (hT : CoverTri e F M) (y : FrPt Xo c (CAt σ)) :
    ∃ k, ∃ x : (M.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) y := by
  obtain ⟨k, x, Pm, hPm, hxy, hv⟩ := hT y
  obtain ⟨Pm', hPm', -, hx', hd', -⟩ := hun k x
  have hP : Pm' = Pm := by
    ext a j
    rw [hPm', hPm]
  subst hP
  refine ⟨k, x, ?_⟩
  have hxx : y.x = (un k x).x := hxy.symm.trans hx'.symm
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (un k x) y y).2.1 hxx fun τ i => ?_
  obtain ⟨cf, h1, h2, h3⟩ := hv (un k x).u hd' τ i
  exact ⟨cf, h1, h2, by rw [← hxx]; exact h3⟩

theorem fibre_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : FramesOK e F M un)
    (hM : ModelBase M) (hB : FibTri e F M) (k k' : Fin F.n) (x : (M.X k).dom) (x' : (M.X k').dom) :
    (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k' x')) ↔
      ∃ γ ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r,
        (⟨k', x'.1⟩ : Σ k, Frame (M.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩ := by
  constructor
  · rintro ⟨t, hx, hu, -⟩
    obtain ⟨Pm, hPm, -, hxP, hd, -⟩ := hun.1 k x
    obtain ⟨Pm', hPm', -, hxP', hd', -⟩ := hun.1 k' x'
    refine hB k k' x x' Pm Pm' (un k x).u (un k' x').u hPm hPm' (hxP.symm.trans (hx.symm.trans hxP')) hd hd'
      fun τ i => ?_
    obtain ⟨cf, hcf, htri, hcomb⟩ := hu τ i
    refine ⟨cf, by rw [hcf]; exact Units.isUnit _, htri, ?_⟩
    rw [hxP] at hcomb
    exact hcomb
  · rintro ⟨γ, hγ, b, hb, heq⟩
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 heq
    have h3 : x'.1 = rmul (lact γ x.1) b := eq_of_heq h2
    have hxg : lact γ x.1 ∈ (M.X k').dom := (hM.domStab k' x.1 x.2).2 γ hγ
    obtain ⟨t1, ht1, -⟩ := hun.2.2.1 k' γ hγ x hxg
    have hxb : rmul (⟨lact γ x.1, hxg⟩ : (M.X k').dom).1 b ∈ (M.X k').dom := by
      have hx2 := x'.2
      rw [h3] at hx2
      exact hx2
    obtain ⟨t2, ht2, -⟩ := hun.2.1 k' ⟨lact γ x.1, hxg⟩ b hb hxb
    have hx' : (⟨rmul (lact γ x.1) b, hxb⟩ : (M.X k').dom) = x' := Subtype.ext h3.symm
    rw [hx'] at ht2
    exact ⟨t2 * t1, (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) _ _ _).2.2.1 t1 t2 ht1 ht2⟩

theorem rdU_of_mem (U : Formalism.L2.PjFree.Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r}
    (h : x ∈ (U.X k).dom) : rdU U f k x = toC (evR Xo c f (U.un k ⟨x, h⟩)) := by
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]

theorem readSec_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : FramesOK e F M un) (hM : ModelBase M)
    (hW : ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → (CAt σ)ˣ)
      (y y' : FrPt Xo c (CAt σ)), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y) :
    ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k,
      ((unfOf e F M un).X k).IsSec (laU (unfOf e F M un) a n k) (rdU (unfOf e F M un) f k) := by
  intro a n hd f hf k
  refine ⟨hun.2.2.2 a n hd f hf k, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hxb : rmul x b ∈ ((unfOf e F M un).X k).dom := (hM.domStab k x hx).1 b hb
    obtain ⟨t, ht, hw⟩ := hun.2.1 k ⟨x, hx⟩ b hb hxb
    refine (rdU_of_mem _ f k hxb).trans ?_
    rw [rdU_of_mem _ f k hx, ← hw a n hd]
    exact congrArg toC (hW a n f hf t _ _ ht)
  · have hxg : lact γ x ∈ ((unfOf e F M un).X k).dom := (hM.domStab k x hx).2 γ hγ
    obtain ⟨t, ht, hw⟩ := hun.2.2.1 k γ hγ ⟨x, hx⟩ hxg
    refine (rdU_of_mem _ f k hxg).trans ?_
    rw [rdU_of_mem _ f k hx, show ((unfOf e F M un).X k).χ (laU (unfOf e F M un) a n k) γ = 1 from hM.chi k _ γ,
      ← hw a n hd]
    exact congrArg toC (hW a n f hf t _ _ ht)

end

theorem isUnf_built : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), GoodEmb c σ → ModelBase M → NegXi M → FramesOK e F M un → IsUnf (unfOf e F M un) := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un hσ hM hN hun
  have hred : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  exact ⟨hM.rank, hM.type,
    cover_unfOf e F M un hun.1 (GlobalTheory.CoverFrame.coverTri E H Dw l Xo c σ g e F r M hσ hM hN),
    fibre_unfOf e F M un hun hM (GlobalTheory.FibreFlag.fibTri E H Dw l Xo c σ g e F r M hσ hM hN),
    readSec_unfOf e F M un hun hM ((GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred),
    g, e, F, id, M.φ, hM.ef, hun.1⟩

end GlobalTheory.FrameUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisationStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU gxFst gxSnd ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyUniformisation_isComplexUniformisation : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), GoodEmb c σ → ModelBase M → NegXi M → FramesOK e F M un → IsUnf (unfOf e F M un) := by
  first | exact @GlobalTheory.FrameUnif.isUnf_built | exact GlobalTheory.FrameUnif.isUnf_built | (intros; apply GlobalTheory.FrameUnif.isUnf_built <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.VVRank (pullS isPullSec_pullS)
open GlobalTheory.TwistBaseChange (eq_pullS_of_isPullSec)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaRuleCompare

section Descent

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem sec_ext {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f₁, p₁⟩ := s
  obtain ⟨f₂, p₂⟩ := s'
  obtain rfl : f₁ = f₂ := funext h
  rfl

omit [GrpObj A] in
theorem chart_ge {T T' : Over S} (h : T' ⟶ T) (j : Fin 1 → L.ι) :
    (h ▷ A).left ⁻¹ᵁ (LPow A L a T).U j ≤ (LPow A L a T').U j := by
  intro y hy
  have h1 : ((h ▷ A).left ≫ (snd T A).left).base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  rw [← Over.comp_left, whiskerRight_snd] at h1
  exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1

theorem gs_pullS {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι) (hz : r z ∈ (LPow A L a T').U j) :
    gs r z ((LPow A L a T').U j) ((pullS A a h s).f j) = gs (r ≫ (h ▷ A).left) z ((LPow A L a T).U j) (s.f j) :=
  (gs_res r z (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j) hz _).trans
    (gs_pull r (h ▷ A).left z _ (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j hz) _)

theorem pullS_comp {T T' T'' : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    pullS A a h' (pullS A a h s) = pullS A a (h' ≫ h) s :=
  sec_ext fun j => fn_ext fun y hy => by
    refine (gs_pullS h' _ _ y j hy).trans ((gs_pullS h _ _ y j
      (chart_le_res A L (h' ▷ A) (whiskerRight_snd _ _) a j hy)).trans (Eq.trans ?_ (gs_pullS _ _ _ y j hy).symm))
    rw [comp_whiskerRight, Over.comp_left]
    rfl

end Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

section Auxiliary

variable (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

end Auxiliary

section Translates

variable (Xo : Moduli Dw l)

variable {Xo}

end Translates

section Values

variable {Xo : Moduli Dw l} {c : Coeff l}

end Values

end GlobalTheory.ThetaRuleCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaFrameDetMulSqInvariantUncond
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaFrameDetMulSqInvariant
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem thetaFrame_det_mul_sq_invariant : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → Out.SecTwistSt → (∀ (g : ℕ) (ga : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), ga ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j)) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct ga τ z) (spAct ga τ) ^ 2 = ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) * (jAut ga τ).det * eC (expArg ga τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ a a', (U.Di i).EF (bas a) (bas a') = -omegaStd a a') → (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P b' (gam a) = h₀ *ᵥ P b a) → ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → (h b).det * (thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) ^ 2 = (h b').det * h₀.det * (thetaChar (τ b') c₁ c₂ (h b' *ᵥ (h₀ *ᵥ z)) * fr j (b', h₀ *ᵥ z)) ^ 2 := by
  intro hMink hT hlaw E _ _ _ H D l Xo σ g ty U i m B P bas h τ c₁ c₂ fr hP hbas hw hn h₁ h₂ hd hne hc h0 hs
    b hb b' hb' gam h₀ hiso hhalf hA hPP j z hz
  have riem : ∀ b ∈ B, IsUnit (h b).det ∧ τ b ∈ SiegelH (Fin g) := fun b hb => by
    obtain ⟨h', τ', -, hu, hsy, hpos, huniq⟩ :=
      (RiemannRel.riemann_relations E H (U.Di i) g ty bas hbas).1 (P b) (hP b hb)
    obtain ⟨e1, e2⟩ := huniq _ _ (hn b hb)
    rw [e1, e2]
    exact ⟨hu, hsy, hpos⟩
  obtain ⟨hu, hτ⟩ := riem b hb
  obtain ⟨hu', hτ'⟩ := riem b' hb'
  obtain ⟨hu₀, hpt, hex⟩ := GlobalTheory.T.uniformization_period_lattice_change hMink E H D l Xo σ g ty U i (P b) (P b') gam h₀ (hP b hb)
    (hP b' hb') hiso hhalf hA hPP
  have hθ : ∀ b ∈ B, (fun z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) ≠ 0 := fun b hb hz => by
    obtain ⟨hu, hτ⟩ := riem b hb
    obtain ⟨n, rfl⟩ := ThetaRatio.exists_eq_halfVec h₁
    obtain ⟨n', rfl⟩ := ThetaRatio.exists_eq_halfVec h₂
    refine theta_ne_zero hτ (halfVec n) (halfVec n') (funext fun w => ?_)
    have := congrFun hz ((h b)⁻¹ *ᵥ w)
    simp only [ThetaRatio.thetaChar_ofRealVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mulVec] at this
    exact this
  obtain ⟨ρ, κ, hρd, hρ0, hρ1, hκ, hrel, hfr⟩ := thetaFrame_ratio hT E H D l Xo σ g ty U i m B P
    (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) fr hP hd hne hc h0 hs b hb b' hb' h₀
    (hθ b hb) (hθ b' hb') hu₀ hpt hex
  have hfull := LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hhalf
  have hiso' : ∀ a b, (U.Di i).EF (gam.symm a) (gam.symm b) = (U.Di i).EF a b := fun a b => by
    rw [← hiso, gam.apply_symm_apply, gam.apply_symm_apply]
  have hfull' : ∀ a, ∃ e, gam.symm a = a + l.M • e := fun a => by
    obtain ⟨e, he⟩ := hfull (gam.symm a)
    rw [gam.apply_symm_apply] at he
    refine ⟨-e, ?_⟩
    rw [smul_neg]
    exact eq_add_neg_of_add_eq he.symm
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => bas.symm (gam.symm (bas (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := AdaptedDet.blocks_det_mod_eight E H (U.Di i) g l.M bas gam.symm N hw
    l.three_le hiso' hfull' (fun _ _ => rfl)
  have hcomp : ∀ a, (h b' * h₀) *ᵥ P b (gam.symm a) = h b' *ᵥ P b' a := fun a => by
    rw [← Matrix.mulVec_mulVec, ← hPP, gam.apply_symm_apply]
  obtain ⟨ga, hga, hgae, hτe, hhe, hde⟩ := PeriodChange.period_change E H (U.Di i) g bas gam.symm N
    (P b) ((P b).comp gam.symm.toLinearMap.toAddMonoidHom) (h b) (h b' * h₀) (τ b) (τ b') hbas hiso'
    (fun _ _ => rfl) (fun _ => rfl) (hn b hb)
    (fun k => ⟨(hcomp _).trans (hn b' hb' k).1, (hcomp _).trans (hn b' hb' k).2⟩) hτ hτ' hu
  have h8ga : ∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j) :=
    fun i j => by
      rw [hgae]
      exact h8 j i
  have hχ : ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have e : ga.toBlocks₂₂.det = N.toBlocks₁₁.det := by
      rw [hgae, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]
    have e' : ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) = 1 := by
      have h4 : ((4 : ℕ) : ℤ) ∣ N.toBlocks₁₁.det - 1 := Dvd.dvd.trans (by norm_num) hdet
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
      rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
      rw [e, this]
    rw [e', map_one, Int.cast_one]
  have hl := hlaw g ga hga h8ga
  rw [hχ] at hl
  have dl : Differentiable ℂ (fun w : Fin g → ℂ => (h b)⁻¹ *ᵥ w) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h b)⁻¹)).differentiable
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g ga hga h8ga hl c₁ c₂ h₁ h₂ (τ b) hτ
    (fun w => ρ ((h b)⁻¹ *ᵥ w)) κ (hρd.comp dl) (fun w => hρ0 _)
    (by simp only [Matrix.mulVec_zero, hρ1]) hκ (fun w => by
      have := hrel ((h b)⁻¹ *ᵥ w)
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at this
      rw [hhe, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hτe] at this
      exact this)
  have e := hrel z
  rw [hfr j z hz, hde, Matrix.det_mul, ← hκ2, ← mul_assoc (thetaChar (τ b') c₁ c₂ _), e]
  ring

end GlobalTheory
end
end

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem thetaFrame_det_mul_sq_invariant_uncond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ a a', (U.Di i).EF (bas a) (bas a') = -omegaStd a a') → (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P b' (gam a) = h₀ *ᵥ P b a) → ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → (h b).det * (thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) ^ 2 = (h b').det * h₀.det * (thetaChar (τ b') c₁ c₂ (h b' *ᵥ (h₀ *ᵥ z)) * fr j (b', h₀ *ᵥ z)) ^ 2 :=
  thetaFrame_det_mul_sq_invariant latMinkowski abelianSchemeLaws_all.2.secTwist
    theta_sq_transform_level_eight

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU gxFst gxSnd ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.ThetaPtChg

theorem exists_chart_point {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ p ⁻¹ᵁ L.U j := by
  let q : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hq : p q ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
  refine ⟨j, fun q' _ => ?_⟩
  have : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [this]
  exact hj

theorem val_of_secBC (hS : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    (x x' : Sp ℂ ⟶ Xo.X) (hx : x' = x) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ)
    (h : SecBC (RingHom.id ℂ) a x x' s s') (p : Over.mk x ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι) (v v' : ℂ)
    (hv : ∀ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = p.left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = v)
    (hv' : ∀ pt : Sp ℂ ⟶ Gx x', pt ≫ gxFst x' = p.left → pt ≫ gxSnd x' = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x').U (fun _ => j)) (s'.f (fun _ => j)) = v') : v' = a * v := by
  subst hx
  have hid : x' = spMap (RingHom.id ℂ) ≫ x' := by
    simp [spMap]
  have h2 := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) x' x' x' hid hid).2.1
    a s s').1 h
  let pt : Sp ℂ ⟶ Gx x' := (CartesianMonoidalCategory.lift (𝟙 (Over.mk x')) p).left
  have e1 : pt ≫ gxFst x' = p.left := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk x')) p)
    exact this
  have e2 : pt ≫ gxSnd x' = 𝟙 (Sp ℂ) := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk x')) p)
    exact this
  rw [← hv pt e1 e2, ← hv' pt e1 e2]
  exact (congrArg (valAt' pt ((PPx x').U (fun _ => j))) (h2 (fun _ => j))).trans
    ((GlobalTheory.sec_values_complex_fibre hS E H Dw l Xo x' s).1 a _ pt e2)

theorem thetaPt_change : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsThetaPt T b κ y → IsThetaPt T b' κ' y' → ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) → (∀ a, T.Pf (T.co b') (gam a) = h₀ *ᵥ T.Pf (T.co b) a) → y'.x = y.x ∧ (∀ τ i, IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co b)) z).left) (h₀⁻¹ *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) ∧ ∃ t₀ : (CAt σ)ˣ, SecBC (RingHom.id (CAt σ)) (t₀ : CAt σ) y.x y'.x y.s y'.s ∧ toC (t₀ : CAt σ) ^ 2 * (κ ^ 2 * (T.h b').det * h₀.det) = κ' ^ 2 * (T.h b).det := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T b hb b' hb' κ κ' y y' gam h₀ hy hy' hgam hP
  obtain ⟨hg1, hg2, hg3⟩ := hgam
  have hp := T.isPer _ hb
  have hp' := T.isPer _ hb'
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k
    (T.Pf (T.co b)) (T.Pf (T.co b')) gam h₀ hp hp' hg1 hg2 hg3 hP
  have hx : y'.x = y.x := hy'.1.trans (hu.symm.trans hy.1.symm)
  refine ⟨hx, fun τ i => ?_, ?_⟩
  · refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k (T.Pf (T.co b)) hp k (T.Pf (T.co b')) (Matrix.mulVecLin h₀) hp'
      hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy'.2.1 τ i
  obtain ⟨gm, a, -, -, -, hbc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y y').1 hx
  refine ⟨a, hbc, ?_⟩
  obtain ⟨hhd, hsym, hpos, -⟩ := T.norm b hb
  obtain ⟨-, w, hw⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  obtain ⟨z, hz⟩ : ∃ z, T.h b *ᵥ z = w :=
    ⟨(T.h b)⁻¹ *ᵥ w, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hhd, Matrix.one_mulVec]⟩
  obtain ⟨j, hj⟩ := exists_chart_point Xo.univ.t.PP.isLB (F.ex k (T.Pf (T.co b)) z).left
  have hmult := GlobalTheory.thetaFrame_det_mul_sq_invariant_uncond E H Dw l Xo _ g _ F k T.m (T.co ⁻¹' (M.X k).dom)
    (fun b => T.Pf (T.co b)) T.bas T.h T.ta T.c₁ T.c₂ T.fr (fun b hb => T.isPer _ hb) T.sympl T.adapt
    (fun b hb => (T.norm b hb).2.2.2) T.half₁ T.half₂ T.fr_hol T.fr_ne T.fr_coc T.fr_rig T.fr_sec
    b hb b' hb' gam h₀ hg1 hg2 hg3 hP j z hj
  have hne : thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) ≠ 0 :=
    mul_ne_zero (by rw [hz]; exact hw) (T.fr_ne j b z hb hj)
  have hw0 : (F.ex k (T.Pf (T.co b)) z).left ≫ Xo.univ.t.G.hom = (y.x : Sp ℂ ⟶ Xo.X) :=
    (Over.w (F.ex k (T.Pf (T.co b)) z)).trans hy.1.symm
  have hval := val_of_secBC hS (Xo := Xo) y.x y'.x hx y.s y'.s (toC (a : CAt σ)) hbc
    (Over.homMk (F.ex k (T.Pf (T.co b)) z).left hw0) j _ _
    (fun pt h1 h2 => hy.2.2 j z pt h1 h2 hj)
    (fun pt h1 h2 => hy'.2.2 j (h₀ *ᵥ z) pt (h1.trans (hex z).symm) h2 (by rw [hex z]; exact hj))
  apply mul_right_cancel₀ (pow_ne_zero 2 hne)
  rw [mul_assoc κ', mul_assoc κ] at hval
  generalize thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) = S at *
  generalize thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ (h₀ *ᵥ z)) * T.fr j (b', h₀ *ᵥ z) = S' at *
  linear_combination (-κ' ^ 2) * hmult - (T.h b').det * h₀.det * (κ' * S' + toC (a : CAt σ) * (κ * S)) * hval

end GlobalTheory.ThetaPtChg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMapStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding Unf GoodEmb toC relab rdU gxFst gxSnd ModelsOf
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsThetaPt T b κ y → IsThetaPt T b' κ' y' → ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) → (∀ a, T.Pf (T.co b') (gam a) = h₀ *ᵥ T.Pf (T.co b) a) → y'.x = y.x ∧ (∀ τ i, IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co b)) z).left) (h₀⁻¹ *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) ∧ ∃ t₀ : (CAt σ)ˣ, SecBC (RingHom.id (CAt σ)) (t₀ : CAt σ) y.x y'.x y.s y'.s ∧ toC (t₀ : CAt σ) ^ 2 * (κ ^ 2 * (T.h b').det * h₀.det) = κ' ^ 2 * (T.h b).det := by
  first | exact @GlobalTheory.ThetaPtChg.thetaPt_change | exact GlobalTheory.ThetaPtChg.thetaPt_change | (intros; apply GlobalTheory.ThetaPtChg.thetaPt_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricLiftsOfFrames
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelCoverCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

attribute [local instance] Over.cartesianMonoidalCategory

section Calc

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {q : Y ⟶ X} {q' : Y' ⟶ X'} {pm : Y' ⟶ Y}

end Calc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Half

end Half

variable {Xo : Moduli D l} {c : Coeff l}

section Cover

variable {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a) (n : ℕ) (nab₂ : NabV C.Xo₂ C.c₂) (f : Rul C.Xo₂ C.c₂)
  (φ : (Fin n → LevQ D a.l₂) → c.F)

end Cover

section Rule

def fnRule (g : Γ(Xo.XF c, ⊤)) : Rul Xo c := fun _ y => fnAt (basePt y) g

theorem fnAt_comp {X : Scheme.{0}} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (y : Sp S ⟶ X) (g : Γ(X, ⊤)) :
    fnAt (spMap ψ ≫ y) g = ψ (fnAt y g) := by
  have e := congrArg (fun k => k.hom (y.appTop.hom g)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

theorem basePt_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {ψ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap ψ y z) : basePt z = spMap ψ.toRingHom ≫ basePt y := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
  · rw [Category.assoc, basePt, basePt, pullback.lift_snd, pullback.lift_snd,
      GlobalTheory.Frames.FramedBaseChange.spMap_comp_spMap]
    exact congrArg spMap ψ.comp_algebraMap.symm

theorem fnRule_mem (g : Γ(Xo.XF c, ⊤)) : fnRule g ∈ sec Xo c 0 0 := by
  refine ⟨fun p q ψ y z h => ?_, fun p t y y' h => ?_⟩
  · change fnAt (basePt z) g = ψ (fnAt (basePt y) g)
    rw [basePt_frMap h, fnAt_comp]
    rfl
  · have e : basePt y' = basePt y := by
      refine pullback.hom_ext ?_ ?_
      · rw [basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
      · rw [basePt, basePt, pullback.lift_snd, pullback.lift_snd]
    have e' : wchar (ex D 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
    change fnAt (basePt y') g = _ * fnAt (basePt y) g
    rw [e, e', _root_.one_mul]

theorem evR_fnRule (g : Γ(Xo.XF c, ⊤)) {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (fnRule g) y = fnAt (basePt y) g := by
  have h := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c S y
  unfold evR evalAt
  rw [dite_eq_left h, basePt_frMap h.choose_spec.choose_spec.choose_spec, fnAt_comp]
  rfl

end Rule

section Law

variable {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)

end Law

section Coefficients

open GlobalTheory.ShortDatumEq

variable {a : IsAuxiliarySplitSquarefreeLevel l}

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) {n : ℕ}

end Coefficients

theorem fnRule_injective : Function.Injective (fnRule (Xo := Xo) (c := c)) := by
  intro g g' h
  refine fn_ext fun z _ => ?_
  obtain ⟨p, j, y, ⟨hj, h1, h2⟩, z, rfl⟩ :=
    GlobalTheory.Frames.exists_openChart_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c z
  have e : basePt y = j := pullback.hom_ext (by rw [basePt, pullback.lift_fst, h1]) (by rw [basePt, pullback.lift_snd, h2])
  have e' : fnAt j g = fnAt j g' := e ▸ congrFun (congrFun h p) y
  have e'' : j.appTop.hom g = j.appTop.hom g' :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of p.R)).hom).1 e'
  refine (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1 ?_
  refine (gs_stalkMap j z ⊤ trivial g).symm.trans (Eq.trans ?_ (gs_stalkMap j z ⊤ trivial g'))
  rw [gs_eq j z ⊤ trivial, gs_eq j z ⊤ trivial]
  exact congrArg _ e''

section Datum

open GlobalTheory.ShortDatumEq

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (n : ℕ)

variable {n}

end Datum

end GlobalTheory.LevelCoverCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq
noncomputable section

namespace GlobalTheory.NonDominant

open AlgebraicGeometry CategoryTheory NumberField Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem poly_eq_zero (P Q : ℂ[X]) (d : ℕ) (hd : 0 < d) (ε : ℂ)
    (h : ∀ c : ℂ, c ≠ 0 → c ^ d * P.eval c = ε * Q.eval c⁻¹) : P = 0 := by
  have key : X ^ (Q.natDegree + d) * P = C ε * Q.reverse := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ (((Set.finite_singleton (0 : ℂ)).infinite_compl).mono fun c hc => ?_)
    have hc : c ≠ 0 := hc
    letI := invertibleOfNonzero (inv_ne_zero hc)
    have h1 := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) c⁻¹ Q
    rw [invOf_eq_inv, inv_inv] at h1
    have h2 : Q.reverse.eval c * c⁻¹ ^ Q.natDegree = Q.eval c⁻¹ := h1
    show eval c _ = eval c _
    rw [eval_mul, eval_mul, eval_pow, eval_X, eval_C, pow_add, mul_assoc, h c hc, ← h2, inv_pow]
    field_simp
  by_contra hP
  have h1 := congrArg natDegree key
  rw [natDegree_X_pow_mul _ hP] at h1
  have h2 := (natDegree_C_mul_le ε Q.reverse).trans (reverse_natDegree_le Q)
  omega

theorem transvection_eq {n : ℕ} {i j : Fin n} (hij : i < j) (c : ℂ) (hc : c ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, (∀ k m, k < m → B k m = 0) ∧
      (∀ k, B k k = if k = i then c else if k = j then -c⁻¹ else 1) ∧
      B * (Matrix.transvection i j c⁻¹ * Matrix.swap ℂ i j) = Matrix.transvection i j c := by
  have hne : i ≠ j := hij.ne
  refine ⟨Matrix.diagonal (fun k => if k = i then c else if k = j then -c⁻¹ else 1) + Matrix.single j i 1,
    fun k m hkm => ?_, fun k => ?_, ?_⟩
  · rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ hkm.ne, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd hij (not_lt.2 hkm.le)
  · rw [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, h⟩
    exact hne h
  · ext k m
    have hT : ∀ (s : ℂ) a b, Matrix.transvection i j s a b = (if a = b then 1 else 0) + if i = a ∧ j = b then s else 0 :=
      fun s a b => by simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
    have hW : ∀ a b, (Matrix.transvection i j c⁻¹ * Matrix.swap ℂ i j) a b =
        Matrix.transvection i j c⁻¹ a (Equiv.swap i j b) := fun a b => by
      by_cases h1 : b = i
      · subst h1; rw [Matrix.mul_swap_apply_left, Equiv.swap_apply_left]
      by_cases h2 : b = j
      · subst h2; rw [Matrix.mul_swap_apply_right, Equiv.swap_apply_right]
      · rw [Matrix.mul_swap_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
    rw [Matrix.add_mul, Matrix.add_apply, Matrix.diagonal_mul]
    have hS : (Matrix.single j i (1 : ℂ) * (Matrix.transvection i j c⁻¹ * Matrix.swap ℂ i j)) k m =
        if k = j then (Matrix.transvection i j c⁻¹ * Matrix.swap ℂ i j) i m else 0 := by
      split_ifs with h
      · subst h; rw [Matrix.single_mul_apply_same, one_mul]
      · exact Matrix.single_mul_apply_of_ne _ _ _ _ _ h _
    rw [hS, hW, hW, hT, hT, hT, Equiv.swap_apply_def]
    by_cases h1 : k = i <;> by_cases h2 : k = j <;> by_cases h3 : m = i <;> by_cases h4 : m = j <;>
      simp_all [eq_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_weight {S : Type} [CommRing S] [Algebra c.F S] [IsReduced S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} (h : FrBor t y y') :
    evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hall : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  exact wtAll_of_borChart (borChartF_of_cover (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
    (ex Dw a n) hf.1 hf.2 S t y y' (hall S y) (hall S y') h

theorem evR_map {S T : Type} [CommRing S] [Algebra c.F S] [IsReduced S] [CommRing T] [Algebra c.F T]
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (φ : S →ₐ[c.F] T) {y : FrPt Xo c S}
    {z : FrPt Xo c T} (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hy := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c S y
  have hW := evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have h1 := frMap_trans _ _ _ _ φ _ _ _ hy.choose_spec.choose_spec.choose_spec h
  have hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨_, _, _, h1⟩
  unfold evR evalAt
  rw [dite_eq_left hz, dite_eq_left hy]
  exact hW f hf.1 T _ _ _ _ _ _ z hz.choose_spec.choose_spec.choose_spec h1

variable {σ : c.F →+* ℂ}

instance (σ : c.F →+* ℂ) : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)

theorem exists_poly {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (y : FrPt Xo c (CAt σ))
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)[X]) (hG : ∀ τ, IsUnit (G τ).det) :
    ∃ P : (CAt σ)[X], ∀ (s : CAt σ) (y' : FrPt Xo c (CAt σ)),
      FrChg (fun τ => (G τ).map (eval s)) 1 y y' → evR Xo c f y' = P.eval s := by
  let π : CAt σ →ₐ[c.F] (CAt σ)[X] := IsScalarTower.toAlgHom _ _ _
  obtain ⟨y₁, h₁⟩ := FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c _ _ π y
  obtain ⟨z, hz, -⟩ := existsUnique_frChg E H Dw l Xo c _ y₁ G 1 hG
  refine ⟨evR Xo c f z, fun s y' hy' => ?_⟩
  let ev : (CAt σ)[X] →ₐ[c.F] CAt σ := (aeval s).restrictScalars c.F
  have hev : ∀ p, ev p = p.eval s := fun p => coe_aeval_eq_eval s ▸ rfl
  obtain ⟨y₂, h₂⟩ := FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c _ _ ev y₁
  have h₃ := frMap_trans _ _ _ π ev _ _ _ h₁ h₂
  have e : ev.comp π = AlgHom.id _ _ := AlgHom.ext fun x => by
    rw [AlgHom.comp_apply, hev]; exact eval_C
  rw [e] at h₃
  obtain rfl : y₂ = y := (frMap_unique_refl_iff E H Dw l Xo c _ _ _ y).1 _ _ h₃ (frMapUniq_refl y)
  rw [← hev]
  refine evR_map hf ev ((ChgBC.frChg_baseChange E H Dw l Xo c _ _ ev y₁ z y₂ y' G _ hz h₂).2 ?_)
  rw [Units.val_one, map_one, show (ev : (CAt σ)[X] → CAt σ) = eval s from funext hev]
  exact hy'

end GlobalTheory.NonDominant
end
end

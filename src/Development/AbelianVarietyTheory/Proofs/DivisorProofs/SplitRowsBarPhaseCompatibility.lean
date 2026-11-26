module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem conjugateReadingsVanishing_splitPart : BarTie (fw2 p) := p.bar


set_option maxHeartbeats 2000000 in
theorem thetaRowData_pins_splitPart (i : Fin D.R.m) : OMPins p.T (R2 p) p.κ p.v₀ (om2 p) i :=
  ⟨(p.pins i).1, { (p.pins i).2 with lift := { (p.pins i).2.lift with }, tuple := fun t => { (p.pins i).2.tuple t with } }⟩

theorem phaseCompatible_splitPart_of_liftUniformisation (hU : p.R.toRealDat.LUnif) (i : Fin D.R.m) :
    PhaseTie p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  have h := p.phase i hU
  have he : phEff p.R = fun _ => 1 := funext fun j => p.phEff_one j
  rw [he] at h
  exact h

end

end GlobalTheory.BigOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRight
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewLevi

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem locMat_unitary_skew (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (skew : ∀ i j, σ (J j i) = -J i j) (g : GL (Fin n) (Fv F v)) :
    (LeviAtPlace.locMat h t J g)ᵀ * J.map (inclR (Fv F v)) * (LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ) =
      J.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (J i j)
  have hs1 : ((LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, LeviAtPlace.locMat, pairMat_snd]
  have hs2 : ((LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, LeviAtPlace.locMat, pairMat_fst]
  have hJs : J.map (t.comp σ) = -(J.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply, Matrix.neg_apply]
    rw [skew j i, map_neg]
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, LeviAtPlace.locMat, pairMat_fst, conjComp]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by
          rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one,
            Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, LeviAtPlace.locMat, pairMat_snd, conjComp, hJs]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))
        = -(Jtᵀ * A * (Jt * Jt⁻¹)ᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg,
            Matrix.neg_mul]
      _ = -(Jtᵀ * (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))) := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]

theorem surj_at_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (h' : GL (Fin (a + a')) (Fv F v)), ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t h'
  have h := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨⟨adelicGL h t G.W.J hJ h', lift_unitary v σ G.W.J _
    (locMat_unitary_skew h t G.W.J hJ hTr.geo.hW.skew h')⟩, lift_sub_one_at v _, ?_⟩
  change (lift v (LeviAtPlace.locMat h t G.W.J h')).map (piW t) = h'.1
  have key : (lift v (LeviAtPlace.locMat h t G.W.J h')).map (piW t) =
      (LeviAtPlace.locMat h t G.W.J h').map (splitProj t) := by
    conv_rhs => rw [← compFin_lift v (LeviAtPlace.locMat h t G.W.J h'), Matrix.map_map]
    rfl
  rw [key]
  exact pairMat_fst h t _ _

end GlobalTheory.SkewLevi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRightStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_group_surjects_general_linear_right : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (h' : GL (Fin (a + a')) (Fv F v)), ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1 := by
  first | exact @GlobalTheory.SkewLevi.surj_at_place | exact GlobalTheory.SkewLevi.surj_at_place | (intros; apply GlobalTheory.SkewLevi.surj_at_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjective
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Matrix

namespace GlobalTheory.SkewSplitSurj

open GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem locMat_unitary_skew (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (skew : ∀ i j, σ (J j i) = -J i j) (g : GL (Fin n) (Fv F v)) :
    (GlobalTheory.LeviAtPlace.locMat h t J g)ᵀ * J.map (inclR (Fv F v)) *
      (GlobalTheory.LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ) = J.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (J i j)
  have hs1 : ((GlobalTheory.LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, GlobalTheory.LeviAtPlace.locMat, pairMat_snd]
  have hs2 : ((GlobalTheory.LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, GlobalTheory.LeviAtPlace.locMat, pairMat_fst]
  have hJs : J.map (t.comp σ) = -(J.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply, Matrix.neg_apply]
    rw [skew j i, map_neg]
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, GlobalTheory.LeviAtPlace.locMat, pairMat_fst, conjComp]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by
          rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one,
            Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, GlobalTheory.LeviAtPlace.locMat, pairMat_snd, conjComp, hJs]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))
        = -(Jtᵀ * A * (Jt * Jt⁻¹)ᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg,
            Matrix.neg_mul]
      _ = -(Jtᵀ * (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))) := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]

end GlobalTheory.SkewSplitSurj


open GlobalTheory.SkewSplitSurj in
theorem GlobalTheory.SkewSplitSurj.exists_locMat_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c x : GL (Fin d) (Fv F v)),
    ∃ h ∈ UAt σ W (evFin F v), locMat t c h = x := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v t c x
  have hcm := hB.cm
  have hJ : IsUnit (W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hW.sig (InfinitePlace.mk φ))
    have h1 : W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show W.J.map t = (t : E →+* Fv F v).mapMatrix W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  set g : GL (Fin d) (Fv F v) := c * x * c⁻¹ with hg
  let hU : UA σ W.J := ⟨GlobalTheory.LeviAtPlace.adelicGL hcm t W.J hJ g,
    GlobalTheory.LeviAtPlace.lift_unitary v σ W.J _ (locMat_unitary_skew hcm t W.J hJ hW.skew g)⟩
  have hmat : mat hU = GlobalTheory.LeviAtPlace.lift v (GlobalTheory.LeviAtPlace.locMat hcm t W.J g) := rfl
  have hpi : (mat hU).map (piW t) = g.val := by
    have e : ∀ M : Matrix (Fin d) (Fin d) (AE F E), M.map (piW t) = (M.map (compFin F E v)).map (splitProj t) :=
      fun M => by rw [Matrix.map_map]; rfl
    rw [hmat, e, GlobalTheory.LeviAtPlace.compFin_lift]
    exact GlobalTheory.LeviAtPlace.pairMat_fst hcm t _ _
  refine ⟨hU, ?_, ?_⟩
  · show At (evFin F v) (mat hU - 1)
    rw [hmat]
    exact GlobalTheory.LeviAtPlace.lift_sub_one_at v _
  · apply Units.ext
    rw [GlobalTheory.KSplit.locMat_val, hpi, hg]
    simp [Matrix.mul_assoc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_matrix_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c x : GL (Fin d) (Fv F v)),
    ∃ h ∈ UAt σ W (evFin F v), locMat t c h = x := by
  first | exact @GlobalTheory.SkewSplitSurj.exists_locMat_eq | exact GlobalTheory.SkewSplitSurj.exists_locMat_eq | (intros; apply GlobalTheory.SkewSplitSurj.exists_locMat_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.IdemAtPl

theorem eq_atPl_of_isIdemAt {D : D7} {e : AE D} {P : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e P) : e = atPl P 1 := by
  classical
  refine ae_ext ?_ fun Q => ?_
  · rw [GlobalTheory.SplitScalar.infPart_splitIdem h.1, (atPl_spec P 1).1]
  · rw [(atPl_spec P 1).2]
    by_cases hQ : Q = P
    · subst hQ
      rw [(cpt_of_isIdemAt h).1, Pi.single_eq_same]
    · rw [(cpt_of_isIdemAt h).2 Q hQ, Pi.single_eq_of_ne hQ]

theorem eq_liftV_of_isPlaceIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (h : IsPlaceIdem D v ε) : ε = GlobalTheory.LatVac.liftV v 1 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hα : α = GlobalTheory.AdelicU.singleFin v 1 := GlobalTheory.AdelicU.af_ext fun u => by
    by_cases hu : u = v
    · subst hu
      rw [h1, GlobalTheory.AdelicU.evalV_singleFin_self]
    · rw [h0 u hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu]
  subst hα
  rfl

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ t : T,
    (∀ w ∈ locPl G t, IsSplitIdem D (atPl w 1) ∧ atPl w 1 + cA D (atPl w 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1)) ∧
    ∀ ε, IsIdemSum ε (locPl G t) → ε = ∑ w ∈ locPl G t, atPl w 1 ∧ ∀ w ∈ locPl G t, ε * atPl w 1 = atPl w 1 := by
  intro D T L sc G μ₀ hL t
  classical
  obtain ⟨_, ⟨es, hes, -⟩, -⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G t
  refine ⟨fun w hw => ?_, fun ε hε => ?_⟩
  · have h := hes w hw
    rw [← eq_atPl_of_isIdemAt h]
    obtain ⟨v, ε, hε, he⟩ := h.1.2.2
    refine ⟨h.1, ?_⟩
    rw [he, eq_liftV_of_isPlaceIdem hε, GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ w v ε h hε he]
  · obtain ⟨⟨fs, hfs, rfl⟩, -⟩ := hε
    have hf : ∀ PP ∈ locPl G t, fs PP = atPl PP 1 := fun PP hPP => eq_atPl_of_isIdemAt (hfs PP hPP)
    refine ⟨Finset.sum_congr rfl hf, fun w hw => ?_⟩
    rw [Finset.sum_congr rfl hf]
    refine ae_ext ?_ fun Q => ?_
    · rw [map_mul, (atPl_spec w 1).1, mul_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_mul, map_mul, (atPl_spec w 1).2, map_sum, map_sum]
        by_cases hQ : Q = w
        · subst hQ
          rw [Pi.single_eq_same, mul_one, Finset.sum_eq_single Q (fun b _ hb => by
            rw [(atPl_spec b 1).2, Pi.single_eq_of_ne (Ne.symm hb)]) (fun h => absurd hw h),
            (atPl_spec Q 1).2, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hQ, mul_zero]

end GlobalTheory.IdemAtPl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ t : T,
    (∀ w ∈ locPl G t, IsSplitIdem D (atPl w 1) ∧ atPl w 1 + cA D (atPl w 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1)) ∧
    ∀ ε, IsIdemSum ε (locPl G t) → ε = ∑ w ∈ locPl G t, atPl w 1 ∧ ∀ w ∈ locPl G t, ε * atPl w 1 = atPl w 1 := by
  first | exact @GlobalTheory.IdemAtPl.main | exact GlobalTheory.IdemAtPl.main | (intros; apply GlobalTheory.IdemAtPl.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine
noncomputable section

namespace GlobalTheory.ThetaLineDeriv

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (realAd)
open scoped Matrix Classical

variable {F : Type} [Field F] [NumberField F]

theorem comp_mem_schA {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun x : κ' → AF F => Φ (x ∘ σ)) ∈ schA F κ' := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
      (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv
    let B : (κ' → Af F) ≃ₜ (κ → Af F) := (Homeomorph.piCongrLeft (Y := fun _ => Af F) σ).symm
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B,
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩
    rfl
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

theorem decay_majorant {N : ℕ} (hF : IsTotallyReal F)
    {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (ω : Set (Fin N → AF F)) (hω : IsCompact ω) :
    ∃ c : (Fin N → F) → ℝ, Summable c ∧ ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ c ξ := by
  obtain ⟨-, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
  refine ⟨fun ξ => C * c ξ, hcs.mul_left C, fun ξ y hy => ?_⟩
  by_cases hmem : fin (rat ξ + y) ∈ K
  · have h1 := hcb ξ y hy hmem
    have h2 := hC (rat ξ + y)
    calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
      _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
      _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
      _ = C * c ξ := mul_comm _ _
  · rw [hKz _ hmem, norm_zero]
    exact mul_nonneg hC0 (hc0 ξ)

theorem schA_majorant {κ : Type} [Fintype κ] (hF : IsTotallyReal F)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (ω : Set (κ → AF F)) (hω : IsCompact ω) :
    ∃ c : (κ → F) → ℝ, Summable c ∧
      ∀ ξ : κ → F, ∀ y ∈ ω, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + y)‖ ≤ c ξ := by
  let σ := Fintype.equivFin κ
  have hc : Continuous fun y : κ → AF F => y ∘ σ.symm := continuous_pi fun i => continuous_apply _
  obtain ⟨c, hcs, hcb⟩ := decay_majorant hF
    (GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (comp_mem_schA σ hΦ)) _ (hω.image hc)
  refine ⟨fun ξ => c (ξ ∘ σ.symm), (Equiv.arrowCongr σ (Equiv.refl F)).summable_iff.2 hcs, fun ξ y hy => ?_⟩
  have h := hcb (ξ ∘ σ.symm) _ ⟨y, hy, rfl⟩
  have e : (rat (ξ ∘ σ.symm) + y ∘ σ.symm) ∘ σ = (fun i => algebraMap F (AF F) (ξ i)) + y := by
    funext i
    simp [rat]
  rwa [e] at h

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_realAd : Continuous (realAd F) :=
  Continuous.prodMk (continuous_ofMixed.comp (continuous_algebraMap ℝ _)) continuous_const

theorem realAd_add (s t : ℝ) : realAd F (s + t) = realAd F s + realAd F t := by
  simp only [realAd, map_add (f := _)]

theorem realAd_zero : realAd F 0 = 0 := by
  simp only [realAd, map_zero]

theorem schr_smul_add {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v : (κ → R) × (κ → R)) (a b : R) (Φ : (κ → R) → ℂ) (z : κ → R) :
    schr ψ ((a + b) • v) Φ z = schr ψ (a • v) (schr ψ (b • v) Φ) z := by
  simp only [schr, Prod.smul_fst, Prod.smul_snd, ← mul_assoc, ← AddChar.map_add_eq_mul, add_smul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  first
    | linear_combination (a * b * (v.1 ⬝ᵥ v.2)) * invOf_mul_self (2 : R)
    | linear_combination (-(a * b * (v.1 ⬝ᵥ v.2))) * invOf_mul_self (2 : R)

variable [Invertible (2 : AF F)] {κ : Type} [Fintype κ]

theorem hasDerivAt_schr (ψ : AddChar (AF F) ℂ) (v : (κ → AF F) × (κ → AF F))
    {Φ Φ' : (κ → AF F) → ℂ} (hd : ∀ z, HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (Φ' z) 0)
    (z : κ → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (schr ψ (realAd F t • v) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) (schr ψ (realAd F t • v) Φ' z) (t - t) := by
    have e : (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) = fun h =>
        ψ (z ⬝ᵥ (realAd F t • v).2 + ⅟(2 : AF F) * ((realAd F t • v).1 ⬝ᵥ (realAd F t • v).2)) *
          schr ψ (realAd F h • v) Φ (z + (realAd F t • v).1) := by
      funext h
      rw [realAd_add, schr_smul_add]
      rfl
    rw [e, sub_self]
    exact (hd _).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

theorem hasDerivAt_thetaSum_schr (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ)
    (v : (κ → AF F) × (κ → AF F)) {Φ Φ' : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΦ' : Φ' ∈ schA F κ)
    (hd : ∀ z, HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (Φ' z) 0) (w : (κ → AF F) × (κ → AF F)) :
    HasDerivAt (fun t : ℝ => thetaSum F (schr ψ w (schr ψ (realAd F t • v) Φ))) (thetaSum F (schr ψ w Φ')) 0 := by
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : realAd F 0 • v = 0 := by rw [realAd_zero, zero_smul]
  set ω : Set (κ → AF F) := (fun s : ℝ => w.1 + (realAd F s • v).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image
    (continuous_const.add (continuous_pi fun i => continuous_realAd.mul (continuous_const (y := v.1 i))))
  obtain ⟨c, hcs, hcb⟩ := schA_majorant hF hΦ' ω hωc
  obtain ⟨c₀, hcs₀, hcb₀⟩ := schA_majorant hF hΦ {w.1} isCompact_singleton
  set r : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i) with hr
  set ph : (κ → F) → ℂ := fun ξ => ψ (r ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => thetaSum F (schr ψ w (schr ψ (realAd F t • v) Φ))) =
      fun t => ∑' ξ : κ → F, ph ξ * schr ψ (realAd F t • v) Φ (r ξ + w.1) := rfl
  have h0 : ∀ Ψ : (κ → AF F) → ℂ, schr ψ (realAd F 0 • v) Ψ = Ψ := fun Ψ => by
    rw [hM0]
    funext z
    simp [schr]
  have hv : thetaSum F (schr ψ w Φ') = ∑' ξ : κ → F, ph ξ * schr ψ (realAd F 0 • v) Φ' (r ξ + w.1) := by
    rw [h0]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected hcs isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_schr ψ v hd (r ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (realAd F t • v).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, schr, norm_mul, hnorm, one_mul, add_assoc]
    exact this
  · refine Summable.of_norm_bounded hcs₀ fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simp only [h0, ph, norm_mul, hnorm, one_mul]
    exact this

end SlopeTestRemainingChoices

end GlobalTheory.ThetaLineDeriv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

theorem GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho : ∀ {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U] {B : U → U → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ (u : U), ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
    (∀ x, HasDerivAt (fun t : ℝ => co.rho ψ (realAd F t • u) Φ x) (Φ' x) 0) →
    ∀ w : U, HasDerivAt (fun t : ℝ => thetaSum F (co.rho ψ w (co.rho ψ (realAd F t • u) Φ))) (thetaSum F (co.rho ψ w Φ')) 0 := by
  intro F _ _ U _ _ B κ _ co ψ hF hψ u Φ hΦ Φ' hΦ' hd w
  simp only [Darboux.rho, map_smul] at hd ⊢
  exact GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr ψ hF hψ (co.e u) hΦ hΦ' hd (co.e w)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_thetaTransform_heisenberg_real_line : ∀ {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U] {B : U → U → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ (u : U), ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
    (∀ x, HasDerivAt (fun t : ℝ => co.rho ψ (realAd F t • u) Φ x) (Φ' x) 0) →
    ∀ w : U, HasDerivAt (fun t : ℝ => thetaSum F (co.rho ψ w (co.rho ψ (realAd F t • u) Φ))) (thetaSum F (co.rho ψ w Φ')) 0 := by
  first | exact @GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho | exact GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho | (intros; apply GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuu
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VacTransport

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring


omit [DecidableEq α] [DecidableEq β] in
theorem symp_mul_transpose (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (h : Matrix β β E)
    (hh : hᵀ * JB * h.map c = JB) (x y : Matrix α β E) :
    symp (R := R) c ξ JA JB (x * hᵀ) (y * hᵀ) = symp (R := R) c ξ JA JB x y := by
  unfold symp
  rw [hTens_eq, hTens_eq]
  have e : (y * hᵀ).map c = y.map c * (hᵀ).map c := Matrix.map_mul (f := c.toRingHom)
  have e2 : x * hᵀ * JB * ((y * hᵀ).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    rw [e, Matrix.transpose_mul, ← Matrix.transpose_map, Matrix.transpose_transpose]
    conv_rhs => rw [← hh]
    simp only [Matrix.mul_assoc]
  rw [e2]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem vecMulVec_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) {x : Fin n → E} (hx : x ∈ X.L)
    {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt Y v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) z ∈ latAtV X Y v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hv, x, hx, y, hy, ?_⟩
    ext i j
    simp [Matrix.vecMulVec_apply, incM]
  | zero =>
    have e : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [e]; exact zero_mem _
  | add z z' _ _ h h' => rw [Matrix.vecMulVec_add]; exact add_mem h h'
  | neg z _ h => rw [Matrix.vecMulVec_neg]; exact neg_mem h

theorem mul_transpose_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) (h : Matrix (Fin d) (Fin d) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.InertSph.latAt Y v, h *ᵥ z ∈ GlobalTheory.InertSph.latAt Y v)
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X Y v) : γ * hᵀ ∈ latAtV X Y v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, x, hx, y, hy, rfl⟩ := hz
    have hm : (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt Y v :=
      AddSubgroup.subset_closure ⟨a, ha, hv, y, hy, rfl⟩
    have e : a • incM F (Matrix.vecMulVec x y) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (a • fun i => inclR (F := F) (AF F) (y i)) := by
      ext i j
      simp [Matrix.vecMulVec_apply, incM]
    rw [e, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    exact vecMulVec_mem X Y v hx (hh _ hm)
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add z z' _ _ h h' => rw [Matrix.add_mul]; exact add_mem h h'
  | neg z _ h => rw [Matrix.neg_mul]; exact neg_mem h

omit [NumberField E] in
theorem tens_smul {R κ : Type} (ev : AF F → R) (c : ℂ) (φ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (c • φ) r = c • tens ev φ r := by
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (1, k)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v k hk θ _ φ hφ φ₁ _ hfix hact γ hγ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hγ' : γ * (mat k⁻¹)ᵀ ∈ latAtV G.V G.W v := mul_transpose_mem G.V G.W v _ (fun z hz => (hk.2 z hz).2) hγ
  have hback : actAB (cA σ) ((1 : UA σ G.V.J), k) (γ * (mat k⁻¹)ᵀ) = γ := by
    change (1 : Matrix _ _ _) * (γ * (mat k⁻¹)ᵀ) * (mat k)ᵀ = γ
    have e : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) (mat k⁻¹)
    (k⁻¹).2 γ γ
  have h1 := hS.impl (1, k) (γ * (mat k⁻¹)ᵀ) _ hr'.2
  rw [hback, hfix _ hγ' r hr', hsy, tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, tens_smul]

end GlobalTheory.VacTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuuStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (1, k)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.VacTransport.transport | exact GlobalTheory.VacTransport.transport | (intros; apply GlobalTheory.VacTransport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.SchrIrred

open ValuativeRel

theorem norm_addChar_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (x : k) : ‖ψ x‖ = 1 := by
  have hle : ∀ y : k, ‖ψ y‖ ≤ 1 := by
    intro y
    have hK : IsCompact ((fun u : k => y * u) '' (𝒪[k] : Set k)) :=
      (IsNonarchimedeanLocalField.isCompact_closedBall k 1).image (by fun_prop)
    obtain ⟨C, hC⟩ := (hK.image (continuous_norm.comp hψ)).isBounded.exists_norm_le
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    have hmem : ‖ψ (y * (n : k))‖ ∈ (fun z => ‖ψ z‖) '' ((fun u : k => y * u) '' (𝒪[k] : Set k)) :=
      ⟨y * n, ⟨n, natCast_mem _ n, rfl⟩, rfl⟩
    have h2 := hC _ hmem
    rw [Real.norm_of_nonneg (norm_nonneg _), mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at h2
    linarith
  have h1 : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by rw [← norm_mul, h1, norm_one]
  have a := hle x
  have b := hle (-x)
  nlinarith [norm_nonneg (ψ x), norm_nonneg (ψ (-x))]

def toCircle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) : AddChar k Circle where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (norm_addChar_eq_one ψ hψ x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (by show ψ (a + b) = ψ a * ψ b; exact AddChar.map_add_eq_mul ψ a b)

theorem coe_toCircle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (x : k) : (toCircle ψ hψ x : ℂ) = ψ x := rfl

def colH (k : Type) [TopologicalSpace k] (κ : Type) : (κ → k) ≃ₜ Matrix κ Unit k where
  toFun x := Matrix.of fun i _ => x i
  invFun M i := M i ()
  left_inv _ := rfl
  right_inv M := by ext i j; cases j; rfl
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun _ => continuous_apply i
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    exact (continuous_apply () ).comp (continuous_apply i)

theorem sb_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {f : Y → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB Y) : f ∘ h ∈ GlobalTheory.WeilM.SB X :=
  ⟨hf.1.comp_continuous h.continuous, hf.2.comp_homeomorph h⟩

end GlobalTheory.SchrIrred

namespace GlobalTheory.SchrIrred

open ValuativeRel

theorem schr_irreducible_local (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] [Invertible (2 : k)] {κ : Type} [Fintype κ] (ψk : AddChar k ℂ) (hc : Continuous ψk) (h1 : ψk ≠ 1)
    (N : Submodule ℂ ((κ → k) → ℂ)) (hN : N ≤ GlobalTheory.WeilM.SB (κ → k))
    (hS : ∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) (φ₀ : (κ → k) → ℂ) (h0 : φ₀ ∈ N) (hne : φ₀ ≠ 0) :
    N = GlobalTheory.WeilM.SB (κ → k) := by
  classical
  let e := colH k κ
  let L : (Matrix κ Unit k → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) := LinearMap.funLeft ℂ ℂ e
  have hL : ∀ Φ, L Φ = Φ ∘ e := fun _ => rfl
  have hcirc : Continuous (toCircle ψk hc) := by
    have : Continuous (fun x => ((toCircle ψk hc x : Circle) : ℂ)) := hc
    exact continuous_induced_rng.2 this
  have hne1 : toCircle ψk hc ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [coe_toCircle] using this
  have hW : N.comap L ≤ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) := by
    intro Φ hΦ
    have h := sb_comp e.symm (hN hΦ)
    have : (Φ ∘ e) ∘ e.symm = Φ := by funext M; simp
    rw [← this]
    exact h
  have hT : ∀ Φ ∈ N.comap L, ∀ x : Matrix κ Unit k, (fun t => Φ (t + x)) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) →
      (fun t => Φ (t + x)) ∈ N.comap L := by
    intro Φ hΦ x _
    rw [Submodule.mem_comap, hL] at hΦ ⊢
    have h := hS (e.symm x, 0) _ hΦ
    convert h using 1
    funext y
    have he : e (y + e.symm x) = e y + x := by ext i j; cases j; rfl
    simp [schr, he]
  have hM : ∀ Φ ∈ N.comap L, ∀ b : Matrix κ Unit k,
      (fun t => ((toCircle ψk hc (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) * Φ t) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) →
      (fun t => ((toCircle ψk hc (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) * Φ t) ∈ N.comap L := by
    intro Φ hΦ b _
    rw [Submodule.mem_comap, hL] at hΦ ⊢
    have h := hS (0, fun r => b r ()) _ hΦ
    convert h using 1
    funext y
    simp [schr, dotProduct, coe_toCircle, e, colH, mul_comm]
    change Φ (e y) * ψk (∑ r, b r () * y r) = ψk (∑ r, b r () * y r) * Φ (e y)
    exact mul_comm _ _
  have h0' : φ₀ ∘ e.symm ∈ N.comap L := by
    rw [Submodule.mem_comap, hL]
    have : (φ₀ ∘ e.symm) ∘ e = φ₀ := by funext y; simp
    rw [this]; exact h0
  have hne' : φ₀ ∘ e.symm ≠ 0 := by
    intro h
    apply hne
    funext y
    have := congrFun h (e y)
    simpa using this
  have hall := GlobalTheory.IrredSB.sb_irreducible k κ Unit (toCircle ψk hc) hcirc hne1 (N.comap L) hW hT hM _ h0' hne'
  refine le_antisymm hN fun φ hφ => ?_
  have hm : φ ∘ e.symm ∈ N.comap L := by
    rw [hall]
    exact sb_comp e.symm hφ
  rw [Submodule.mem_comap, hL] at hm
  have : (φ ∘ e.symm) ∘ e = φ := by funext y; simp
  rwa [this] at hm

end GlobalTheory.SchrIrred

namespace GlobalTheory.SchrIrred

theorem schr_irreducible : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ N : Submodule ℂ ((κ → Fv F v) → ℂ), N ≤ GlobalTheory.WeilM.SB (κ → Fv F v) → (∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) → ∀ φ₀ ∈ N, φ₀ ≠ 0 →
      N = GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v κ _ ψk hc h1 N hN hS φ₀ h0 hne
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  exact schr_irreducible_local (Fv F v) ψk hc h1 N hN hS φ₀ h0 hne

end GlobalTheory.SchrIrred
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_irreducible_finitePlaceCompletion : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ N : Submodule ℂ ((κ → Fv F v) → ℂ), N ≤ GlobalTheory.WeilM.SB (κ → Fv F v) → (∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) → ∀ φ₀ ∈ N, φ₀ ≠ 0 →
      N = GlobalTheory.WeilM.SB (κ → Fv F v) := by
  first | exact @GlobalTheory.SchrIrred.schr_irreducible | exact GlobalTheory.SchrIrred.schr_irreducible | (intros; apply GlobalTheory.SchrIrred.schr_irreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualL6OfLowerBound
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

def lowScalarPt (C CH : ℝ) : PtP := fun _ _ _ p => (p.S true).L6 (p.N C CH)

end GlobalTheory.Fc.Ind

end
end

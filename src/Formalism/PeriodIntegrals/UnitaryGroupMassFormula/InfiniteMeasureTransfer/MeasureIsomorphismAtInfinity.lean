module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasInfXferOf

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.ContinuousEvI
noncomputable section

open NumberField Matrix Formalism.L2.SG.AdBridge
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)

namespace Formalism.L2.SG.Pf.MeasInfW

variable (I : AutInst)

abbrev TI : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F ⊗[I.F] I.E

def evI (v : InfinitePlace I.F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    (Pi.evalRingHom (fun w : InfinitePlace I.F => w.Completion) v)

theorem evI_apply (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) :
    evI I v a = InfinitePlace.Completion.extensionEmbedding v (a v) := rfl

theorem evI_algebraMap (v : InfinitePlace I.F) (a : I.F) :
    evI I v (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) a) = v.embedding a := by
  change InfinitePlace.Completion.extensionEmbedding v (algebraMap I.F v.Completion a) = _
  rw [AbsoluteValue.Completion.algebraMap_def, InfinitePlace.Completion.extensionEmbedding_coe,
    WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply, WithAbs.equiv_apply,
    WithAbs.ofAbs_toAbs]

def thI (v : InfinitePlace I.F) : TI I →+* ℂ :=
  letI : Algebra I.F ℂ := v.embedding.toAlgebra
  (Algebra.TensorProduct.lift
    ({ evI I v with commutes' := fun a => evI_algebraMap I v a } :
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F →ₐ[I.F] ℂ)
    ({ I.φ v with commutes' := I.φ_over v } : I.E →ₐ[I.F] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem thI_tmul (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (x : I.E) :
    thI I v (a ⊗ₜ[I.F] x) = evI I v a * I.φ v x := by
  simp [thI]

def kap : TT I →+* TI I := Formalism.L2.SG.Measures.tensMap (E := I.E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA I.F)

theorem kap_tmul (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (x : I.E) : kap I (a ⊗ₜ[I.F] x) = a.1 ⊗ₜ[I.F] x := by
  simp [kap, Formalism.L2.SG.Measures.tensMap]
  rfl

theorem thI_kap (v : InfinitePlace I.F) (y : TT I) : thI I v (kap I y) = thetaV I v y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [kap_tmul, thI_tmul, thetaV_tmul]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem kap_surj (y : TI I) : ∃ y0 : TT I, kap I y0 = y ∧ tauF I y0 = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | tmul a x =>
    let a0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F := (a, 0)
    refine ⟨a0 ⊗ₜ[I.F] x, kap_tmul I a0 x, ?_⟩
    rw [tauF_tmul]
    exact TensorProduct.tmul_zero _ _
  | add x y hx hy =>
    obtain ⟨x0, hx0, hx1⟩ := hx
    obtain ⟨y0, hy0, hy1⟩ := hy
    exact ⟨x0 + y0, by rw [map_add (f := _), hx0, hy0], by rw [map_add (f := _), hx1, hy1, add_zero]⟩

theorem thI_inj (y : TI I) (h : ∀ v, thI I v y = 0) : y = 0 := by
  obtain ⟨y0, rfl, hτ⟩ := kap_surj I y
  have : y0 = 0 := TT_ext I y0 (fun v => by rw [← thI_kap]; exact h v) hτ
  rw [this, map_zero]

theorem thI_ext (y y' : TI I) (h : ∀ v, thI I v y = thI I v y') : y = y' :=
  sub_eq_zero.1 (thI_inj I _ fun v => by rw [map_sub, h v, sub_self])

theorem thI_surj (z : InfinitePlace I.F → ℂ) : ∃ y : TI I, ∀ v, thI I v y = z v := by
  obtain ⟨y0, h1, -⟩ := TT_surj I z 0
  exact ⟨kap I y0, fun v => by rw [thI_kap]; exact h1 v⟩

theorem thI_inclR (v : InfinitePlace I.F) (x : I.E) :
    thI I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) x) = I.φ v x := by
  show thI I v ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) ⊗ₜ[I.F] x) = _
  rw [thI_tmul, map_one, one_mul]

theorem thI_sigR (v : InfinitePlace I.F) (x : TI I) :
    thI I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig x) =
      starRingEnd ℂ (thI I v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig (a ⊗ₜ[I.F] y) =
        a ⊗ₜ[I.F] I.cm.sig y := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    rw [hs, thI_tmul, thI_tmul, map_mul]
    congr 1
    · have hv : v.IsReal := I.cm.totReal.isReal v
      rw [evI_apply, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv, Complex.conj_ofReal]
    · exact I.cm.cmUnram.2.1 (I.φ v) y
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

instance imtTI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I) := ⟨rfl⟩

instance topRingTI : IsTopologicalRing (TI I) :=
  IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)

theorem continuous_evI (v : InfinitePlace I.F) : Continuous (evI I v) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)

theorem continuous_thI (v : InfinitePlace I.F) : Continuous (thI I v) := by
  apply IsModuleTopology.continuous_of_ringHom (R := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F)
  have : (thI I v).comp (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)) = evI I v := by
    ext a
    simp [Algebra.TensorProduct.algebraMap_apply, thI_tmul]
  rw [this]
  exact continuous_evI I v

theorem continuous_kap : Continuous (kap I) := by
  apply IsModuleTopology.continuous_of_ringHom (R := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)
  have := IsModuleTopology.toContinuousSMul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)
  have : (kap I).comp (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (TT I)) =
      (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)).comp
        (RingHom.fst (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (Formalism.MainNotions.S.Af I.F)) := by
    ext a
    show kap I (algebraMap _ _ a) = algebraMap _ (TI I) a.1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Algebra.algebraMap_self, RingHom.id_apply, kap_tmul]
  rw [this]
  exact (continuous_algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)).comp continuous_fst

end Formalism.L2.SG.Pf.MeasInfW
end
end

noncomputable section

open NumberField Matrix Formalism.L2.SG.AdBridge
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)

namespace Formalism.L2.SG.Pf.MeasInfW

variable (I : AutInst)

abbrev hmI (g : HI I) : Matrix (Fin I.n) (Fin I.n) (TI I) :=
  ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J g : GL (Fin I.n) (TI I)) :
    Matrix (Fin I.n) (Fin I.n) (TI I))

def matI : HI I →* GL (Fin I.n) (TI I) :=
  (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J).subtype

theorem matI_apply (g : HI I) : ((matI I g : GL (Fin I.n) (TI I)) : Matrix _ _ _) = hmI I g := rfl

theorem thI_mem (g : HI I) (v : InfinitePlace I.F) :
    Formalism.REAL.inUJ (I.ε v) ((I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v) := by
  have hg : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig) (hmI I g) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.J * hmI I g =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.J := by
    have hm : ∀ h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J,
        (h : GL (Fin I.n) (TI I)) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J :=
      fun h => h.2
    exact hm g
  have h1 : ((hmI I g).map (thI I v))ᴴ * I.J.map (I.φ v) * (hmI I g).map (thI I v) =
      I.J.map (I.φ v) := by
    have h2 := congrArg (fun M => M.map (thI I v)) hg
    simp only [Matrix.map_mul] at h2
    have e1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig)
        (hmI I g)).map (thI I v) = ((hmI I g).map (thI I v))ᴴ := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        thI_sigR, starRingEnd_apply]
    have e2 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.J).map (thI I v) =
        I.J.map (I.φ v) := by
      ext i j
      simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply, thI_inclR]
    rw [e1, e2] at h2
    exact h2
  have hd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have hPP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hPPh : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one]
  show ((I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v)ᴴ * Formalism.REAL.Jm (I.ε v) *
      ((I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v) = Formalism.REAL.Jm (I.ε v)
  rw [← I.P_spec v]
  simp only [Matrix.conjTranspose_mul]
  calc _ = (I.P v)ᴴ * (((hmI I g).map (thI I v))ᴴ * ((((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) *
          I.J.map (I.φ v) * ((I.P v * (I.P v)⁻¹) * (hmI I g).map (thI I v)))) * I.P v := by
        simp only [Matrix.mul_assoc]
    _ = (I.P v)ᴴ * (((hmI I g).map (thI I v))ᴴ * I.J.map (I.φ v) * (hmI I g).map (thI I v)) *
          I.P v := by
        rw [hPPh, hPP]
        simp only [Matrix.one_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]

def betaV (v : InfinitePlace I.F) : HI I →* Formalism.REAL.UJ (I.ε v) :=
  ((MulAut.conj (Formalism.L2.SG.Pf.Pu I v)⁻¹).toMonoidHom.comp ((Formalism.UG.bc (thI I v)).comp (matI I))).codRestrict
    (Formalism.REAL.UJ (I.ε v)) (fun g => by
      show Formalism.REAL.inUJ (I.ε v) _
      convert thI_mem I g v using 1
      simp [Formalism.L2.SG.Pf.Pu, Formalism.UG.bc, matI_apply, Matrix.coe_units_inv])

theorem betaV_val (v : InfinitePlace I.F) (g : HI I) :
    uMat (betaV I v g) = (I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v := by
  simp [betaV, uMat, Formalism.L2.SG.Pf.Pu, Formalism.UG.bc, matI_apply, Matrix.coe_units_inv]

def betaI : HI I →* I.Ginf := MonoidHom.pi (betaV I)

theorem continuous_betaV (v : InfinitePlace I.F) : Continuous (betaV I v) := by
  have hval : Continuous (fun g : HI I => hmI I g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hinv : Continuous (fun g : HI I => hmI I g⁻¹) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have key : ∀ f : HI I → Matrix (Fin I.n) (Fin I.n) (TI I), Continuous f →
      Continuous (fun g => (I.P v)⁻¹ * (f g).map (thI I v) * I.P v) := fun f hf =>
    (continuous_const.matrix_mul (hf.matrix_map (continuous_thI I v))).matrix_mul continuous_const
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · convert key _ hval using 1
    funext g
    exact betaV_val I v g
  · convert key _ hinv using 1
    funext g
    simp only [Function.comp_apply]
    rw [← betaV_val, map_inv]
    rfl

theorem continuous_betaI : Continuous (betaI I) := continuous_pi fun v => continuous_betaV I v

section Bridge

variable (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I)

theorem continuous_toInfL : Continuous (Formalism.L2.SG.Pf.MeasInf.toInfL I hb) := by
  have h1 : Continuous (fun s : I.Ginf => toHA I hb (s, 1)) :=
    (toHA I hb).continuous.comp (continuous_id.prodMk continuous_const)
  have hv : Continuous (fun x : HAd I => (hmat I x).map (kap I)) :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_map (continuous_kap I)
  have hi : Continuous (fun x : HAd I =>
      (((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J x)⁻¹ :
        GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)).map (kap I)) :=
    (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (continuous_kap I)
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hv.comp h1
  · exact hi.comp h1

def toInfH : I.Ginf →* HI I :=
  (Formalism.L2.SG.Measures.haMap I.cm.sig I.J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA I.F)).comp
    ((toHA I hb).toMulEquiv.toMonoidHom.comp (MonoidHom.inl I.Ginf I.Gf))

theorem hmI_toInfL (s : I.Ginf) (i j : Fin I.n) :
    hmI I (Formalism.L2.SG.Pf.MeasInf.toInfL I hb s) i j = kap I (hmat I (toHA I hb (s, 1)) i j) := rfl

theorem betaI_toInfL (s : I.Ginf) : betaI I (Formalism.L2.SG.Pf.MeasInf.toInfL I hb s) = s := by
  funext v
  apply Subtype.ext
  apply Units.ext
  change uMat (betaV I v (Formalism.L2.SG.Pf.MeasInf.toInfL I hb s)) = uMat (s v)
  rw [betaV_val, show uMat (s v) = _ from (hb.choose_spec (s, 1)).1 v]
  simp only [Formalism.L2.SG.AdBridge.ofHAInf]
  congr 2
  ext i j
  simp only [Matrix.map_apply]
  rw [hmI_toInfL, thI_kap]
  rfl

private lemma eq_of_conj_eq_of_isUnit {n : ℕ} (A B P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (h : P⁻¹ * A * P = P⁻¹ * B * P) : A = B := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 := congrArg (fun M => P * M * P⁻¹) h
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one] at h1
  simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul] using h1

theorem betaI_inj (g g' : HI I) (h : betaI I g = betaI I g') : g = g' := by
  have hv : ∀ v, (hmI I g).map (thI I v) = (hmI I g').map (thI I v) := by
    intro v
    have h1 := congrArg uMat (congrFun h v)
    have e1 : uMat (betaI I g v) = (I.P v)⁻¹ * (hmI I g).map (thI I v) * I.P v := betaV_val I v g
    have e2 : uMat (betaI I g' v) = (I.P v)⁻¹ * (hmI I g').map (thI I v) * I.P v :=
      betaV_val I v g'
    rw [e1, e2] at h1
    exact eq_of_conj_eq_of_isUnit _ _ _ (I.P_unit v) h1
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply thI_ext I
  intro v
  have h3 := congrFun (congrFun (hv v) i) j
  simp only [Matrix.map_apply] at h3
  exact h3

theorem toInfL_betaI (g : HI I) : Formalism.L2.SG.Pf.MeasInf.toInfL I hb (betaI I g) = g := betaI_inj I _ g (betaI_toInfL I hb (betaI I g))

def toInfE : I.Ginf ≃ₜ* HI I where
  toFun := Formalism.L2.SG.Pf.MeasInf.toInfL I hb
  invFun := betaI I
  left_inv := betaI_toInfL I hb
  right_inv := toInfL_betaI I hb
  map_mul' := (toInfH I hb).map_mul
  continuous_toFun := continuous_toInfL I hb
  continuous_invFun := continuous_betaI I

end Bridge

theorem measure_isomorphism_at_infinity : IsoStep := fun I hb => ⟨toInfE I hb, fun _ => rfl⟩

end Formalism.L2.SG.Pf.MeasInfW

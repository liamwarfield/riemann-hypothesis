module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetInertPlaceLatticeLength
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetInertPlaceLatticeLength
noncomputable section

namespace GlobalTheory.InertLatLength

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open GlobalTheory.LFun (toCompl latAt IsFrameAt)
open GlobalTheory.LFun.InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

def intMap (h : w.under (𝓞 F) = v) : intLoc F E v →+* w.adicCompletionIntegers E :=
  ((toCompl h).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E) fun y => toCompl_mem h y.2

theorem intMap_surjective (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    Function.Surjective (intMap h) := by
  intro z
  obtain ⟨y, hy⟩ := (toCompl_bijective hw h).2 (z : w.adicCompletion E)
  have hy' : y ∈ intLoc F E v := (mem_intLoc_iff hw h y).2 (by rw [hy]; exact z.2)
  exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩

def coord (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y : Fin n → Fv F v ⊗[F] E) :
    Fin n → w.adicCompletion E :=
  (a⁻¹).1 *ᵥ (toCompl h ∘ y)

theorem mulVec_coord (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y : Fin n → Fv F v ⊗[F] E) :
    a.1 *ᵥ coord h a y = toCompl h ∘ y := by
  rw [coord, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_latLoc_iff_coord {L : Submodule (𝓞 E) (Fin n → E)} (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) {a : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a)
    (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ latLoc F L v ↔ ∀ i, coord h a y i ∈ w.adicCompletionIntegers E := by
  rw [mem_latLoc_iff hw h, ← mulVec_coord h a y]
  exact (ha _).symm

theorem coord_injective (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (a : GL (Fin n) (w.adicCompletion E)) : Function.Injective (coord h a) := by
  intro y y' e
  have e' : toCompl h ∘ y = toCompl h ∘ y' := by rw [← mulVec_coord, ← mulVec_coord, e]
  exact funext fun i => (toCompl_bijective hw h).1 (congrFun e' i)

theorem coord_add (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (y y' : Fin n → Fv F v ⊗[F] E) :
    coord h a (y + y') = coord h a y + coord h a y' := by
  simp only [coord, ← Matrix.mulVec_add]
  congr 1
  funext i
  simp [map_add (f := _)]

theorem coord_smul (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (c : Fv F v ⊗[F] E)
    (y : Fin n → Fv F v ⊗[F] E) :
    coord h a (fun i => c * y i) = toCompl h c • coord h a y := by
  simp only [coord, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

theorem coord_mulVec (h : w.under (𝓞 F) = v) (a : GL (Fin n) (w.adicCompletion E)) (α : GL (Fin n) (Fv F v ⊗[F] E))
    (y : Fin n → Fv F v ⊗[F] E) :
    coord h a (α.1 *ᵥ y) = (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 *ᵥ coord h a y := by
  rw [coord, comp_mulVec, ← mulVec_coord h a y, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Units.val_mul, Units.val_mul]

theorem exists_coord_eq (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (a : GL (Fin n) (w.adicCompletion E)) (z : Fin n → w.adicCompletion E) : ∃ y, coord h a y = z := by
  obtain ⟨y, hy⟩ := (toCompl_bijective hw h).2.comp_left (a.1 *ᵥ z)
  refine ⟨y, ?_⟩
  rw [coord, show toCompl h ∘ y = a.1 *ᵥ z from hy, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

section Main

variable {L : Submodule (𝓞 E) (Fin n → E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {a : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w L a)

def phi : latLoc F L v →ₛₗ[intMap h] (Fin n → w.adicCompletionIntegers E) where
  toFun y i := ⟨coord h a y i, (mem_latLoc_iff_coord hw h ha y).1 y.2 i⟩
  map_add' y y' := funext fun i => Subtype.ext (congrFun (coord_add h a y y') i)
  map_smul' r y := funext fun i => Subtype.ext (congrFun (coord_smul h a r.1 y.1) i)

theorem coe_phi (y : latLoc F L v) (i : Fin n) : (phi hw h ha y i : w.adicCompletion E) = coord h a y i := rfl

include hw ha in
theorem phi_surjective : Function.Surjective (phi hw h ha) := by
  intro z
  obtain ⟨y, hy⟩ := exists_coord_eq hw h a (fun i => (z i : w.adicCompletion E))
  have hm : y ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha y).2 fun i => by rw [hy]; exact (z i).2
  exact ⟨⟨y, hm⟩, funext fun i => Subtype.ext (congrFun hy i)⟩

variable {M : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)} {α : GL (Fin n) (Fv F v ⊗[F] E)}

include hw ha in
theorem integral_entries (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) (i j : Fin n) :
    (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨y, hy⟩ := exists_coord_eq hw h a (Pi.single j 1)
  have hm : y ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha y).2 fun k => by
    rw [hy]
    by_cases e : k = j
    · subst e; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne e]; exact zero_mem _
  have h1 := (mem_latLoc_iff_coord hw h ha _).1 (hM ((hα _).2 ⟨y, hm, rfl⟩)) i
  rw [coord_mulVec, hy, Matrix.mulVec_single_one] at h1
  exact h1

def intMat (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) :
    Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) :=
  Matrix.of fun i j => ⟨_, integral_entries hw h ha hM hα i j⟩

variable (hM : M ≤ latLoc F L v) (hα : ∀ y, y ∈ M ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x)

theorem coe_intMat_mulVec (z : Fin n → w.adicCompletionIntegers E) (i : Fin n) :
    ((intMat hw h ha hM hα *ᵥ z) i : w.adicCompletion E) =
      ((a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 *ᵥ fun j => (z j : w.adicCompletion E)) i := by
  have := RingHom.map_mulVec (w.adicCompletionIntegers E).subtype (intMat hw h ha hM hα) z i
  exact this

theorem submoduleOf_eq :
    M.submoduleOf (latLoc F L v) = (LinearMap.range (intMat hw h ha hM hα).mulVecLin).comap (phi hw h ha) := by
  ext y
  change y.1 ∈ M ↔ _
  rw [hα, Submodule.mem_comap, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨phi hw h ha ⟨x, hx⟩, funext fun i => Subtype.ext ?_⟩
    rw [Matrix.mulVecLin_apply, coe_intMat_mulVec, coe_phi, e, coord_mulVec]
    rfl
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := exists_coord_eq hw h a (fun i => (z i : w.adicCompletion E))
    have hm : x ∈ latLoc F L v := (mem_latLoc_iff_coord hw h ha x).2 fun i => by rw [hx]; exact (z i).2
    refine ⟨x, hm, coord_injective hw h a (funext fun i => ?_)⟩
    rw [coord_mulVec, hx, ← coe_intMat_mulVec hw h ha hM hα, ← coe_phi hw h ha y]
    exact congrArg (fun t => ((t i : w.adicCompletionIntegers E) : w.adicCompletion E)) hz.symm

def quotMap : (latLoc F L v ⧸ M.submoduleOf (latLoc F L v)) →ₛₗ[intMap h]
    ((Fin n → w.adicCompletionIntegers E) ⧸ LinearMap.range (intMat hw h ha hM hα).mulVecLin) :=
  (M.submoduleOf (latLoc F L v)).mapQ _ (phi hw h ha) (submoduleOf_eq hw h ha hM hα).le

theorem quotMap_bijective : Function.Bijective (quotMap hw h ha hM hα) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq => ?_, fun q => ?_⟩
  · induction q using Submodule.Quotient.induction_on with
    | H y =>
      rw [quotMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero, submoduleOf_eq hw h ha hM hα]
      exact hq
  · induction q using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨y, rfl⟩ := phi_surjective hw h ha z
      exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem length_eq_addVal :
    Module.length (intLoc F E v) (latLoc F L v ⧸ M.submoduleOf (latLoc F L v)) =
      IsDiscreteValuationRing.addVal _ (intMat hw h ha hM hα).det := by
  haveI : RingHomSurjective (intMap h) := ⟨intMap_surjective hw h⟩
  rw [← GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det, Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective (quotMap hw h ha hM hα) (quotMap_bijective hw h ha hM hα))

theorem coe_det_intMat :
    ((intMat hw h ha hM hα).det : w.adicCompletion E) = toCompl h (Matrix.GeneralLinearGroup.det α).1 := by
  have h1 := RingHom.map_det (w.adicCompletionIntegers E).subtype (intMat hw h ha hM hα)
  have h2 : (w.adicCompletionIntegers E).subtype.mapMatrix (intMat hw h ha hM hα) =
      (a⁻¹ * Formalism.UG.bc (toCompl h) α * a).1 := Matrix.ext fun i j => rfl
  have h3 : Matrix.GeneralLinearGroup.det (a⁻¹ * Formalism.UG.bc (toCompl h) α * a) =
      Matrix.GeneralLinearGroup.det (Formalism.UG.bc (toCompl h) α) := by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  change (w.adicCompletionIntegers E).subtype _ = _
  rw [h1, h2]
  have h4 := congrArg Units.val h3
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply] at h4
  rw [h4, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Main

theorem ordL_eq_addVal {d : w.adicCompletionIntegers E} (hd : d ≠ 0) :
    ∃ m : ℕ, IsDiscreteValuationRing.addVal _ d = m ∧ Formalism.UG.ordL (d : w.adicCompletion E) = m := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hϖ' : Valued.v ϖ = WithZero.exp (-1) := hϖ
  have hle : ϖ ∈ w.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  let π : w.adicCompletionIntegers E := ⟨ϖ, hle⟩
  have hπ := GlobalTheory.DegreeOneUniformiser.irreducible_of_valued w π hϖ'
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
  refine ⟨m, IsDiscreteValuationRing.addVal_def d u hπ m hu, ?_⟩
  have hc : (d : w.adicCompletion E) = ((u : w.adicCompletionIntegers E) : w.adicCompletion E) * ϖ ^ m := by
    rw [hu, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hv : Valued.v (d : w.adicCompletion E) = WithZero.exp (-(m : ℤ)) := by
    rw [hc, map_mul, map_pow, hϖ', HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit,
      one_mul, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hne : Valued.v (d : w.adicCompletion E) ≠ 0 := by rw [hv]; exact WithZero.exp_ne_zero
  have hz : WithZero.unzero hne = Multiplicative.ofAdd (-(m : ℤ)) :=
    WithZero.coe_inj.1 (by rw [WithZero.coe_unzero, hv]; rfl)
  rw [Formalism.UG.ordL, dite_eq_right hne, hz]
  simp

theorem main_of_abs (habs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v), Formalism.UG.IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ,
    (absEv F E v x : ℝ) = (Formalism.UG.qV F v : ℝ) ^ (-(2 * Formalism.UG.ordL (toCompl h x.1)))) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ L _ v P hP g α hα
  have hw : Formalism.UG.IsInertAt F E v P := hP
  have h : P.under (𝓞 F) = v := (under_eq_iff hw P).2 rfl
  obtain ⟨a, ha⟩ := exists_isFrameAt hw (Submodule.IsLattice.fg E L) (Submodule.IsFullLattice.span_eq_top (A := E) (M := L))
  have hM : latLoc F L v ⊓ latMoved σ J L v g ≤ latLoc F L v := inf_le_left
  have hα' : ∀ y, y ∈ latLoc F L v ⊓ latMoved σ J L v g ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x := fun y => hα y
  have hlen := length_eq_addVal hw h ha hM hα'
  have hdet := coe_det_intMat hw h ha hM hα'
  have hd0 : (intMat hw h ha hM hα').det ≠ 0 := by
    intro e
    rw [e, ZeroMemClass.coe_zero] at hdet
    exact ((Matrix.GeneralLinearGroup.det α).isUnit.map (toCompl h)).ne_zero hdet.symm
  obtain ⟨m, hm1, hm2⟩ := ordL_eq_addVal hd0
  refine ⟨m, hlen.trans hm1, ?_⟩
  have e1 := habs F E σ hσ v P h hw (Matrix.GeneralLinearGroup.det α)
  rw [← hdet, hm2] at e1
  have hq := absNorm_eq hσ.2.2.1 hw
  apply NNReal.eq
  rw [e1, NNReal.coe_zpow, hq, Formalism.UG.qV]
  push_cast
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem absEv_det_eq_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) :=
  main_of_abs GlobalTheory.AbsInert.absEv_inert

end GlobalTheory.InertLatLength
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetInertPlaceLatticeLengthStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingNorm_det_inertPlace_lattice_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) := by
  first | exact @GlobalTheory.InertLatLength.absEv_det_eq_of_inert | exact GlobalTheory.InertLatLength.absEv_det_eq_of_inert | (intros; apply GlobalTheory.InertLatLength.absEv_det_eq_of_inert <;> assumption)
end
end

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

namespace GlobalTheory.GraphNorm

private theorem pairVec_finSumFinEquiv_injective_eq {X : Type} {n : ℕ} {a b c d : Fin n → X}
    (h : pairVec finSumFinEquiv a b = pairVec finSumFinEquiv c d) : a = c ∧ b = d := by
  constructor
  · funext i
    have h' := congrFun h (finSumFinEquiv (.inl i))
    simpa only [pairVec_inl] using h'
  · funext i
    have h' := congrFun h (finSumFinEquiv (.inr i))
    simpa only [pairVec_inr] using h'
theorem unitaryLocalPoint_latticeGraphNorm_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) (g : GLoc σ J v) (p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) (k : GLoc σ (dblGram finSumFinEquiv J) v), k ∈ KFin σ (dblGram finSumFinEquiv J) L v → ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k → ∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = (leviOf finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)) p).1 *ᵥ x := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v g p k hk hpk y
  simp only [KFin] at hk
  unfold GlobalTheory.AdelicU.stabLoc at hk
  rw [Subgroup.mem_comap, latLoc_sumLat] at hk
  simp only [Formalism.UG.stabGL, Subgroup.mem_mk, Set.mem_setOf_eq, Submonoid.mem_mk, Subsemigroup.mem_mk] at hk
  have hmat : (matHom (Fv F v) σ (dblGram finSumFinEquiv J) (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *
      (matHom (Fv F v) σ (dblGram finSumFinEquiv J) k).1 =
      blkMat finSumFinEquiv (matHom (Fv F v) σ J g).1 1 := by
    have h1 := congrArg (fun x => (matHom (Fv F v) σ (dblGram finSumFinEquiv J) x).1) hpk
    simp only [map_mul, Units.val_mul, matHom_ioH, val_blkGL, map_one, Units.val_one] at h1
    exact h1.symm
  have hkd : KeepsDiag finSumFinEquiv
      (matHom (Fv F v) σ (dblGram finSumFinEquiv J) (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 :=
    mem_siegelOf.mp p.2
  have hkdi : KeepsDiag finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)
      ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) : GLoc σ (dblGram finSumFinEquiv J) v)).1 :=
    mem_siegelOf.mp (p⁻¹).2
  have hPinv : matHom (Fv F v) σ (dblGram finSumFinEquiv J)
      ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) : GLoc σ (dblGram finSumFinEquiv J) v) =
      (matHom (Fv F v) σ (dblGram finSumFinEquiv J) (p : GLoc σ (dblGram finSumFinEquiv J) v))⁻¹ := by
    rw [Subgroup.coe_inv, map_inv]
  rw [val_leviOf, mem_latMoved]
  set M := matHom (Fv F v) σ (dblGram finSumFinEquiv J) with hM
  set mJ := matHom (Fv F v) σ J with hmJ
  set S := sumLat finSumFinEquiv (latLoc F L v) (latLoc F L v) with hS
  constructor
  · rintro ⟨hy, hyg⟩
    have hw : pairVec finSumFinEquiv ((mJ g⁻¹).1 *ᵥ y) y ∈ S :=
      (pairVec_mem_sumLat finSumFinEquiv).mpr ⟨hyg, hy⟩
    have hz := (hk _).mp hw
    have hPz : (M (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ ((M k).1 *ᵥ pairVec finSumFinEquiv ((mJ g⁻¹).1 *ᵥ y) y) =
        pairVec finSumFinEquiv y y := by
      rw [Matrix.mulVec_mulVec, hmat, blkMat_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
        ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
    have hz_eq : (M k).1 *ᵥ pairVec finSumFinEquiv ((mJ g⁻¹).1 *ᵥ y) y =
        pairVec finSumFinEquiv (leviMat finSumFinEquiv (M ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) :
          GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ y)
          (leviMat finSumFinEquiv (M ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) :
          GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ y) := by
      rw [← hkdi.mulVec_diag, ← hPz, Matrix.mulVec_mulVec, hPinv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hz_eq, pairVec_mem_sumLat] at hz
    refine ⟨_, hz.1, ?_⟩
    have hd := hkd.mulVec_diag (leviMat finSumFinEquiv (M ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) :
          GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ y)
    rw [← hz_eq, hPz] at hd
    exact (pairVec_finSumFinEquiv_injective_eq hd).1
  · rintro ⟨x, hx, rfl⟩
    have hxx : pairVec finSumFinEquiv x x ∈ S := (pairVec_mem_sumLat finSumFinEquiv).mpr ⟨hx, hx⟩
    obtain ⟨u, hu⟩ : ∃ u, u = (M k⁻¹).1 *ᵥ pairVec finSumFinEquiv x x := ⟨_, rfl⟩
    have hKu : (M k).1 *ᵥ u = pairVec finSumFinEquiv x x := by
      rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.one_mulVec]
    have huS : u ∈ S := (hk u).mpr (hKu ▸ hxx)
    have hsplit := (pairVec_eta finSumFinEquiv u).symm
    have hPKu : blkMat finSumFinEquiv (mJ g).1 1 *ᵥ u =
        pairVec finSumFinEquiv (leviMat finSumFinEquiv (M (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ x)
          (leviMat finSumFinEquiv (M (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ x) := by
      rw [← hmat, ← Matrix.mulVec_mulVec, hKu, hkd.mulVec_diag]
    rw [hsplit, blkMat_mulVec, Matrix.one_mulVec] at hPKu
    obtain ⟨h1, h2⟩ := pairVec_finSumFinEquiv_injective_eq hPKu
    rw [hsplit, pairVec_mem_sumLat] at huS
    refine ⟨h2 ▸ huS.2, ?_⟩
    rw [← h1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
    exact huS.1
private theorem exists_isElemDiv {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (x : GL (Fin n) (Fv F v)) : ∃ d : Fin n → (Fv F v)ˣ, IsElemDiv x d := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  have hϖ0 : ((π : F) : v.adicCompletion F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hmem : ((π : F) : v.adicCompletion F) ∈ Formalism.UG.Ov F v := by
    show _ ∈ v.adicCompletionIntegers F
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hv, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, hx⟩ := Formalism.UG.Final.CartanDecomp F v n _ hmem hv x
  refine ⟨fun i => Units.mk0 (((π : F) : v.adicCompletion F) ^ (a i)) (zpow_ne_zero _ hϖ0), k₁, hk₁, k₂, hk₂, ?_⟩
  rw [hx]
  rfl
private theorem min_self_inv_le_one (a : ℝ≥0) : min a a⁻¹ ≤ 1 := by
  rcases le_total a 1 with h1 | h1
  · exact (min_le_left _ _).trans h1
  · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h1)
private theorem natCast_zpow_neg_le_one (N l : ℕ) (hN : 1 ≤ N) : ((N : ℝ≥0)) ^ (-(l : ℤ)) ≤ 1 := by
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hN))

theorem graphNormFinite : GraphNormFinite := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hSD
  refine ⟨?_, ?_⟩
  · intro τ β hβ g
    obtain ⟨p, k, hk, hpk⟩ := GlobalTheory.T.graph_element_iwasawa_split_place F E σ h n J hJ L v hSD ⟨τ⟩ g
    have hlat := unitaryLocalPoint_latticeGraphNorm_identity F E σ h n J hJ L v g p k hk hpk
    have hgr : graphHgt σ J L v g = absEv F E v (Matrix.GeneralLinearGroup.det
        (leviOf finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)) p)) := by
      rw [graphHgt, hpk, hgtFin_mul p hk]
      rfl
    refine ⟨exists_isElemDiv _, ?_, ?_⟩
    · intro d hd
      rw [hgr]
      exact GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection F E σ h n J hJ L v hSD τ β hβ g _ hlat d hd
    · obtain ⟨d, hd⟩ := exists_isElemDiv (splitEquivIn h hJ τ β g)
      rw [hgr, GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection F E σ h n J hJ L v hSD τ β hβ g _ hlat d hd]
      exact Finset.prod_le_one₀ (fun _ _ => by positivity) (fun i _ => min_self_inv_le_one _)
  · intro P hP g
    obtain ⟨p, k, hk, hpk⟩ := GlobalTheory.T.graph_element_iwasawa_inert_place F E σ h n J hJ L v hSD P hP g
    have hlat := unitaryLocalPoint_latticeGraphNorm_identity F E σ h n J hJ L v g p k hk hpk
    have hgr : graphHgt σ J L v g = absEv F E v (Matrix.GeneralLinearGroup.det
        (leviOf finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)) p)) := by
      rw [graphHgt, hpk, hgtFin_mul p hk]
      rfl
    obtain ⟨l, hl1, hl2⟩ := GlobalTheory.T.doublingNorm_det_inertPlace_lattice_length F E σ h n J hJ L v P hP g _ hlat
    refine ⟨⟨l, hl1, hgr.trans hl2⟩, ?_⟩
    rw [hgr, hl2]
    apply natCast_zpow_neg_le_one
    exact Nat.one_le_iff_ne_zero.mpr (fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))

end GlobalTheory.GraphNorm

end

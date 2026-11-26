module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenExhaustionStabilizes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.UnitarisableLocalReps.IsUnitarisableLocRep
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.UnitaryBC
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace PositivityTheory.PRW.SatakeDual

section Transport

variable {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {n : ℕ}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

theorem star_Tj (ϖ : w.adicCompletion F) (j : ℕ) (g : GL (Fin n) (w.adicCompletion F)) :
    starRingEnd ℂ (Tj ℂ n (Ov F w) ϖ j g) = Tj ℂ n (Ov F w) ϖ j g := by
  unfold Tj Set.indicator
  split_ifs <;> simp

theorem isSatVecGL_of_conj (ρ₁ : Representation ℂ (GL (Fin n) (w.adicCompletion F)) V₁)
    (ρ₂ : Representation ℂ (GL (Fin n) (w.adicCompletion F)) V₂) (D : V₂ →+ V₁) (hinj : Function.Injective D)
    (hsmul : ∀ (c : ℂ) v, D (c • v) = starRingEnd ℂ c • D v) (hρ : ∀ g v, D (ρ₂ g v) = ρ₁ g (D v)) {y : V₂}
    {B : Multiset ℂˣ} (hy0 : y ≠ 0) (hyf : y ∈ fixed ρ₂ (KGL w (n := n))) (h : IsSatVecGL w ρ₁ (D y) B) :
    IsSatVecGL w ρ₂ y (B.map star) := by
  refine ⟨hy0, hyf, by rw [Multiset.card_map, h.2.2.1], fun ϖ hϖ j hj => hinj ?_⟩
  have hfin := finite_heckeVec (Final.GLintComm F w n) (Tj_mem_hecke hϖ j) ρ₂ y
  rw [hsmul, UnitaryParam.satEig_map_star, Complex.conj_conj, ← h.2.2.2 ϖ hϖ j hj, heckeVec,
    D.map_finsum hfin, heckeVec]
  refine finsum_congr fun c => ?_
  rw [hsmul, hρ, star_Tj]

end Transport

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem invA_invA (g : GA E a) : PositivityTheory.PRW.GKD.invA E a (PositivityTheory.PRW.GKD.invA E a g) = g := by
  have h := (GlobalTheory.DiscreteUnit.transInv (Ad E) a).left_inv g
  exact (congrArg (GlobalTheory.DiscreteUnit.transInv (Ad E) a) (Units.ext rfl : PositivityTheory.PRW.GKD.invA E a g =
    GlobalTheory.DiscreteUnit.transInv (Ad E) a g)).trans ((Units.ext rfl).trans h)

theorem act_val (o : Op E a) {y ψ : Sm E a} (hy : ∀ g, y.1 g = star (ψ.1 (invT a (Ad E) g))) (g : GA E a) :
    (act o y).1 g = star ((act (invTOp o) ψ).1 (invT a (Ad E) g)) := by
  cases o with
  | fin k =>
    change y.1 (g * finGL E a k) = star (ψ.1 (invT a (Ad E) g * finGL E a (invT a (Af E) k)))
    rw [hy, map_mul, GlobalTheory.CompanionTheory.DualAct.invT_finGL]
  | cpt k =>
    change y.1 (g * infGL E a (Unitary.toUnits k)) =
      star (ψ.1 (invT a (Ad E) g * infGL E a (Unitary.toUnits (barK k))))
    rw [hy, map_mul, GlobalTheory.CompanionTheory.DualAct.invT_infGL, GlobalTheory.CompanionTheory.DualAct.invT_toUnits]
  | lie X =>
    have e : y.1 = fun g => star (ψ.1 (invT a (Ad E) g)) := funext hy
    change lieD X y.1 g = star (lieD (toL (-(Matrix.of X)ᵀ)) ψ.1 (invT a (Ad E) g))
    rw [e, GlobalTheory.CompanionTheory.DualAct.lieD_star_invT X ψ.2 g]

abbrev invW (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) : GL (Fin a) (w.adicCompletion E) ≃* GL (Fin a) (w.adicCompletion E) :=
  ConjPlace.invT (RingEquiv.refl (w.adicCompletion E)) a

omit [_root_.NumberField.IsTotallyComplex E] in
theorem invW_invW (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) : invW w a (invW w a g) = g :=
  Units.ext (Matrix.ext fun i j => by
    rw [ConjPlace.invT_val, ← map_inv, ConjPlace.invT_val, inv_inv]; rfl)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem invW_symm (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) : (invW w a).symm g = invW w a g :=
  (MulEquiv.symm_apply_eq _).2 (invW_invW w g).symm


omit [_root_.NumberField.IsTotallyComplex E] in
theorem invT_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    invT a (Af E) (locGL E a w g) = locGL E a w ((invW w a).symm g) := by
  rw [invW_symm]
  calc invT a (Af E) (locGL E a w g) = GlobalTheory.DiscreteUnit.transInv (Af E) a (cornerGL a (sLoc E w) g) := Units.ext rfl
    _ = cornerGL a (sLoc E w) (GlobalTheory.DiscreteUnit.transInv _ a g) := (GlobalTheory.DiscreteUnit.cornerGL_transInv _ g).symm
    _ = locGL E a w (invW w a g) := congrArg (cornerGL a (sLoc E w)) (Units.ext (Matrix.ext fun i j =>
        (ConjPlace.invT_val (RingEquiv.refl (w.adicCompletion E)) g i j).symm))

theorem isUnitarisable_locRep (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : IsNormalised π)
    (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.LGrp.IsUnitarisable (π.locRep w) := by
  classical
  have := GlobalTheory.DiscreteUnit.countable_latticeGL (E := E) (N := a)
  have : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (GA E a), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  have := (GlobalTheory.CovolGL.finvol E a μ).1
  have hc : ∀ φ ∈ π.V, Continuous φ.1 := fun φ hφ =>
    GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level
  have hsq : ∀ φ ∈ π.V, IsSqInt φ.1 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hB E a φ (π.cusp φ hφ) (fun t g => by rw [hπ φ hφ t g])
    have hl := GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL (π.cusp φ hφ).1.left (hπ φ hφ)
    exact (GlobalTheory.CuspRep.CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (hc φ hφ) (π.cusp φ hφ).1.left (hπ φ hφ)).1
      (GlobalTheory.CuspQuot.memL2_of_bound (μ := μ) (hc φ hφ) hl hC)
  refine GlobalTheory.DiscreteUnit.isUnitarisable_of_embedding (Γ := latticeGL E a) (π.locRep w)
    (fun g => finGL E a (locGL E a w g)) (fun g => ?_) ((Sm E a).subtype.comp π.V.subtype)
    (Subtype.val_injective.comp Subtype.val_injective) (fun v => hc v.1 v.2)
    (fun v => GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL (π.cusp v.1 v.2).1.left (hπ v.1 v.2))
    (fun v => (hsq v.1 v.2).2) fun h v g => rfl
  exact GlobalTheory.DiscreteUnit.modular_eq_one ((finGL E a).comp (locGL E a w))
    (fun g => (congrArg (finGL E a) (GlobalTheory.DiscreteUnit.cornerGL_transInv (sLoc E w) g)).trans
      (GlobalTheory.DiscreteUnit.cornerGL_transInv (sFin E) _)) g

theorem hasSat_dual (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : IsNormalised π) (σ : CuspSub E a)
    (hσ : ∀ ψ : Sm E a, ψ ∈ σ.V ↔ ∃ φ ∈ π.V, ψ.1 = fun g => star (φ.1 (PositivityTheory.PRW.GKD.invA E a g)))
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (h : (CG.mk π).HasSat w B) :
    (CG.mk σ).HasSat w B := by
  classical
  rw [CG.hasSat_mk] at h ⊢
  obtain ⟨hsph, hall⟩ := h

  have hex : ∀ y : σ.V, ∃ φ : π.V, ∀ g, y.1.1 g = star (φ.1.1 (invT a (Ad E) g)) := fun y => by
    obtain ⟨φ, hφ, e⟩ := (hσ y.1).1 y.2
    exact ⟨⟨φ, hφ⟩, fun g => congrFun e g⟩
  choose Df hDf using hex
  have hDv : ∀ y h, (Df y).1.1 h = star (y.1.1 (invT a (Ad E) h)) := fun y h => by
    rw [hDf y, invA_invA, star_star]
  have hDext : ∀ x x' : π.V, (∀ h, x.1.1 h = x'.1.1 h) → x = x' := fun x x' e =>
    Subtype.ext (Subtype.ext (funext e))
  let D : σ.V →+ π.V :=
    { toFun := Df
      map_zero' := hDext _ _ fun h => by
        rw [hDv]
        change star ((0 : Sm E a).1 _) = (0 : Sm E a).1 h
        simp
      map_add' := fun y y' => hDext _ _ fun h => by
        rw [hDv]
        change star (y.1.1 _ + y'.1.1 _) = (Df y).1.1 h + (Df y').1.1 h
        rw [hDv, hDv]
        exact star_add _ _ }
  have hD : ∀ y, D y = Df y := fun _ => rfl
  have hinj : Function.Injective D := fun y y' e => by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    rw [hDf y, hDf y', ← hD, ← hD, e]
  have hsmul : ∀ (c : ℂ) y, D (c • y) = starRingEnd ℂ c • D y := fun c y => hDext _ _ fun h => by
    simp only [hD]
    rw [hDv]
    change _ = starRingEnd ℂ c * (Df y).1.1 h
    rw [hDv]
    change star (c * y.1.1 _) = _
    rw [star_mul']; rfl
  have hop : ∀ o y, D (σ.op o y) = π.op (invTOp o) (D y) := fun o y => hDext _ _ fun h => by
    simp only [hD]
    rw [hDv]
    change star ((act o y.1).1 _) = (act (invTOp o) (Df y).1).1 h
    rw [act_val o (hDf y), invA_invA, star_star]

  have hsurj : Function.Surjective D := by
    let S : Submodule ℂ (Sm E a) :=
      { carrier := {φ | ∃ y : σ.V, ∀ g, y.1.1 g = star (φ.1 (invT a (Ad E) g))}
        add_mem' := fun {φ φ'} ⟨y, hy⟩ ⟨y', hy'⟩ => ⟨y + y', fun g => by
          change y.1.1 g + y'.1.1 g = _
          rw [hy, hy']
          exact (star_add _ _).symm⟩
        zero_mem' := ⟨0, fun g => by simp⟩
        smul_mem' := fun c {φ} ⟨y, hy⟩ => ⟨starRingEnd ℂ c • y, fun g => by
          change starRingEnd ℂ c * y.1.1 g = _
          rw [hy]
          change _ = star (c * φ.1 _)
          rw [star_mul']; rfl⟩ }
    have hle : S ≤ π.V := fun φ ⟨y, hy⟩ => by
      have e : φ = (Df y).1 := Subtype.ext (funext fun h => by rw [hDv, hy, invA_invA, star_star])
      rw [e]
      exact (Df y).2
    have hst : _root_.GlobalTheory.CuspRep.IsStable S := fun o φ ⟨y, hy⟩ => ⟨σ.op (invTOp o) y, fun g => by
      change (act (invTOp o) y.1).1 g = _
      rw [act_val (invTOp o) hy, GlobalTheory.CsdBack.invTOp_involutive o]⟩
    have hne : S ≠ ⊥ := by
      obtain ⟨ψ, hψ, h0⟩ := (Submodule.ne_bot_iff _).1 σ.ne_bot
      refine (Submodule.ne_bot_iff _).2 ⟨(Df ⟨ψ, hψ⟩).1, ⟨⟨ψ, hψ⟩, hDf _⟩, fun e => h0 ?_⟩
      refine Subtype.ext (funext fun g => ?_)
      change ψ.1 g = 0
      rw [show ψ.1 g = (⟨ψ, hψ⟩ : σ.V).1.1 g from rfl, hDf, e]
      simp
    have hS : S = π.V := (π.irred S hle hst).resolve_left hne
    intro x
    have hx : x.1 ∈ S := by rw [hS]; exact x.2
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hDext _ _ fun h => by rw [hD, hDv, hy, invA_invA, star_star]⟩

  have hρ : ∀ g y, D (σ.locRep w g y) = ((π.locRep w).comp (invW w a).symm.toMonoidHom) g (D y) := fun g y => by
    rw [CuspSub.locRep_eq, hop]
    change π.op (.fin (invT a (Af E) (locGL E a w g))) (D y) = _
    rw [invT_locGL]
    rfl
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hK : ∀ g, g ∈ KGL w (n := a) ↔ invW w a g ∈ KGL w (n := a) :=
    ConjPlace.mem_iff_invT (n := a) c (ConjPlace.map_mem_Ov_iff c hc)
  have hfix : ∀ y : σ.V, y ∈ fixed (σ.locRep w) (KGL w (n := a)) ↔ D y ∈ fixed (π.locRep w) (KGL w (n := a)) := fun y => by
    rw [GlobalTheory.LGrp.mem_fixed, GlobalTheory.LGrp.mem_fixed]
    constructor
    · intro hy k hk
      have e := hρ (invW w a k) y
      rw [hy _ ((hK k).1 hk), MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at e
      exact e.symm
    · intro hx k hk
      apply hinj
      rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, invW_symm]
      exact hx _ ((hK k).1 hk)

  obtain ⟨x₀, hx₀f, hx₀⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hBB := UnitaryParam.map_star_eq_map_inv E w a π.V (π.locRep w) x₀ B (isUnitarisable_locRep hB hπ w)
    (hall x₀ hx₀f hx₀)
  have hBf : (B.map (·⁻¹)).map star = B := by
    rw [Multiset.map_map]
    have e : (star ∘ fun b : ℂˣ => b⁻¹) = (fun b : ℂˣ => b⁻¹) ∘ star := funext fun b => star_inv b
    rw [e, ← Multiset.map_map, hBB, Multiset.map_map]
    simp
  have hD0 : ∀ y, D y = 0 → y = 0 := fun y e => hinj (e.trans D.map_zero.symm)
  refine ⟨?_, fun y hyf hy0 => ?_⟩
  · obtain ⟨y₀, rfl⟩ := hsurj x₀
    exact (Submodule.ne_bot_iff _).2 ⟨y₀, (hfix y₀).2 hx₀f, fun e => hx₀ (by rw [e, D.map_zero])⟩
  · have hxy := hall (D y) ((hfix y).1 hyf) fun e => hy0 (hD0 y e)
    have h1 := ConjPlace.isSatVecGL_invT c hc rfl hxy
    have h2 := isSatVecGL_of_conj _ (σ.locRep w) D hinj hsmul hρ hy0 hyf h1
    rwa [hBf] at h2

end PositivityTheory.PRW.SatakeDual

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormConjugateInverse
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormConjugateInverse
noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open PositivityTheory.PRW.GKD GlobalTheory.SmGL GlobalTheory.ThetaPull

namespace GlobalTheory.CompanionTheory.DualCusp

section Semilinear

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem qdet_semilinear {n : ℕ} (D : V →ₗ⋆[ℂ] V) (X Y : Fin n → Fin n → Module.End ℂ V)
    (h : ∀ i j v, Y i j (D v) = D (X i j v)) (u : ℂ) (v : V) :
    Formalism.REAL.qdet Y (star u) (D v) = D (Formalism.REAL.qdet X u v) := by
  have hp : ∀ {t : ℕ} (x y : Fin t → Module.End ℂ V), (∀ k v, y k (D v) = D (x k v)) →
      ∀ v, (List.ofFn y).prod (D v) = D ((List.ofFn x).prod v) := by
    intro t
    induction t with
    | zero => intro x y _ v; simp
    | succ t ih =>
      intro x y h v
      simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
      rw [ih _ _ (fun k => h k.succ), h]
  have hT : ∀ (w : ℂ) (i j : Fin n) (v : V),
      Formalism.REAL.Tm Y (star w) i j (D v) = D (Formalism.REAL.Tm X w i j v) := by
    intro w i j v
    simp only [Formalism.REAL.Tm, LinearMap.add_apply, map_add (f := _), h]
    split_ifs
    · simp [Module.algebraMap_end_apply]
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul]
  congr 1
  refine hp _ _ (fun k v => ?_) v
  have := hT (u - (k : ℂ)) (id (σ k)) (id k) v
  simpa using this

end Semilinear

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def dual : Sm E a →ₗ⋆[ℂ] Sm E a where
  toFun φ := ⟨fun g => star (φ.1 (invA E a g)), GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm φ.2⟩
  map_add' φ ψ := Subtype.ext (funext fun g => by simp)
  map_smul' c φ := Subtype.ext (funext fun g => by simp)

theorem dual_apply (φ : Sm E a) (g : GA E a) : (dual E a φ).1 g = star (φ.1 (invA E a g)) := rfl

theorem dual_dual (φ : Sm E a) : dual E a (dual E a φ) = φ :=
  Subtype.ext (funext fun g => by simp [dual_apply, invA_invA])

theorem dual_injective : Function.Injective (dual E a) :=
  Function.LeftInverse.injective (g := dual E a) dual_dual

theorem act_dual (o : Op E a) (φ : Sm E a) : act o (dual E a φ) = dual E a (act (invTOp o) φ) :=
  GlobalTheory.CompanionTheory.DualAct.act_star_invT o φ _ _ (fun _ => rfl) (fun _ => rfl)

theorem lieS_dual (i j : Fin a) (x : Cinf E) (φ : Sm E a) :
    lieS E a i j x (dual E a φ) = -dual E a (lieS E a j i x φ) := by
  have h := act_dual (.lie (toL (Matrix.single i j x))) φ
  have e : (toL (-(Matrix.of (toL (Matrix.single i j x)))ᵀ) : Lie E a) = -toL (Matrix.single j i x) := by
    change toL (-(Matrix.single i j x)ᵀ) = _
    rw [Matrix.transpose_single]
    rfl
  change lie E a _ _ = dual E a (lie E a (toL (-(Matrix.of (toL (Matrix.single i j x)))ᵀ)) φ) at h
  rw [e, map_neg, LinearMap.neg_apply, map_neg] at h
  exact h

theorem Eop_dual (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (dual E a φ) = dual E a ((-Eop (ComplexEmbedding.conjugate τ) j i) φ) := by
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  have c2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact Complex.conj_ofReal _
  simp only [Eop, e1, e2, map_neg, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, lieS_dual,
    map_smulₛₗ, map_sub, c2, Complex.conj_I, neg_neg, smul_neg]
  module

theorem cap_dual (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (dual E a φ) =
      dual E a (((-1 : ℂ) ^ a • cap (a := a) (ComplexEmbedding.conjugate τ) (-star u) : Module.End ℂ (Sm E a)) φ) := by
  have h := qdet_semilinear (dual E a) (fun i j => -Eop (ComplexEmbedding.conjugate τ) j i) (Eop τ)
    (fun i j v => Eop_dual τ i j v) (star u + ((a : ℂ) - 1) / 2) φ
  have e : star (star u + ((a : ℂ) - 1) / 2) = u + ((a : ℂ) - 1) / 2 := by simp
  have e' : (a : ℂ) - 1 - (star u + ((a : ℂ) - 1) / 2) = -star u + ((a : ℂ) - 1) / 2 := by ring
  rw [e, (GlobalTheory.CapelliNegT.glRel_negT_and_qdet _ a _ (glRel_Eop (ComplexEmbedding.conjugate τ))).2, e', ← cap, ← cap] at h
  exact h

theorem Zalg_dual {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (dual E a φ) = dual E a (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Subalgebra.smul_mem _ (Algebra.subset_adjoin (by exact ⟨_, _, rfl⟩)) _, cap_dual τ u⟩
  | algebraMap c =>
    exact ⟨algebraMap ℂ _ (star c), Subalgebra.algebraMap_mem _ _, fun φ => by
      simp [Module.algebraMap_end_apply, map_smulₛₗ]⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

theorem finiteDimensional_map (S : Submodule ℂ (Sm E a)) (hS : FiniteDimensional ℂ S) :
    FiniteDimensional ℂ (S.map (dual E a)) := by
  obtain ⟨s, rfl⟩ := (Submodule.fg_iff_finiteDimensional S).2 hS
  rw [Submodule.map_span]
  exact (Submodule.fg_iff_finiteDimensional _).1 (Submodule.fg_span (s.finite_toSet.image _))

theorem continuous_invT {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invT a R) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · change Continuous fun g : GL (Fin a) R => (g⁻¹).val j i
    exact Units.continuous_coe_inv.matrix_elem _ _
  · change Continuous fun g : GL (Fin a) R => g.val j i
    exact Units.continuous_val.matrix_elem _ _

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_toL_transpose_le (M : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL Mᵀ‖ ≤ ‖toL M‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
    (norm_le_pi_norm (toL M j) i).trans (norm_le_pi_norm (toL M) j)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_invT_le (y : GL (Fin a) (Cinf E)) : height (invT a (Cinf E) y) ≤ height y := by
  have h1 : ‖toL (invT a (Cinf E) y).val‖ ≤ ‖toL (y⁻¹).val‖ := norm_toL_transpose_le (y⁻¹).val
  have h2 : ‖toL ((invT a (Cinf E) y)⁻¹).val‖ ≤ ‖toL y.val‖ := norm_toL_transpose_le y.val
  unfold height
  linarith


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_invT (y : GL (Fin a) (Cinf E)) : height (invT a (Cinf E) y) = height y := by
  refine le_antisymm (height_invT_le y) ?_
  have h := height_invT_le (invT a (Cinf E) y)
  have e : invT a (Cinf E) (invT a (Cinf E) y) = y := Units.ext (Matrix.transpose_transpose y.val)
  rwa [e] at h

theorem isAutForm_dual {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (dual E a φ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    rw [dual_apply, dual_apply, map_mul]
    have e : invA E a (ratGL E a γ) = ratGL E a (invT a E γ) :=
      (GlobalTheory.CompanionTheory.DualAct.map_invT (algebraMap E (Ad E)) γ).symm
    rw [e, h.left]
  · convert h.level.preimage (continuous_invT (a := a) (R := Af E)) using 1
    ext k
    exact (Eq.congr_left (act_dual (.fin k) φ)).trans dual_injective.eq_iff
  · have := h.kfin
    have := finiteDimensional_map _ this
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      (dual E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_dual (.cpt k) φ).symm⟩
  · have := finiteDimensional_map _ h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (dual E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_dual hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  · intro g
    obtain ⟨C, N, h1⟩ := h.growth (invA E a g)
    refine ⟨C, N, fun y => ?_⟩
    have e : (dual E a φ).1 (g * infGL E a y) =
        star (φ.1 (invA E a g * infGL E a (invT a (Cinf E) y))) := by
      rw [dual_apply, map_mul, GlobalTheory.CompanionTheory.DualAct.invT_infGL]
    have h2 := h1 (invT a (Cinf E) y)
    rw [height_invT] at h2
    rw [e, norm_star]
    exact h2


omit [_root_.NumberField.IsTotallyComplex E] in
theorem phiU_eq : PhiU a (Ad E) = ratGL E a (PhiU a E) := by
  ext i j
  change GlobalTheory.Tw.Phi a (Ad E) i j = algebraMap E (Ad E) (GlobalTheory.Tw.Phi a E i j)
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem invA_eq (g : GA E a) :
    invA E a g = (PhiU a (Ad E))⁻¹ * thetaGL a (RingHom.id (Ad E)) g * PhiU a (Ad E) := by
  have e : GeneralLinearGroup.map (RingHom.id (Ad E)) g = g := by
    ext i j
    rfl
  change _ = (PhiU a (Ad E))⁻¹ * (PhiU a (Ad E) * invT a (Ad E) (GeneralLinearGroup.map (RingHom.id (Ad E)) g) *
    (PhiU a (Ad E))⁻¹) * PhiU a (Ad E)
  rw [e]
  group

omit [_root_.NumberField.IsTotallyComplex E] in
theorem blockMap_id_mem_ratN {r s : ℕ} (h : r + s = a) {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) :
    blockMap h (RingHom.id (Ad E)) x ∈ ratN E a s := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨blockMap h (RingHom.id E) y, funext fun p => ?_⟩
  change algebraMap E (Ad E) (_ * (-y _)) = _ * (-algebraMap E (Ad E) _)
  rw [map_mul, map_neg, map_pow, map_neg, map_one]

theorem isCuspidal_dual {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g) (hφ : IsCuspidal φ) :
    IsCuspidal fun g => star (φ (invA E a g)) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  obtain ⟨s, h⟩ : ∃ s, r + s = a := ⟨a - r, by omega⟩
  have h' : s + r = a := by omega
  let c := RingHom.id (Ad E)
  let β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a s → Ad E) :=
    { toFun := blockMap h c
      invFun := blockMap h' c
      left_inv := blockMap_blockMap h h' _ fun _ => rfl
      right_inv := blockMap_blockMap h' h _ fun _ => rfl
      map_add' := map_add _
      continuous_toFun := continuous_blockMap h _ continuous_id
      continuous_invFun := continuous_blockMap h' _ continuous_id }
  let e : ratN E a s ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, blockMap_id_mem_ratN h' y.2⟩
      invFun := fun x => ⟨β x, blockMap_id_mem_ratN h x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  borelize (BlockIx a s → Ad E)
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ s (by omega) (by omega) (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply]) (PhiU a (Ad E) * invA E a g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  have e1 : ∀ x : BlockIx a r → Ad E,
      φ (invA E a (unip x * g)) = φ (unip (m x) * (PhiU a (Ad E) * invA E a g)) := fun x => by
    have hm : unip (m x) = thetaGL a c (unip x) := (thetaGL_unip h c x).symm
    rw [map_mul, invA_eq (unip x), hm, phiU_eq, ← map_inv, mul_assoc, mul_assoc, hl, ← mul_assoc]
  have h3 : ∫ x in 𝓕, φ (invA E a (unip x * g)) ∂μ = 0 := by
    rw [← h2]
    congr 1
    funext x
    exact e1 x
  change ∫ x in 𝓕, (starRingEnd ℂ) (φ (invA E a (unip x * g))) ∂μ = 0
  rw [integral_conj, h3, map_zero]

end GlobalTheory.CompanionTheory.DualCusp


open GlobalTheory.CompanionTheory.DualCusp in
theorem GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (φ : Sm E a) (hψ : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a) (h : IsCuspForm φ) :
    IsCuspForm (⟨fun g => star (φ.1 (invA E a g)), hψ⟩ : Sm E a) :=
  ⟨isAutForm_dual h.1, isCuspidal_dual h.1.left h.2⟩

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormConjugateInverseStatement
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_conjugate_inverse : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (φ : Sm E a) (hψ : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a), IsCuspForm φ → IsCuspForm (⟨fun g => star (φ.1 (invA E a g)), hψ⟩ : Sm E a) := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | exact GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | (intros; apply GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugateInverseRightAction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugateInverseRightAction
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD

noncomputable section

namespace GlobalTheory.CompanionTheory.DualMapAct

theorem act_dual : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (o : Op E a) (φ : Sm E a)
    (h1 : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a)
    (h2 : (fun g => star ((act (invTOp o) φ).1 (invA E a g))) ∈ Sm E a),
    act o (⟨fun g => star (φ.1 (invA E a g)), h1⟩ : Sm E a) =
      ⟨fun g => star ((act (invTOp o) φ).1 (invA E a g)), h2⟩ :=
  fun o φ _ _ => GlobalTheory.CompanionTheory.DualAct.act_star_invT o φ _ _ (fun _ => rfl) (fun _ => rfl)

end GlobalTheory.CompanionTheory.DualMapAct

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugateInverseRightActionStatement
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_inverse_right_action : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (o : Op E a) (φ : Sm E a) (h1 : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a) (h2 : (fun g => star ((act (invTOp o) φ).1 (invA E a g))) ∈ Sm E a), act o (⟨fun g => star (φ.1 (invA E a g)), h1⟩ : Sm E a) = ⟨fun g => star ((act (invTOp o) φ).1 (invA E a g)), h2⟩ := by
  first | exact @GlobalTheory.CompanionTheory.DualMapAct.act_dual | exact GlobalTheory.CompanionTheory.DualMapAct.act_dual | (intros; apply GlobalTheory.CompanionTheory.DualMapAct.act_dual <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasDerivAtLpOfDominated
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil Filter Topology
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve

theorem lp_two_norm_sq {E : Type*} [MeasurableSpace E] {μ : Measure E} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  simp_rw [inner_self_eq_norm_sq]

theorem hasDerivAt_Lp_of_dominated {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (F : ℝ → Lp ℂ 2 μ) (G : Lp ℂ 2 μ) (f f' : ℝ → E → ℂ) (b : E → ℝ) (t₀ δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ t, F t =ᵐ[μ] f t) (hG : G =ᵐ[μ] f' t₀) (hb : MemLp b 2 μ)
    (hd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, HasDerivAt (fun s => f s x) (f' t x) t)
    (hbd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, ‖f' t x‖ ≤ b x) :
    HasDerivAt F G t₀ := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set d : ℝ → E → ℂ := fun s x => (s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x) - f' t₀ x with hd_def
  have hD : ∀ s : ℝ, ((s⁻¹ • (F (t₀ + s) - F t₀) - G : Lp ℂ 2 μ) : E → ℂ) =ᵐ[μ] d s := by
    intro s
    filter_upwards [Lp.coeFn_sub (s⁻¹ • (F (t₀ + s) - F t₀)) G,
      Lp.coeFn_smul s⁻¹ (F (t₀ + s) - F t₀), Lp.coeFn_sub (F (t₀ + s)) (F t₀),
      hF (t₀ + s), hF t₀, hG] with x h1 h2 h3 h4 h5 h6
    simp only [hd_def, h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, h6]
  have hsq : ∀ s : ℝ, ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2 = ∫ x, ‖d s x‖ ^ 2 ∂μ := by
    intro s
    rw [lp_two_norm_sq]
    exact integral_congr_ae ((hD s).mono fun x hx => by simp only [hx])
  have hlim : Tendsto (fun s : ℝ => ∫ x, ‖d s x‖ ^ 2 ∂μ) (𝓝[≠] 0) (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => (2 * b x) ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun s =>
        (((Lp.aestronglyMeasurable _).congr (hD s)).norm.pow 2)
    · have hs : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 ∧ |s| < δ := by
        have h1 : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := eventually_mem_nhdsWithin
        have h2 : ∀ᶠ s : ℝ in 𝓝[≠] 0, |s| < δ := by
          refine nhdsWithin_le_nhds ?_
          have : ∀ᶠ s : ℝ in 𝓝 0, s ∈ Metric.ball (0 : ℝ) δ := Metric.ball_mem_nhds _ hδ
          exact this.mono fun s hs => by simpa using hs
        exact h1.and h2
      refine hs.mono fun s hs => Eventually.of_forall fun x => ?_
      obtain ⟨hs0, hsδ⟩ := hs
      have hmem : t₀ + s ∈ Metric.ball t₀ δ := by simpa [Metric.mem_ball, dist_eq_norm] using hsδ
      have h0 : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
      have hmv : ‖f (t₀ + s) x - f t₀ x‖ ≤ b x * ‖(t₀ + s) - t₀‖ :=
        (convex_ball t₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun r => f r x) (f' := fun r => f' r x)
          (fun r hr => (hd x r hr).hasDerivWithinAt) (fun r hr => hbd x r hr) h0 hmem
      have hb0 : 0 ≤ b x := (norm_nonneg _).trans (hbd x t₀ h0)
      have hq : ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ ≤ b x := by
        rw [norm_smul, norm_inv]
        have hn : 0 < ‖s‖ := norm_pos_iff.2 hs0
        rw [add_sub_cancel_left] at hmv
        rw [inv_mul_le_iff₀ hn]
        linarith [mul_comm (b x) ‖s‖]
      have hdn : ‖d s x‖ ≤ 2 * b x := by
        calc ‖d s x‖ ≤ ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ + ‖f' t₀ x‖ := norm_sub_le _ _
          _ ≤ 2 * b x := by linarith [hbd x t₀ h0]
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hdn 2
    · simpa [mul_pow] using hb.integrable_sq.const_mul (2 ^ 2)
    · refine Eventually.of_forall fun x => ?_
      have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hd x t₀ (Metric.mem_ball_self hδ))
      have h2 : Tendsto (fun s : ℝ => d s x) (𝓝[≠] 0) (𝓝 (f' t₀ x - f' t₀ x)) :=
        h1.sub tendsto_const_nhds
      have h3 := (h2.norm).pow 2
      simpa using h3
  have hlim0 : Tendsto (fun s : ℝ => ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simp only [hsq]
    simpa using hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h4 := (Real.continuous_sqrt.tendsto 0).comp hlim0
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h4

variable {l : Type} [Fintype l]

end GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve

end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.PairingL2
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open scoped InnerProductSpace

namespace PositivityTheory.PRW.GKD

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_haar_GA : ∃ μ : Measure (GA E a), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩

theorem memL2_normalised_cusp_form (hB : GlobalTheory.Published.CuspFormsBoundedGL) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    {π : CuspSub E a} (hπ : IsNormalised π) : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1 := by
  intro φ hφ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h := π.cusp φ hφ
  obtain ⟨C, hC⟩ := hB E a φ h fun t g => by rw [hπ φ hφ t g]
  exact GlobalTheory.CuspQuot.memL2_of_bound (ContAut.continuous_of_isOpen_stab E a φ h.1.level)
    (leftInv_latticeGL h.1.left (hπ φ hφ)) hC

theorem continuous_of_mem {π : CuspSub E a} : ∀ φ ∈ π.V, Continuous φ.1 := fun φ hφ =>
  ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level

theorem inner_R (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E a)
    (F F' : L2 (latticeGL E a) μ) :
    ⟪R (latticeGL E a) μ g F, R (latticeGL E a) μ g F'⟫_ℂ = ⟪F, F'⟫_ℂ :=
  LinearIsometry.inner_map_map
    { toLinearMap := (R (latticeGL E a) μ g : L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ).toLinearMap
      norm_map' := norm_R g } F F'

end PositivityTheory.PRW.GKD

end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.LieSkew
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open scoped InnerProductSpace

namespace PositivityTheory.PRW.GKD

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def expG (X : Lie E a) (t : ℝ) : GL (Fin a) (Cinf E) := (Matrix.isUnit_exp (t • Matrix.of X)).unit

theorem expG_val (X : Lie E a) (t : ℝ) : (expG X t).val = NormedSpace.exp (t • Matrix.of X) :=
  IsUnit.unit_spec _

theorem expG_zero (X : Lie E a) : expG X 0 = 1 := by
  ext1
  rw [expG_val]
  simp


open scoped Matrix.Norms.Operator in
theorem hasDerivAt_toL_exp (X : Lie E a) (t : ℝ) :
    HasDerivAt (fun s : ℝ => toL (NormedSpace.exp (s • Matrix.of X))) (rmul X (toL (NormedSpace.exp (t • Matrix.of X)))) t := by
  let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) t
  exact L.hasFDerivAt.comp_hasDerivAt t h1

theorem hasDerivAt_expG {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (X : Lie E a) (x : GA E a) (t : ℝ) :
    HasDerivAt (fun s => φ (x * infGL E a (expG X s))) (lieD X φ (x * infGL E a (expG X t))) t := by
  have hx : toL (expG X t).val ∈ invSet E a := val_mem_invSet _
  have hf := ((contDiffAt_chart hφ x hx).differentiableAt (by simp)).hasFDerivAt
  have hc := hasDerivAt_toL_exp X t
  rw [← expG_val] at hc
  have h := hf.comp_hasDerivAt t hc
  have e1 : (fun s => φ (x * infGL E a (expG X s))) = chart φ x ∘ fun s : ℝ => toL (NormedSpace.exp (s • Matrix.of X)) := by
    funext s
    rw [Function.comp_apply, ← expG_val, chart_val]
  rw [e1]
  refine h.congr_deriv ?_
  rw [← chart_lieD hφ X x hx, chart_val]

theorem hasDerivAt_R (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    [IsFiniteMeasure (quotMeasure (latticeGL E a) μ)] {φ : Sm E a} (X : Lie E a)
    (hl : MemL2Quotient (latticeGL E a) μ φ.1) (hl' : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1)
    {C : ℝ} (hC : ∀ g, ‖(lie E a X φ).1 g‖ ≤ C) :
    HasDerivAt (fun t => R (latticeGL E a) μ (infGL E a (expG X t)) hl.toL2) hl'.toL2 0 := by
  refine GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve.hasDerivAt_Lp_of_dominated _ _
    (fun t q => descend (latticeGL E a) (fun x => φ.1 (x * infGL E a (expG X t))) q)
    (fun t q => descend (latticeGL E a) (fun x => lieD X φ.1 (x * infGL E a (expG X t))) q)
    (fun _ => C) 0 1 one_pos ?_ ?_ ?_ ?_ ?_
  · intro t
    rw [right_translate_toL2]
    exact (hl.mul_right _).coeFn_toL2
  · have e : (fun q => descend (latticeGL E a) (fun x => lieD X φ.1 (x * infGL E a (expG X 0))) q) =
        descend (latticeGL E a) (lie E a X φ).1 := by
      funext q
      simp [descend, expG_zero]
    rw [e]
    exact hl'.coeFn_toL2
  · exact memLp_const C
  · intro q t _
    exact hasDerivAt_expG φ.2 X q.out t
  · intro q t _
    exact hC _

theorem inner_lie_skew' (hB : GlobalTheory.Published.CuspFormsBoundedGL) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    {π : CuspSub E a} (hπ : IsNormalised π) (X : Lie E a) (f g : π.V) :
    ⟪toL2ₗ μ π.V (memL2_normalised_cusp_form hB μ hπ) (π.op (.lie X) f), toL2ₗ μ π.V (memL2_normalised_cusp_form hB μ hπ) g⟫_ℂ +
      ⟪toL2ₗ μ π.V (memL2_normalised_cusp_form hB μ hπ) f,
        toL2ₗ μ π.V (memL2_normalised_cusp_form hB μ hπ) (π.op (.lie X) g)⟫_ℂ = 0 := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  set hL := memL2_normalised_cusp_form hB μ hπ
  have hbd : ∀ x : π.V, ∃ C : ℝ, ∀ g, ‖(lie E a X x.1).1 g‖ ≤ C := fun x =>
    hB E a _ (π.cusp _ (π.stable (.lie X) x.1 x.2)) fun t g => congrArg norm (hπ _ (π.stable (.lie X) x.1 x.2) t g)
  obtain ⟨C1, h1⟩ := hbd f
  obtain ⟨C2, h2⟩ := hbd g
  have df := hasDerivAt_R μ X (hL f.1 f.2) (hL _ (π.stable (.lie X) f.1 f.2)) h1
  have dg := hasDerivAt_R μ X (hL g.1 g.2) (hL _ (π.stable (.lie X) g.1 g.2)) h2
  have hd := HasDerivAt.inner ℂ df dg
  have hconst : (fun t => ⟪R (latticeGL E a) μ (infGL E a (expG X t)) (hL f.1 f.2).toL2,
      R (latticeGL E a) μ (infGL E a (expG X t)) (hL g.1 g.2).toL2⟫_ℂ) =
      fun _ => ⟪(hL f.1 f.2).toL2, (hL g.1 g.2).toL2⟫_ℂ := funext fun t => inner_R μ _ _ _
  rw [hconst] at hd
  have h0 := hd.unique (hasDerivAt_const _ _)
  simp only [expG_zero, map_one, ContinuousLinearMap.one_apply] at h0
  rw [add_comm]
  exact h0

end PositivityTheory.PRW.GKD

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open scoped InnerProductSpace

namespace PositivityTheory.PRW.GKD

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def dualMapC : Sm E a →ₗ⋆[ℂ] Sm E a where
  toFun φ := ⟨fun g => star (φ.1 (invA E a g)), GlobalTheory.T.smooth_conjugate_inverse_mem φ.2⟩
  map_add' φ ψ := Subtype.ext (funext fun g => by simp)
  map_smul' c φ := Subtype.ext (funext fun g => by simp)

theorem dualMapC_dualMapC (φ : Sm E a) : dualMapC E a (dualMapC E a φ) = φ :=
  Subtype.ext (funext fun g => by simp [dualMapC, invA_invA])

theorem act_dualMapC (o : Op E a) (φ : Sm E a) : act o (dualMapC E a φ) = dualMapC E a (act (invTOp o) φ) :=
  GlobalTheory.T.conjugate_inverse_right_action o φ _ _

theorem isCuspForm_dualMapC {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (dualMapC E a φ) :=
  GlobalTheory.T.cuspForm_conjugate_inverse φ _ h

theorem dualMapC_injective : Function.Injective (dualMapC E a) := fun φ ψ h => by
  rw [← dualMapC_dualMapC φ, ← dualMapC_dualMapC ψ, h]

theorem dualMapC_surjective : Function.Surjective (dualMapC E a) := fun φ => ⟨dualMapC E a φ, dualMapC_dualMapC φ⟩

def dualSubC (π : CuspSub E a) : CuspSub E a where
  V := π.V.map (dualMapC E a)
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact isCuspForm_dualMapC (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable (invTOp o) φ hφ, (act_dualMapC o φ).symm⟩
  ne_bot h := π.ne_bot (by
    rw [eq_bot_iff]
    intro φ hφ
    have h1 : dualMapC E a φ ∈ (⊥ : Submodule ℂ (Sm E a)) := h ▸ ⟨φ, hφ, rfl⟩
    rw [Submodule.mem_bot] at h1 ⊢
    exact dualMapC_injective (h1.trans (map_zero _).symm))
  irred W hW hs := by
    have h := π.irred (W.comap (dualMapC E a)) (fun φ hφ => by
        obtain ⟨ψ, h1, h2⟩ := hW hφ
        rwa [← dualMapC_injective h2]) fun o φ hφ => by
      have h1 := hs (invTOp o) _ hφ
      rw [act_dualMapC, GlobalTheory.CsdBack.invTOp_involutive o] at h1
      exact h1
    have e := Submodule.map_comap_eq_of_surjective dualMapC_surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem paired_of_dualSubC_eq (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : IsNormalised π)
    (h : (dualSubC π).V = π.V) : Paired π π invTOp := by
  obtain ⟨μ, hμ⟩ := exists_haar_GA (E := E) (a := a)
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  set hL := memL2_normalised_cusp_form hB μ hπ
  set u := toL2ₗ μ π.V hL
  have hJ : ∀ ψ : π.V, dualMapC E a ψ.1 ∈ π.V := fun ψ => by
    have h1 : dualMapC E a ψ.1 ∈ (dualSubC π).V := ⟨ψ.1, ψ.2, rfl⟩
    rwa [h] at h1
  let J : π.V → π.V := fun ψ => ⟨dualMapC E a ψ.1, hJ ψ⟩
  have JJ : ∀ ψ, J (J ψ) = ψ := fun ψ => Subtype.ext (dualMapC_dualMapC ψ.1)
  have Jadd : ∀ ψ ψ', J (ψ + ψ') = J ψ + J ψ' := fun ψ ψ' => Subtype.ext (map_add (dualMapC E a) ψ.1 ψ'.1)
  have Jsmul : ∀ (c : ℂ) ψ, J (c • ψ) = (starRingEnd ℂ c) • J ψ := fun c ψ =>
    Subtype.ext (LinearMap.map_smulₛₗ (dualMapC E a) c ψ.1)
  have Jop : ∀ o ψ, J (π.op (invTOp o) ψ) = π.op o (J ψ) := fun o ψ =>
    Subtype.ext (act_dualMapC o ψ.1).symm
  have uR : ∀ (g : GA E a) (x : π.V) (hg : rt E a g x.1 ∈ π.V),
      u ⟨_, hg⟩ = R (latticeGL E a) μ g (u x) := fun g x hg => (R_toL2ₗ hL x hg).symm
  have ufin : ∀ (k : GL (Fin a) (Af E)) (x : π.V), u (π.op (.fin k) x) = R (latticeGL E a) μ (finGL E a k) (u x) :=
    fun k x => (R_toL2ₗ hL x (π.stable (.fin k) x.1 x.2)).symm
  have ucpt : ∀ (k : Kinf E a) (x : π.V),
      u (π.op (.cpt k) x) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (u x) :=
    fun k x => (R_toL2ₗ hL x (π.stable (.cpt k) x.1 x.2)).symm
  have hinj : Function.Injective u := toL2ₗ_injective hL continuous_of_mem
  let B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun φ ψ => ⟪u (J ψ), u φ⟫_ℂ)
    (fun φ φ' ψ => by simp only [map_add (f := _), inner_add_right])
    (fun c φ ψ => by simp only [map_smul, inner_smul_right, smul_eq_mul])
    (fun φ ψ ψ' => by simp only [Jadd, map_add (f := _), inner_add_left])
    (fun c φ ψ => by simp only [Jsmul, map_smul, inner_smul_left, RingHomCompTriple.comp_apply, RingHom.id_apply,
      smul_eq_mul])
  have hB' : ∀ φ ψ, B φ ψ = ⟪u (J ψ), u φ⟫_ℂ := fun _ _ => rfl
  have hself : ∀ x : π.V, ⟪u x, u x⟫_ℂ = 0 → x = 0 := fun x hx =>
    hinj ((inner_self_eq_zero.1 hx).trans (map_zero u).symm)
  refine ⟨B, fun φ hφ => hself φ (by simpa [hB', JJ] using hφ (J φ)), fun ψ hψ => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · have h1 := hself (J ψ) (by simpa [hB'] using hψ (J ψ))
    rw [← JJ ψ, h1]
    exact Subtype.ext (by simp [J])
  · rw [hB', hB', Jop, ufin, ufin]
    exact inner_R μ _ _ _
  · rw [hB', hB', Jop, ucpt, ucpt]
    exact inner_R μ _ _ _
  · rw [hB', hB', Jop, add_comm]
    exact inner_lie_skew' hB μ hπ X (J ψ) φ

theorem dualSubC_V_eq (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (hM : GlobalTheory.Published.CuspidalMultiplicityOne)
    (hB : GlobalTheory.Published.CuspFormsBoundedGL) (ha : 1 ≤ a) {π : CuspSub E a} (hπ : IsNormalised π) : (dualSubC π).V = π.V := by
  refine hM E a (dualSubC π) π ?_
  obtain ⟨s, hs⟩ := hJ E Unit Unit (fun _ => a) (fun _ => a) (fun _ => CG.mk (dualSubC π)) (fun _ => CG.mk π)
    (fun _ => ha) (fun _ => ha) (by
      filter_upwards [GlobalTheory.T.cuspidal_satake_almost_all π] with w hw
      obtain ⟨B, hw⟩ := hw
      exact ⟨fun _ => B, fun _ => B, fun _ => PositivityTheory.PRW.SatakeDual.hasSat_dual hB hπ (dualSubC π) (fun ψ => ⟨fun ⟨φ, hφ, e⟩ => ⟨φ, hφ, e ▸ rfl⟩,
        fun ⟨φ, hφ, e⟩ => ⟨φ, hφ, Subtype.ext e.symm⟩⟩) w B hw, fun _ => hw, rfl⟩)
  exact eq_of_heq (Sigma.mk.inj_iff.1 (hs ())).2

theorem gelfandKazhdanDual_of_multiplicityOne (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (hM : GlobalTheory.Published.CuspidalMultiplicityOne)
    (hB : GlobalTheory.Published.CuspFormsBoundedGL) : GlobalTheory.Published.GelfandKazhdanDual := by
  intro E _ _ _ n π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.Published.InvTransposeModel.rank_zero π
  obtain ⟨π₀, χ, h0, rfl⟩ := GlobalTheory.T.cuspidal_eq_twist_normalised π
  exact GlobalTheory.Published.InvTransposeModel.twist (paired_of_dualSubC_eq hB h0 (dualSubC_V_eq hJ hM hB hn h0)) χ

end PositivityTheory.PRW.GKD

end

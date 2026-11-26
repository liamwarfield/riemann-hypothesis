module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.UnitTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutNewform
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.AutomorphicNewform

end UpperTheory.V.Af.AutomorphicNewform
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GelfandKazhdanReal
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.PairZero
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.pairZero :
    UpperTheory.V.Af.Gk.PairZero := by
  intro F _ _ _ π
  have hs : ∀ g h : GlobalTheory.CuspRep.GA F 0, g = h := fun g h => Units.ext (Subsingleton.elim _ _)
  let e : π.V →ₗ[ℂ] ℂ := (LinearMap.proj 1) ∘ₗ (Sm F 0).subtype ∘ₗ π.V.subtype
  have he : ∀ φ, e φ = φ.1.1 1 := fun _ => rfl
  have hinj : ∀ φ, e φ = 0 → φ = 0 := fun φ h =>
    Subtype.ext <| Subtype.ext <| funext fun g => by rw [hs g 1]; exact h
  have hfin : ∀ k φ, e (π.op (.fin k) φ) = e φ := fun k φ => congrArg φ.1.1 (hs _ _)
  have hcpt : ∀ k φ, e (π.op (.cpt k) φ) = e φ := fun k φ => congrArg φ.1.1 (hs _ _)
  have hlie : ∀ X φ, e (π.op (.lie X) φ) = 0 := fun X φ => by
    rw [Subsingleton.elim X 0]
    exact map_zero (fderiv ℝ (chart φ.1.1 1) (oneL F 0))
  refine ⟨(LinearMap.mul ℂ ℂ).compl₁₂ e e, fun φ h => hinj φ (mul_self_eq_zero.1 (h φ)),
    fun φ h => hinj φ (mul_self_eq_zero.1 (h φ)), fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · change e _ * e _ = e φ * e ψ
    rw [hfin, hfin]
  · change e _ * e _ = e φ * e ψ
    rw [hcpt, hcpt]
  · change e _ * e _ + e _ * e _ = 0
    rw [hlie, hlie, zero_mul, mul_zero, add_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.ConjSub
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.ConjCusp
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

noncomputable section

namespace UpperTheory.V.Af.Gk

private theorem map_qdet_conj {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (f : A →+* A)
    (hf : ∀ c : ℂ, f (algebraMap ℂ A c) = algebraMap ℂ A (starRingEnd ℂ c)) (X : Fin n → Fin n → A)
    (hX : ∀ i j, f (X i j) = X i j) (u : ℂ) :
    f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet X (starRingEnd ℂ u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, id_eq, Formalism.REAL.Tm, map_add, hX]
  split_ifs <;> simp [hf, map_sub]

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

private def conjOp : Module.End ℂ (Sm E a) →+* Module.End ℂ (Sm E a) where
  toFun z := (conjFn E a).toLinearMap ∘ₛₗ (z ∘ₛₗ (conjFn E a).toLinearMap)
  map_one' := LinearMap.ext fun φ => conjFn_conjFn φ
  map_mul' x y := LinearMap.ext fun φ => by
    change conjFn E a (x (y (conjFn E a φ))) = conjFn E a (x (conjFn E a (conjFn E a (y (conjFn E a φ)))))
    rw [conjFn_conjFn]
  map_zero' := LinearMap.ext fun φ => map_zero (conjFn E a)
  map_add' x y := LinearMap.ext fun φ => map_add (conjFn E a) _ _

private theorem conjOp_apply (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjOp z φ = conjFn E a (z (conjFn E a φ)) := rfl

private theorem conjOp_algebraMap (c : ℂ) :
    conjOp (algebraMap ℂ (Module.End ℂ (Sm E a)) c) = algebraMap ℂ _ (starRingEnd ℂ c) :=
  LinearMap.ext fun φ => by
    rw [conjOp_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smulₛₗ, conjFn_conjFn]

private theorem conjOp_Eop (v : InfinitePlace E) (i j : Fin a) : conjOp (Eop v i j) = Eop v i j :=
  LinearMap.ext fun φ => (congrArg (conjFn E a) (act_conjFn (.lie _) φ)).trans (conjFn_conjFn _)

private theorem conjOp_cap (v : InfinitePlace E) (u : ℂ) :
    conjOp (cap (a := a) v u) = cap v (starRingEnd ℂ u) := by
  refine (map_qdet_conj (conjOp (E := E) (a := a)) conjOp_algebraMap (Eop v) (conjOp_Eop v) _).trans ?_
  refine congrArg (Formalism.REAL.qdet (Eop (a := a) v)) ?_
  simp only [map_add (f := _), map_div₀, map_sub, map_natCast, map_one, map_ofNat]

private theorem conjOp_mem {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : conjOp z ∈ Zalg E a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    rw [conjOp_cap]
    exact Algebra.subset_adjoin ⟨τ, _, rfl⟩
  | algebraMap c => rw [conjOp_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem fin_of_conj {s t : Set (Sm E a)} (h : FiniteDimensional ℂ (Submodule.span ℂ s))
    (hst : ∀ y ∈ t, ∃ x ∈ s, conjFn E a x = y) : FiniteDimensional ℂ (Submodule.span ℂ t) := by
  have h1 : (Submodule.span ℂ s).FG := Module.Finite.iff_fg.1 h
  have h2 : FiniteDimensional ℂ ((Submodule.span ℂ s).map (conjFn E a).toLinearMap) :=
    Module.Finite.iff_fg.2 (h1.map _)
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ s).map (conjFn E a).toLinearMap)
    (Submodule.span_le.2 fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := hst y hy
  exact ⟨x, Submodule.subset_span hx, rfl⟩

private theorem isAutForm_conjFn {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (conjFn E a φ) := by
  exact {
    left γ g := by rw [conjFn_apply, conjFn_apply, h.left]
    level := by
      convert h.level using 1
      ext k
      exact (Iff.of_eq (congrArg (· = conjFn E a φ) (act_conjFn (.fin k) φ))).trans (conjFn E a).injective.eq_iff
    kfin := fin_of_conj h.kfin (by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, (act_conjFn (.cpt k) φ).symm⟩)
    zfin := fin_of_conj h.zfin (by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨_, ⟨conjOp z, conjOp_mem hz, rfl⟩, ?_⟩
      beta_reduce
      rw [conjOp_apply, conjFn_conjFn])
    growth g := by
      obtain ⟨C, N, h1⟩ := h.growth g
      refine ⟨C, N, fun y => ?_⟩
      rw [conjFn_apply, Complex.norm_conj]
      exact h1 y }

end UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.conjCusp :
    UpperTheory.V.Af.Gk.ConjCusp := by
  intro F _ _ _ a φ h
  refine ⟨isAutForm_conjFn h.1, ?_⟩
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  have key := h.2 r h0 h1 μ 𝓕 hμ hF g
  simp only [conjFn_apply]
  rw [integral_conj, key, map_zero]
end
end

open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

noncomputable section

namespace UpperTheory.V.Af.Gk

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

private def conjRep (π : TR.CuspSub E a) : TR.CuspSub E a where
  V := π.V.map (conjFn E a).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact conjCusp E a φ (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable o φ hφ, (act_conjFn o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := conjFn E a)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (conjFn E a).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (conjFn E a).injective h2]) fun o φ hφ => by
      have h1 := hs o _ hφ
      change act _ (conjFn E a φ) ∈ W at h1
      rw [act_conjFn] at h1
      exact h1
    have e := Submodule.map_comap_eq_of_surjective (f := (conjFn E a).toLinearMap) (conjFn E a).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

end UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.conjSub :
    UpperTheory.V.Af.Gk.ConjSub := by
  intro F _ _ _ a π
  exact ⟨conjRep π, (conjFn F a).submoduleMap π.V, fun o φ => Subtype.ext (act_conjFn o φ.1).symm⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.PairOfTwist
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

private theorem UpperTheory.V.Af.Gk.opMul_mul_invT {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}
    (χ : HChar E) (o : Op E a) : ((opMul χ o : ℂˣ) : ℂ) * ((opMul χ (invTOp o) : ℂˣ) : ℂ) = 1 := by
  have key : ∀ g : GlobalTheory.CuspRep.GA E a, ((GlobalTheory.CuspRep.chiDet a χ g : ℂˣ) : ℂ) *
      ((GlobalTheory.CuspRep.chiDet a χ (GlobalTheory.CuspRep.invT a _ g) : ℂˣ) : ℂ) = 1 := fun g => by
    rw [InvT.chiDet_invT]
    exact Units.mul_inv _
  cases o with
  | fin k =>
    have := key (GlobalTheory.CuspRep.finGL E a k)
    rw [← InvT.finGL_invT] at this
    exact this
  | cpt k =>
    have := key (infGL E a (Unitary.toUnits k))
    rw [← infGL_invT, invT_toUnits] at this
    exact this
  | lie X => simp [opMul, invTOp]

theorem UpperTheory.V.Af.Gk.pairOfTwist :
    UpperTheory.V.Af.Gk.PairOfTwist := by
  intro F _ _ _ a π χ ⟨B, h1, h2, hf, hc, hl⟩
  let T := π.toTwist χ
  refine ⟨B.compl₁₂ T.toLinearMap T.toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ h
    apply T.injective
    rw [T.map_zero]
    apply h1
    intro ψ
    simpa using h (T.symm ψ)
  · intro ψ h
    apply T.injective
    rw [T.map_zero]
    apply h2
    intro φ
    simpa using h (T.symm φ)
  · intro k φ ψ
    have h := hf k (T φ) (T ψ)
    have e := opMul_mul_invT χ (.fin k : Op F a)
    simp only [T, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← mul_assoc, mul_comm (_ : ℂ) ((opMul χ (.fin k) : ℂˣ) : ℂ)] at h
    erw [e] at h
    rw [one_mul] at h
    exact h
  · intro k φ ψ
    have h := hc k (T φ) (T ψ)
    have e := opMul_mul_invT χ (.cpt k : Op F a)
    simp only [T, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← mul_assoc] at h
    erw [e] at h
    rw [one_mul] at h
    exact h
  · intro X φ ψ
    have h := hl X (T φ) (T ψ)
    have e : (Matrix.of (toL (-(Matrix.of X)ᵀ))).trace = -(Matrix.of X).trace := by
      change (-(Matrix.of X)ᵀ).trace = _
      rw [Matrix.trace_neg, Matrix.trace_transpose]
    simp only [T, CuspSub.op_toTwist, opAdd, opMul, Units.val_one, one_smul, map_add (f := _), map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, e, map_neg] at h
    change B (T _) (T ψ) + B (T φ) (T _) = 0
    linear_combination h
end

open NumberField GlobalTheory.CuspRep UpperTheory.V

open GroundTheory.Automorphic in
private theorem lieMatch : UpperTheory.V.Af.Gk.LieMatch := by
  intro F _ _ _ a
  refine ⟨(Fb.lieEq F a).toLinearMap, Subtype.ext ?_, fun X φ _ =>
    congrArg Subtype.val (UpperTheory.V.Af.CuspFin.uAction_lieEq X φ)⟩
  rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
  rfl

theorem UpperTheory.V.Af.gelfandKazhdanReal :
    UpperTheory.V.Published.StrongMultOneReal → UpperTheory.V.Published.GelfandKazhdanReal :=
  Gk.gelfandKazhdan_of Gk.conjSub Gk.satConj Gk.satAE Gk.unitTwist Gk.pairOfTwist Gk.pairZero
    (Gk.hermEx_of (fun _ _ _ _ _ => CuspFin.mem_cuspForms_of) lieMatch)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SolDescent
open NumberField UpperTheory.V.Af

theorem UpperTheory.V.Af.solDescent :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.SolDescent := by
  intro H F₀ F M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF hsol hplus hM l _ ι n hn r μ hr hirr hμ hs ⟨c, P, hc, hP⟩
  have hM' : IsCMField M := hM.resolve_left fun h => by
    obtain ⟨v⟩ : Nonempty (InfinitePlace M) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.2 ((isTotallyComplex_of_algebra F M).isComplex v)) (h.isReal v)
  exact Z.Bc.solC H H.cyc F M Ω hsol hF hM' l ι n hn r hr hirr ⟨F₀, _, _, _, _, inferInstance, inferInstance, hplus.1, μ, c, P, hμ, hs, hc, hP⟩
end

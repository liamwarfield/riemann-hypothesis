module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.ExistsJointEigenvectorBis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.GenRestrict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.IndepFinset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.RankLeOneOfSlices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.BoxIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.SpehInfRankOneEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PrimeNotMemSectionBasePlaceAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.InfDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PrimeNotMemSectionBasePlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DualDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.Decomp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.SphSame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.ResEq2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.ValOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.MapInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.AbsSpec2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.MapMemIsotypicInvariants
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.CommFinsum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.MuHeckeE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.EigBoxE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.EPartPi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.CountE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.ZEqDimE

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.SchurGL
open UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.schurGL :
    SchurGL := by
  intro L _ _ n w τ
  letI := τ.acg
  letI := τ.mod
  haveI : τ.ρ.IsIrreducible := τ.irred
  have hsm : GroundTheory.Automorphic.IsSmooth τ.ρ := τ.smooth
  refine ⟨τ.irred, fun f hf => ?_⟩
  let φ : Representation.IntertwiningMap τ.ρ τ.ρ :=
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext fun v => hf g v }
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hsm).2 φ
  exact ⟨c, LinearMap.ext fun v => (congrArg (fun h : Representation.IntertwiningMap τ.ρ τ.ρ => h v) hc).symm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.CompsEx
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

theorem compsEx : CompsEx := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV σ hσ
  have hund : ∀ {A : ValuationSubring Ω} {w : Plc L}, IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 (Lp L))) :=
    fun hA y => hA (algebraMap (𝓞 (Lp L)) (𝓞 L) y)
  have hwv : ∀ v, (s.w v).under (𝓞 (Lp L)) = v := fun v =>
    HeightOneSpectrum.ext (Ideal.ext fun y => (hund (s.hw v) y).symm.trans (s.hA v y))
  have hsp : ∀ v ∈ s.S, IsSplitAt (s.w v) := fun v hv =>
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v hv) _ (hwv v)
  have hex : ∀ w : Plc L, IsSplitAt w → ∃ τ : SmIrr (GLw n w), Cp σ w τ := fun w hw => by
    obtain ⟨τ, -, h1, -⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ, hσ⟩ w hw
    exact ⟨τ, h1⟩
  have hl : ∀ v : V.frame.Vl, v.1 ∈ s.S := fun v => Or.inl v.2
  have hu : ∀ u : s.St, u.1 ∈ s.S := fun u => Or.inr (Or.inl u.2)
  have ho : s.v0 ∈ s.S := Or.inr (Or.inr rfl)
  choose f hf using fun v (hv : v ∈ s.S) => hex (s.w v) (hsp v hv)
  exact ⟨⟨fun v => f _ (hl v), fun u => f _ (hu u), f _ ho, fun v => hf _ (hl v), fun u => hf _ (hu u), hf _ ho⟩⟩

end UpperTheory.V.Z.J.D
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.KirCusp
open UpperTheory.V.Z.Desc.V0

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.V0.KC

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

private theorem colT_rel (hψ : StdPsi ψ) (X : Set (GA E a))
    (hX : ∀ γ : GL (Fin a) E, IsMir (a - 1) γ → ∀ g ∈ X, ratGL E a γ * g ∈ X)
    {m : ℕ} {f : GA E a → ℂ} (hma : m + 1 < a) (hG : Good ψ (m + 1) f)
    (h0 : ∀ g ∈ X, colT ψ (m + 1) f g = 0) : ∀ g ∈ X, f g = 0 := by
  intro g₀ hgX
  by_contra hg₀
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ0 : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp only [Pi.zero_apply] at h1
    apply hg₀
    have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
    rw [e, one_mul] at h1
    exact h1
  obtain ⟨ξ, hξ⟩ : ∃ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, coefF ψ (m + 1) ξ f g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ0 (GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer h)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hξ
    have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
    have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
      intro x
      simp [dot]
    simp only [coefF, e, one_mul]
    exact hv
  obtain ⟨γ, hγ, hγξ⟩ := GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0
  have hγ' : IsMir (a - 1) γ := fun i k h => hγ i k (by omega)
  have h1 := h0 _ (hX γ hγ' g₀ hgX)
  simp only [colT] at h1
  rw [GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
  have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ :=
    funext hγξ
  rw [e] at h1
  exact hξ h1

private theorem whit_rel (hψ : StdPsi ψ) (X : Set (GA E a))
    (hX : ∀ γ : GL (Fin a) E, IsMir (a - 1) γ → ∀ g ∈ X, ratGL E a γ * g ∈ X) (m : ℕ) :
    (m < a ∨ m = 0) → ∀ {f : GA E a → ℂ}, Good ψ m f → (∀ g ∈ X, whit ψ m f g = 0) → ∀ g ∈ X, f g = 0 := by
  induction m with
  | zero => exact fun _ _ _ h => h
  | succ m ih =>
    intro h f hf h0
    have h1 : m + 1 < a := by omega
    exact colT_rel hψ X hX h1 hf (ih (Or.inl (by omega)) (GlobalTheory.CuspRep.Generic.good_colT hψ h1 hf) h0)

private theorem ker_le_of_rank {V : Type} [AddCommGroup V] [Module ℂ V] (K : Submodule ℂ V)
    (hr : Module.rank ℂ (V ⧸ K) ≤ 1) (l l' : V →ₗ[ℂ] ℂ) (hl : K ≤ LinearMap.ker l) (hl' : K ≤ LinearMap.ker l')
    {v₁ : V} (h1 : l v₁ ≠ 0) {v : V} (hv : l v = 0) : l' v = 0 := by
  obtain ⟨x, hx⟩ := rank_le_one_iff.1 hr
  obtain ⟨r₁, e₁⟩ := hx (K.mkQ v₁)
  obtain ⟨r, e⟩ := hx (K.mkQ v)
  have hr₁ : r₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at e₁
    exact h1 (hl ((Submodule.Quotient.mk_eq_zero K).1 e₁.symm))
  have e2 : K.mkQ (v - (r / r₁) • v₁) = 0 := by
    rw [map_sub, map_smul, ← e, ← e₁, smul_smul, div_mul_cancel₀ _ hr₁, sub_self]
  have hK : v - (r / r₁) • v₁ ∈ K := (Submodule.Quotient.mk_eq_zero K).1 e2
  have h2 : l (v - (r / r₁) • v₁) = 0 := hl hK
  have h3 : l' (v - (r / r₁) • v₁) = 0 := hl' hK
  rw [map_sub, map_smul, hv, zero_sub, neg_eq_zero, smul_eq_mul] at h2
  have hc : r / r₁ = 0 := (mul_eq_zero.1 h2).resolve_right h1
  rw [hc, zero_smul, sub_zero] at h3
  exact h3

private theorem denseRange_mapGL {K B : Type} [Field K] [Field B] [TopologicalSpace B] [IsTopologicalRing B]
    [ContinuousInv₀ B] [T1Space B] (j : K →+* B) (hj : DenseRange j) (a : ℕ) :
    DenseRange (GeneralLinearGroup.map j : GL (Fin a) K → GL (Fin a) B) := by
  intro M
  rw [mem_closure_iff]
  intro o ho hMo
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 ho
  let f : Matrix (Fin a) (Fin a) B → Matrix (Fin a) (Fin a) B × (Matrix (Fin a) (Fin a) B)ᵐᵒᵖ :=
    fun P => (P, MulOpposite.op P⁻¹)
  have hdet : M.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have hinv : ContinuousAt (fun P : Matrix (Fin a) (Fin a) B => P⁻¹) M.val := by
    have e : (fun P : Matrix (Fin a) (Fin a) B => P⁻¹) = fun P => (P.det)⁻¹ • P.adjugate := by
      funext P
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    exact ((continuousAt_inv₀ hdet).comp (continuous_id.matrix_det).continuousAt).smul
      (continuous_id.matrix_adjugate).continuousAt
  have hf : ContinuousAt f M.val := continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hfM : f M.val = Units.embedProduct _ M := by
    simp only [f, Units.embedProduct_apply, Matrix.coe_units_inv]
  have hN : f ⁻¹' O ∩ {P | P.det ≠ 0} ∈ nhds M.val := by
    refine Filter.inter_mem (hf.preimage_mem_nhds (hO.mem_nhds ?_)) ?_
    · rw [hfM]; exact hMo
    · exact (isOpen_ne.preimage (continuous_id.matrix_det)).mem_nhds hdet
  have hd : DenseRange fun Q : Matrix (Fin a) (Fin a) K => Q.map j :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hj
  obtain ⟨Q, hQO, hQd⟩ := hd.mem_nhds hN
  have hQ : IsUnit Q.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => hQd ?_
    have : j Q.det = 0 := by rw [h0, map_zero]
    rw [RingHom.map_det] at this
    exact this
  let γ : GL (Fin a) K := ((Matrix.isUnit_iff_isUnit_det Q).2 hQ).unit
  refine ⟨GeneralLinearGroup.map j γ, ?_, γ, rfl⟩
  change Units.embedProduct _ (GeneralLinearGroup.map j γ) ∈ O
  have e : Units.embedProduct _ (GeneralLinearGroup.map j γ) = f (Q.map j) := by
    simp only [f, Units.embedProduct_apply, Matrix.coe_units_inv]
    rfl
  rw [e]; exact hQO

variable [_root_.NumberField.IsTotallyComplex E]

private noncomputable def pw (w : HeightOneSpectrum (𝓞 E)) : GA E a →* GL (Fin a) (w.adicCompletion E) :=
  (GeneralLinearGroup.map (pLoc E w)).comp (GeneralLinearGroup.map (pFin E))

private theorem pw_fl (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)) :
    pw w (finGL E a (locGL E a w u)) = u := by
  simp only [pw, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL]

private theorem pw_rat (w : HeightOneSpectrum (𝓞 E)) (γ : GL (Fin a) E) :
    pw w (ratGL E a γ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ := by
  apply Units.ext
  ext i j
  rfl

private theorem comm_of_pw (w : HeightOneSpectrum (𝓞 E)) {h : GA E a} (hk : pw w h = 1)
    (u : GL (Fin a) (w.adicCompletion E)) :
    h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_finGL, one_mul, mul_one]
  · rw [map_mul, map_mul, pFin_finGL]
    exact LocUniq.comm_locGL w hk u

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem isMirL_mul {k : Type} [Field k] {p q : GL (Fin a) k} (hp : IsMirL p) (hq : IsMirL q) : IsMirL (p * q) := by
  intro i j hi
  change (p.val * q.val) i j = _
  rw [Matrix.mul_apply]
  simp_rw [hp i _ hi]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact hq i j hi

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem isMirL_one {k : Type} [Field k] : IsMirL (1 : GL (Fin a) k) := fun _ _ _ => rfl

private def X (w : HeightOneSpectrum (𝓞 E)) : Set (GA E a) := {g | IsMirL (pw w g)}

private theorem X_stable (w : HeightOneSpectrum (𝓞 E)) (γ : GL (Fin a) E) (hγ : IsMir (a - 1) γ) (g : GA E a)
    (hg : g ∈ X w) : ratGL E a γ * g ∈ X w := by
  change IsMirL (pw w (ratGL E a γ * g))
  rw [map_mul, pw_rat]
  refine isMirL_mul (fun i j hi => ?_) hg
  change algebraMap E (w.adicCompletion E) (γ.val i j) = _
  rw [hγ i j (Or.inl (by omega))]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

end UpperTheory.V.Z.Desc.V0.KC

open UpperTheory.V.Z.Desc.V0.KC GlobalTheory.CuspRep.Generic in
theorem UpperTheory.V.Z.Desc.V0.kirCusp :
    KirCusp := by
  intro E _ _ _ a _ P w σ hσ
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v, Good ψ (a - 1) (f v).1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ (f v).1 (P.cusp _ (f v).2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have hv1 : (f v₀).1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h₀, gw, e, hc₀⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x =
      whit ψ (a - 1) (f v).1.1 (x * finGL E a (locGL E a w u)) := fun u v x => by
    rw [hf u v]
    exact whit_rt _ _ _ _
  let L : GA E a → σ.V →ₗ[ℂ] ℂ := fun h =>
    { toFun := fun v => whit ψ (a - 1) (f v).1.1 h
      map_add' := fun v v' => by
        rw [map_add f]
        exact congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => by
        rw [map_smul f]
        exact congrFun (whit_smul (a - 1) c (f v).1.1) h }
  have hL : ∀ h v, L h v = whit ψ (a - 1) (f v).1.1 h := fun _ _ => rfl
  have hne : L h₀ (σ.ρ gw v₀) ≠ 0 := by
    rw [hL, hrt, ← e]
    exact hg₀
  have hlaw : ∀ h, (∀ u, h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h) →
      ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) v,
      L h (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion E)).val p.1 p.2) : ℂ) * L h v := by
    intro h hc u v
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 u.2
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hL, hrt, hc, this, t3]
    rfl
  have hK : ∀ h, (∀ u, h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h) →
      GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤
        LinearMap.ker (L h) := by
    intro h hc
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw h hc, smul_eq_mul]
    exact sub_eq_zero.2 rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hnt : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  have hrank := PositivityTheory.rg.gu.whit.whitLeOne (w.adicCompletion E) a (locPsi hψ w) σ.V σ.ρ σ.5 σ.6 hcont hnt
  refine ⟨locPsi hψ w, L h₀, hcont, hnt, ?_, ?_⟩
  · intro u hu v
    rw [hlaw h₀ hc₀ ⟨u, hu⟩ v]
    simp only [chr, one_mul]
  · intro v hv
    have hA : ∀ g ∈ (X w : Set (GA E a)), whit ψ (a - 1) (f v).1.1 g = 0 := by
      intro g hgX
      have hp : pw w (g * (finGL E a (locGL E a w (pw w g)))⁻¹) = 1 := by
        rw [map_mul, map_inv, pw_fl, mul_inv_cancel]
      have e1 : g = g * (finGL E a (locGL E a w (pw w g)))⁻¹ * finGL E a (locGL E a w (pw w g)) :=
        (inv_mul_cancel_right _ _).symm
      rw [e1, ← hrt, ← hL]
      exact ker_le_of_rank _ hrank (L h₀) (L _) (hK h₀ hc₀) (hK _ (comm_of_pw w hp)) hne (hv _ hgX)
    have hB := whit_rel hψ (X w) (X_stable w) (a - 1) h0 (hg v) hA
    have hC : (f v).1.1 = 0 := by
      funext g
      have hU : IsOpen {u | σ.ρ u v = v} := σ.5 v
      obtain ⟨γ, hγ⟩ := (denseRange_mapGL (algebraMap E (w.adicCompletion E))
        (HeightOneSpectrum.denseRange_algebraMap E w) a).exists_mem_open
        (hU.preimage (continuous_mul_const (pw w g))) ⟨(pw w g)⁻¹, by
          change σ.ρ ((pw w g)⁻¹ * pw w g) v = v
          rw [inv_mul_cancel, map_one]
          rfl⟩
      have hu : σ.ρ (pw w (ratGL E a γ * g)) v = v := by
        rw [map_mul, pw_rat]
        exact hγ
      have hp : pw w (ratGL E a γ * g * (finGL E a (locGL E a w (pw w (ratGL E a γ * g))))⁻¹) = 1 := by
        rw [map_mul _ _ (_)⁻¹, map_inv, pw_fl, mul_inv_cancel]
      have hX1 : ratGL E a γ * g * (finGL E a (locGL E a w (pw w (ratGL E a γ * g))))⁻¹ ∈ (X w : Set (GA E a)) := by
        change IsMirL _
        rw [hp]
        exact isMirL_one
      have h1 := hB _ hX1
      have h2 : (f (σ.ρ (pw w (ratGL E a γ * g)) v)).1.1 (ratGL E a γ * g * (finGL E a (locGL E a w (pw w (ratGL E a γ * g))))⁻¹) =
          (f v).1.1 (ratGL E a γ * g) := by
        rw [hf]
        change (f v).1.1 (_ * _) = _
        rw [inv_mul_cancel_right]
      rw [hu, h1] at h2
      rw [← (P.cusp _ (f v).2).1.left γ g]
      exact h2.symm
    have hfv : f v = 0 := Subtype.ext (Subtype.ext hC)
    obtain ⟨-, hirr⟩ := (isIrreducible_iff σ.ρ).1 σ.6
    rcases hirr (LinearMap.ker f) (fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hf, hx, map_zero]) with h | h
    · exact (Submodule.eq_bot_iff _).1 h v hfv
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.TvApply
noncomputable section

open ValuativeRel GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V.Hi Matrix

namespace UpperTheory.V.Z.Desc.V0

section Rank

variable {R : Type} [CommRing R] {n : ℕ}

private theorem vv_sq (y w : Fin n → R) : vecMulVec y w * vecMulVec y w = (w ⬝ᵥ y) • vecMulVec y w := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => by ring)

private theorem tv_mul (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) :
    (1 + vecMulVec y w) * (1 - c • vecMulVec y w) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, mul_smul_comm, vv_sq, smul_smul, ← add_smul,
    show c + c * (w ⬝ᵥ y) = c * (1 + w ⬝ᵥ y) by ring, h, one_smul]
  abel

private theorem tv_mul' (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) :
    (1 - c • vecMulVec y w) * (1 + vecMulVec y w) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_assoc, vv_sq, smul_smul]
  rw [show (c * (w ⬝ᵥ y)) = c * (1 + w ⬝ᵥ y) - c by ring, h, sub_smul, one_smul]
  abel

private def tv (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) : GL (Fin n) R where
  val := 1 + vecMulVec y w
  inv := 1 - c • vecMulVec y w
  val_inv := tv_mul y w c h
  inv_val := tv_mul' y w c h

private theorem tv_apply (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) (a b : Fin n) :
    (tv y w c h : Matrix (Fin n) (Fin n) R) a b = (1 : Matrix (Fin n) (Fin n) R) a b + y a * w b := by
  simp [tv, vecMulVec_apply]

end Rank

section Loc

variable {k : Type} [Field k] {n : ℕ}

private theorem chr_of (ψ : AddChar k Circle) (t : Fin n → k) (g : GL (Fin n) k) (y w : Fin n → k) (i c : Fin n)
    (hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b + y a * w b)
    (hy : ∀ a, i < a → y a = 0) (hw : ∀ b, b ≤ i → w b = 0) (hc : (c : ℕ) = i + 1) (hwc : w c = 1) :
    chr ψ t g = (ψ (t i * y i) : ℂ) := by
  simp only [chr]
  congr 2
  have hic : i ≠ c := by
    intro h
    have := congrArg Fin.val h
    omega
  rw [Finset.sum_eq_single_of_mem (i, c) (by simp [hc])]
  · rw [hg, Matrix.one_apply_ne hic, hwc]
    ring
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    have hab' : a ≠ b := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [hg, Matrix.one_apply_ne hab']
    rcases lt_trichotomy a i with h | h | h
    · have h1 := Fin.lt_def.1 h
      rw [hw b (by rw [Fin.le_def]; omega)]
      ring
    · subst h
      exfalso
      apply hne
      have : b = c := by
        ext
        omega
      rw [this]
    · rw [hy a h]
      ring

private theorem unip_of (g : GL (Fin n) k) (y w : Fin n → k) (i : Fin n)
    (hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b + y a * w b)
    (hy : ∀ a, i < a → y a = 0) (hw : ∀ b, b ≤ i → w b = 0) : g ∈ unipB k (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [hg, Matrix.one_apply_ne hba.ne']
    by_cases ha : i < a
    · rw [hy a ha]
      ring
    · rw [hw b (le_trans hba.le (not_lt.1 ha))]
      ring
  · rw [hg]
    by_cases ha : i < a
    · simp [hy a ha]
    · simp [hw a (not_lt.1 ha)]

private theorem inv_rows (p : GL (Fin n) k) (i : Fin n)
    (hp : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1) :
    ∀ a, i < a → ∀ j, j ≤ a →
      ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = (1 : Matrix (Fin n) (Fin n) k) a j := by
  have hq : (p : Matrix (Fin n) (Fin n) k) * ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 :=
    Units.mul_inv p
  intro a
  induction h : n - (a : ℕ) using Nat.strong_induction_on generalizing a with
  | _ d ih =>
    intro ha j hj
    have e := congrFun (congrFun hq a) j
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at e
    · rw [(hp a ha).2, one_mul] at e
      exact e
    · intro m _ hma
      rcases lt_or_gt_of_ne hma with hlt | hgt
      · rw [(hp a ha).1 m hlt, zero_mul]
      · have hjm : j < m := lt_of_le_of_lt hj hgt
        have h1 := Fin.lt_def.1 hgt
        have h2 := m.isLt
        rw [ih (n - (m : ℕ)) (by omega) m rfl (lt_trans ha hgt) j hjm.le, Matrix.one_apply_ne (ne_of_gt hjm)]
        ring
    · simp

private theorem conj_eq (p : GL (Fin n) k) (x : Fin n → k) (c : Fin n) :
    (p : Matrix (Fin n) (Fin n) k) * (1 + vecMulVec x (Pi.single c 1)) =
      (1 + vecMulVec ((p : Matrix (Fin n) (Fin n) k) *ᵥ x) (((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c)) *
        (p : Matrix (Fin n) (Fin n) k) := by
  have hrow : ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c ᵥ* (p : Matrix (Fin n) (Fin n) k) = Pi.single c 1 := by
    funext b
    have e := congrFun (congrFun (Units.inv_mul p) c) b
    rw [Matrix.mul_apply] at e
    rw [Matrix.vecMul, dotProduct, e]
    rcases eq_or_ne b c with rfl | hb
    · simp
    · simp [hb, Matrix.one_apply_ne hb.symm]
  rw [Matrix.mul_add, mul_one, Matrix.mul_vecMulVec, Matrix.add_mul, one_mul, Matrix.vecMulVec_mul, hrow]

end Loc

section Val

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem lev_lt (ψ : AddChar k Circle) (hψ : Lev1 ψ) (y : k)
    (h : ∀ s : 𝒪[k], ψ (y * (s : k)) = 1) : valuation k y < 1 := by
  by_contra hy
  have hy1 : 1 ≤ valuation k y := not_lt.1 hy
  have hy0 : y ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hy1
    exact absurd hy1 (not_le.2 zero_lt_one)
  obtain ⟨x, hx, hne⟩ := hψ.2.2
  have hs : valuation k (x / y) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ (hx.trans hy1) zero_le'
  apply hne
  have := h ⟨x / y, hs⟩
  have hyx : y * ((⟨x / y, hs⟩ : 𝒪[k]) : k) = x := by
    show y * (x / y) = x
    field_simp
  rwa [hyx] at this

private theorem rowStep {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W)
    (ψ : AddChar k Circle) (t : Fin n → k) (l : W →ₗ[ℂ] ℂ)
    (hl : ∀ u ∈ unipB k (Fin n), ∀ v, l (τ u v) = chr ψ t u * l v) (v : W)
    (hv : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v)
    (p : GL (Fin n) k) (i c : Fin n) (hc : (c : ℕ) = i + 1)
    (hp : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1)
    (hW : l (τ p v) ≠ 0) (j : Fin n) (hj : j ≤ i) (s : 𝒪[k]) :
    ψ (t i * ((p : Matrix (Fin n) (Fin n) k) i j * (s : k))) = ψ (t i * (Pi.single j (s : k) : Fin n → k) i) := by
  have hci : i < c := by rw [Fin.lt_def, hc]; omega
  have hjc : j ≠ c := fun h => absurd (lt_of_le_of_lt hj hci) (by rw [h]; exact lt_irrefl c)
  set x : Fin n → k := Pi.single j (s : k) with hx
  set e : Fin n → k := Pi.single c 1 with he
  have hdot : e ⬝ᵥ x = 0 := by
    simp only [dotProduct, he, hx, Pi.single_apply]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    split_ifs with h1 h2
    · exact absurd (h2.symm.trans h1) hjc
    all_goals simp
  have h0 : (1 : k) * (1 + e ⬝ᵥ x) = 1 := by rw [hdot]; ring
  have hy : ∀ a, i < a → x a = 0 := fun a ha => by
    rw [hx, Pi.single_eq_of_ne]
    exact fun h => absurd (lt_of_le_of_lt hj ha) (by rw [h]; exact lt_irrefl j)
  have hw : ∀ b, b ≤ i → e b = 0 := fun b hb => by
    rw [he, Pi.single_eq_of_ne]
    exact fun h => absurd (lt_of_le_of_lt hb hci) (by rw [h]; exact lt_irrefl c)
  have hu := unip_of (tv x e 1 h0) x e i (tv_apply x e 1 h0) hy hw
  have hcu := chr_of ψ t (tv x e 1 h0) x e i c (tv_apply x e 1 h0) hy hw hc (by rw [he, Pi.single_eq_same])
  have hK : tv x e 1 h0 ∈ KO k (Fin n) := by
    have h00 : (1 : 𝒪[k]) * (1 + (Pi.single c 1 : Fin n → 𝒪[k]) ⬝ᵥ (Pi.single j s)) = 1 := by
      have hz : (Pi.single c 1 : Fin n → 𝒪[k]) ⬝ᵥ (Pi.single j s) = 0 := by
        simp only [dotProduct, Pi.single_apply]
        refine Finset.sum_eq_zero (fun b _ => ?_)
        split_ifs with h1 h2
        · exact absurd (h2.symm.trans h1) hjc
        all_goals simp
      rw [hz]; ring
    refine ⟨tv (Pi.single j s) (Pi.single c 1) 1 h00, ?_⟩
    apply Units.ext
    ext a b
    simp [tv, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.single_apply, he, hx]
    split_ifs <;> first | rfl | simp
  set y : Fin n → k := (p : Matrix (Fin n) (Fin n) k) *ᵥ x with hyd
  set w : Fin n → k := ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c with hwd
  have hyv : ∀ a, y a = (p : Matrix (Fin n) (Fin n) k) a j * (s : k) := by
    intro a
    simp [hyd, hx, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  have hinv := inv_rows p i hp
  have hy' : ∀ a, i < a → y a = 0 := fun a ha => by
    rw [hyv, (hp a ha).1 j (lt_of_le_of_lt hj ha), zero_mul]
  have hw' : ∀ b, b ≤ i → w b = 0 := fun b hb => by
    rw [hwd, hinv c hci b (le_of_lt (lt_of_le_of_lt hb hci))]
    exact Matrix.one_apply_ne (fun h => absurd (lt_of_le_of_lt hb hci) (by rw [h]; exact lt_irrefl b))
  have hwc : w c = 1 := by rw [hwd, hinv c hci c le_rfl, Matrix.one_apply_eq]
  have hdot' : w ⬝ᵥ y = 0 := by
    rw [dotProduct]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rcases le_or_gt b i with hb | hb
    · rw [hw' b hb, zero_mul]
    · rw [hy' b hb, mul_zero]
  have h1 : (1 : k) * (1 + w ⬝ᵥ y) = 1 := by rw [hdot']; ring
  have hu' := unip_of (tv y w 1 h1) y w i (tv_apply y w 1 h1) hy' hw'
  have hcu' := chr_of ψ t (tv y w 1 h1) y w i c (tv_apply y w 1 h1) hy' hw' hc hwc
  have hconj : p * tv x e 1 h0 = tv y w 1 h1 * p := by
    apply Units.ext
    exact conj_eq p x c
  have eq1 : l (τ (p * tv x e 1 h0) v) = chr ψ t (tv x e 1 h0) * l (τ p v) := by
    rw [map_mul, Module.End.mul_apply, hv _ hu hK, map_smul, map_smul, smul_eq_mul]
  have eq2 : l (τ (tv y w 1 h1 * p) v) = chr ψ t (tv y w 1 h1) * l (τ p v) := by
    rw [map_mul, Module.End.mul_apply, hl _ hu' (τ p v)]
  rw [hconj, eq2] at eq1
  have eq3 := mul_right_cancel₀ hW eq1
  rw [hcu, hcu'] at eq3
  have eq4 : ψ (t i * y i) = ψ (t i * x i) := Subtype.ext (by exact_mod_cast eq3)
  rw [hyv] at eq4
  exact eq4

set_option synthInstance.maxHeartbeats 200000 in
private theorem exists_mem_Kc_rows_unitriangular (p : GL (Fin n) k) (i : Fin n)
    (hp : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1)
    (hd : ∀ j, j ≤ i → valuation k ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1) :
    ∃ κ ∈ Kc k n 1, ∀ a, i ≤ a → (∀ j, j < a → ((p * κ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = 0) ∧
      ((p * κ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a a = 1 := by
  classical
  set P := (p : Matrix (Fin n) (Fin n) k) with hP
  let d : Fin n → k := fun j => if j ≤ i then P i j - (1 : Matrix (Fin n) (Fin n) k) i j else 0
  have hdv : ∀ j, valuation k (d j) < 1 := by
    intro j
    by_cases hj : j ≤ i
    · simp only [d, if_pos hj]
      exact hd j hj
    · simp only [d, if_neg hj, map_zero]
      exact zero_lt_one
  have hint : ∀ j, d j ∈ 𝒪[k] := fun j => (Valuation.mem_integer_iff _ _).2 (hdv j).le
  have hI := Valuation.integer.integers (valuation k)
  have hmax : ∀ x : 𝒪[k], valuation k (x : k) < 1 → x ∈ 𝓂[k] := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
    exact hx.ne
  let d₀ : Fin n → 𝒪[k] := fun j => ⟨d j, hint j⟩
  let y₀ : Fin n → 𝒪[k] := Pi.single i 1
  have hdot : d₀ ⬝ᵥ y₀ = d₀ i := by simp [y₀]
  have hu : IsUnit (1 + d₀ ⬝ᵥ y₀) := by
    rw [hdot, hI.isUnit_iff_valuation_eq_one, map_add (f := _), map_one]
    exact Valuation.map_one_add_of_lt _ (hdv i)
  obtain ⟨u, hu'⟩ := hu
  have hc : ((u⁻¹ : (𝒪[k])ˣ) : 𝒪[k]) * (1 + d₀ ⬝ᵥ y₀) = 1 := by rw [← hu']; exact u.inv_mul
  let M₀ : GL (Fin n) 𝒪[k] := tv y₀ d₀ _ hc
  let M : GL (Fin n) k := GeneralLinearGroup.map (algebraMap 𝒪[k] k) M₀
  have hM : ∀ a b, (M : Matrix (Fin n) (Fin n) k) a b =
      (1 : Matrix (Fin n) (Fin n) k) a b + (Pi.single i (1 : k) : Fin n → k) a * d b := by
    intro a b
    simp only [M, GeneralLinearGroup.map_apply, M₀, tv_apply, map_add (f := _), map_mul]
    congr 1
    · simp [Matrix.one_apply]
    · congr 1
      simp [y₀, Pi.single_apply]
  refine ⟨M⁻¹, ?_, ?_⟩
  · apply Subgroup.inv_mem
    refine ⟨M₀, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply GeneralLinearGroup.ext
    intro a b
    rw [GeneralLinearGroup.map_apply, tv_apply, map_add (f := _)]
    have hz : Ideal.Quotient.mk (𝓂[k] ^ 1) (y₀ a * d₀ b) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact Ideal.mul_mem_left _ _ (hmax _ (hdv b))
    rw [hz, add_zero]
    simp [Matrix.one_apply]
  · set Q := ((p * M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hQ
    have hq : ∀ a j, Q a j + Q a i * d j = P a j := by
      intro a j
      have h1 : ((p * M⁻¹ * M : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = P a j := by
        rw [inv_mul_cancel_right]
      rw [Units.val_mul, Matrix.mul_apply] at h1
      simp_rw [hM] at h1
      rw [← h1]
      simp [mul_add, Finset.sum_add_distrib, Matrix.one_apply, Pi.single_apply, Q]
    have hdi : 1 + d i = P i i := by simp [d]
    have hPii : P i i ≠ 0 := by
      intro h0
      have := hd i le_rfl
      rw [h0, zero_sub, Valuation.map_neg, Matrix.one_apply_eq, map_one] at this
      exact lt_irrefl _ this
    have hQi : ∀ a, Q a i * P i i = P a i := by
      intro a
      rw [← hdi, ← hq a i]
      ring
    intro a ha
    rcases ha.eq_or_lt with rfl | hlt
    · have hii : Q i i = 1 := by
        have := hQi i
        exact (mul_eq_right₀ hPii).1 this
      refine ⟨fun j hj => ?_, hii⟩
      have h2 := hq i j
      rw [hii, one_mul] at h2
      have hdj : d j = P i j - (1 : Matrix (Fin n) (Fin n) k) i j := by simp [d, hj.le]
      rw [hdj, Matrix.one_apply_ne hj.ne'] at h2
      linear_combination h2
    · obtain ⟨hz, h1⟩ := hp a hlt
      have hai : Q a i = 0 := by
        have := hQi a
        rw [hz i hlt] at this
        exact (mul_eq_zero.1 this).resolve_right hPii
      have hrow : ∀ j, Q a j = P a j := by
        intro j
        have := hq a j
        rw [hai, zero_mul, add_zero] at this
        exact this
      exact ⟨fun j hj => by rw [hrow]; exact hz j hj, by rw [hrow]; exact h1⟩

private theorem descent {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W)
    (ψ : AddChar k Circle) (t : Fin n → k) (l : W →ₗ[ℂ] ℂ) (hψ : Lev1 ψ) (ht : ∀ i, valuation k (t i) = 1)
    (hl : ∀ u ∈ unipB k (Fin n), ∀ v, l (τ u v) = chr ψ t u * l v) (v : W) (hlv : l v = 0)
    (hfix : ∀ κ ∈ Kc k n 1, τ κ v = v)
    (hv : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v) (r : ℕ) :
    r ≤ n - 1 → ∀ p : GL (Fin n) k,
      (∀ a : Fin n, r ≤ (a : ℕ) → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧
        (p : Matrix (Fin n) (Fin n) k) a a = 1) → l (τ p v) = 0 := by
  induction r with
  | zero =>
    intro _ p hp
    have hu : p ∈ unipB k (Fin n) :=
      (mem_unipB k).2 ⟨fun a j h => (hp a (Nat.zero_le _)).1 j h, fun a => (hp a (Nat.zero_le _)).2⟩
    rw [hl p hu v, hlv, mul_zero]
  | succ r ih =>
    intro hr p hp
    by_contra hW
    have hrn : r < n := by omega
    have hcn : r + 1 < n := by omega
    let i : Fin n := ⟨r, hrn⟩
    let c : Fin n := ⟨r + 1, hcn⟩
    have hpi : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧
        (p : Matrix (Fin n) (Fin n) k) a a = 1 := fun a ha => hp a (Fin.lt_def.1 ha)
    have hd : ∀ j, j ≤ i → valuation k ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := by
      intro j hj
      have hs := rowStep τ ψ t l hl v hv p i c rfl hpi hW j hj
      have h2 : ∀ s : 𝒪[k], ψ ((t i * ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)) * (s : k)) = 1 := by
        intro s
        have e : t i * ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) * (s : k) =
            t i * ((p : Matrix (Fin n) (Fin n) k) i j * (s : k)) - t i * (Pi.single j (s : k) : Fin n → k) i := by
          rw [Pi.single_apply]
          rcases eq_or_ne i j with h | h
          · subst h
            simp only [Matrix.one_apply_eq, if_true]
            ring
          · simp only [h, Matrix.one_apply_ne h, if_false]
            ring
        rw [e, AddChar.map_sub_eq_div, hs s, div_self']
      have h3 := lev_lt ψ hψ _ h2
      rw [map_mul, ht i, one_mul] at h3
      exact h3
    obtain ⟨κ, hκ, hpk⟩ := exists_mem_Kc_rows_unitriangular p i hpi hd
    apply hW
    have e : τ (p * κ) v = τ p v := by
      rw [map_mul, Module.End.mul_apply, hfix κ hκ]
    rw [← e]
    exact ih (by omega) (p * κ) (fun a ha => hpk a (Fin.le_def.2 ha))

end Val

theorem isoLe : IsoLe := by
  intro k _ _ _ _ n W _ _ τ ψ t l hψ ht hK v hv hlv
  obtain ⟨hl, hsep⟩ := hK
  have hfix : ∀ κ ∈ Kc k n 1, τ κ v = v := (Submodule.mem_inf.1 hv).1
  have heig : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v := by
    intro u h1 h2
    have h3 := (Submodule.mem_iInf _).1 (Submodule.mem_iInf _ |>.1 (Submodule.mem_inf.1 hv).2 u) ⟨h1, h2⟩
    exact Module.End.mem_eigenspace_iff.1 h3
  refine hsep v fun p hp => descent τ ψ t l hψ ht hl v hlv hfix heig (n - 1) le_rfl p fun a ha => ?_
  have hn : (a : ℕ) + 1 = n := by
    have := a.2
    omega
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hp a j hn, one_apply_ne (ne_of_gt hj)]
  · rw [hp a a hn, one_apply_eq]

end UpperTheory.V.Z.Desc.V0
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.KirMove
open UpperTheory.V.Z.Desc.V0

noncomputable section

open GlobalTheory.SmGL Matrix

namespace UpperTheory.V.Z.Desc.V0.KirillovTranslation

variable {k : Type} [Field k] {n : ℕ}

private def dg (e : Fin n → k) (he : ∀ i, e i ≠ 0) : GeneralLinearGroup (Fin n) k :=
  ⟨diagonal e, diagonal fun i => (e i)⁻¹, by simp [diagonal_mul_diagonal, he, ← diagonal_one],
    by simp [diagonal_mul_diagonal, he, ← diagonal_one]⟩

private theorem dg_inv_val (e : Fin n → k) (he : ∀ i, e i ≠ 0) :
    (((dg e he)⁻¹ : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal fun i => (e i)⁻¹ := rfl

private theorem dg_val (e : Fin n → k) (he : ∀ i, e i ≠ 0) :
    ((dg e he : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal e := rfl

private theorem conj_apply (e : Fin n → k) (he : ∀ i, e i ≠ 0) (u : GeneralLinearGroup (Fin n) k) (i j : Fin n) :
    ((dg e he * u * (dg e he)⁻¹ : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      e i * (u : Matrix (Fin n) (Fin n) k) i j * (e j)⁻¹ := by
  rw [Units.val_mul, Units.val_mul, dg_inv_val, dg_val, mul_diagonal, diagonal_mul]

private theorem inv_mul_apply (e : Fin n → k) (he : ∀ i, e i ≠ 0) (p : GeneralLinearGroup (Fin n) k) (i j : Fin n) :
    (((dg e he)⁻¹ * p : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (e i)⁻¹ * (p : Matrix (Fin n) (Fin n) k) i j := by
  rw [Units.val_mul, dg_inv_val, diagonal_mul]

private def ee (c : Fin n → k) (i : Fin n) : k :=
  ∏ j : Fin n with i ≤ j ∧ (j : ℕ) + 1 < n, c j

private theorem ee_ne (c : Fin n → k) (hc : ∀ i, c i ≠ 0) (i : Fin n) : ee c i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => hc j

private theorem ee_last (c : Fin n → k) (i : Fin n) (hi : (i : ℕ) + 1 = n) : ee c i = 1 := by
  unfold ee
  apply Finset.prod_eq_one
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hj
  omega

private theorem ee_step (c : Fin n → k) (i j : Fin n) (hij : (j : ℕ) = i + 1) : ee c i = c i * ee c j := by
  unfold ee
  have hi : i ∈ (Finset.univ.filter fun x : Fin n => i ≤ x ∧ (x : ℕ) + 1 < n) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, le_refl]
    have := j.isLt
    omega
  rw [← Finset.mul_prod_erase _ _ hi]
  congr 1
  apply Finset.prod_congr
  · ext x
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, ne_eq, Fin.ext_iff]
    omega
  · intro _ _
    rfl

end UpperTheory.V.Z.Desc.V0.KirillovTranslation

open UpperTheory.V.Z.Desc.V0.KirillovTranslation in
theorem UpperTheory.V.Z.Desc.V0.kirMove :
    KirMove := by
  intro k _ _ _ _ n W _ _ τ hK ψ t hψ hψ1 ht
  obtain ⟨ψ0, l0, hc0, hn0, hu0, hm0⟩ := hK
  obtain ⟨a, ha⟩ := GlobalTheory.LocGL.exists_unit_eq_mulShift hc0 hn0 hψ hψ1
  let c : Fin n → k := fun i => (a : k) * t i
  have hcE : ∀ i, c i = (a : k) * t i := fun _ => rfl
  have hc : ∀ i, c i ≠ 0 := fun i => mul_ne_zero a.ne_zero (ht i)
  let g : GeneralLinearGroup (Fin n) k := dg (ee c) (ee_ne c hc)
  have hτ : ∀ (x y : GeneralLinearGroup (Fin n) k) (w : W), τ (x * y) w = τ x (τ y w) := by
    intro x y w
    rw [map_mul, Module.End.mul_apply]
  refine ⟨l0 ∘ₗ τ g, ?_, ?_⟩
  · intro u hu v
    have hconj : g * u * g⁻¹ ∈ unipB k (Fin n) := by
      rw [mem_unipB] at hu ⊢
      refine ⟨fun i j hji => ?_, fun i => ?_⟩
      · rw [conj_apply, hu.1 i j hji, mul_zero, zero_mul]
      · rw [conj_apply, hu.2 i, mul_one, mul_inv_cancel₀ (ee_ne c hc i)]
    have hmove : τ g (τ u v) = τ (g * u * g⁻¹) (τ g v) := by
      rw [hτ, hτ, ← hτ g⁻¹, inv_mul_cancel, map_one, Module.End.one_apply]
    simp only [LinearMap.comp_apply]
    rw [hmove, hu0 _ hconj]
    congr 1
    unfold chr
    rw [ha, AddChar.mulShift_apply, Finset.mul_sum]
    have hs : (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1),
        (fun _ => (1 : k)) p.1 * ((g * u * g⁻¹ : GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1 p.2) =
        ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1),
          (a : k) * (t p.1 * (u : Matrix (Fin n) (Fin n) k) p.1 p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [conj_apply, ee_step c p.1 p.2 hp, hcE]
      have hE := ee_ne c hc p.2
      field_simp
    rw [hs]
  · intro v hv
    apply hm0 v
    intro q hq
    have hp : IsMirL (g⁻¹ * q) := by
      intro i j hi
      rw [inv_mul_apply, ee_last c i hi, inv_one, one_mul]
      exact hq i j hi
    have := hv _ hp
    simp only [LinearMap.comp_apply] at this
    rwa [← hτ, mul_inv_cancel_left] at this
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.RankEqOneOfInj
open UpperTheory.V.Z.Desc.V0

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.Z.Desc.V0.rank_eq_one_of_inj {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ W) (l : W →ₗ[ℂ] ℂ) (hne : S ≠ ⊥) (hinj : ∀ v ∈ S, l v = 0 → v = 0) :
    Module.rank ℂ ↥S = 1 := by
  have hle : Module.rank ℂ ↥S ≤ 1 := by
    have hi : Function.Injective (l ∘ₗ S.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have := hinj v.1 v.2 hv
      exact Subtype.ext this
    simpa using LinearMap.rank_le_of_injective _ hi
  have hne0 : Module.rank ℂ ↥S ≠ 0 := by
    rw [Ne, Submodule.rank_eq_zero]
    exact hne
  exact le_antisymm hle (Cardinal.one_le_iff_ne_zero.mpr hne0)

theorem UpperTheory.V.Z.Desc.V0.locE :
    KirMove → IsoNe → IsoLe → EOp → LocE := by
  intro hMove hNe hLe hE k _ _ _ _ n
  obtain ⟨ψ, a, j, T, hψ, hIsE, hTne, hTval, hrank⟩ := hE k n
  refine ⟨a, j, T.card, hIsE, Finset.card_pos.mpr hTne, ?_⟩
  intro W _ _ τ hsm hKir hfix
  have hψne : ψ ≠ 1 := by
    rintro rfl
    obtain ⟨_, _, x, _, hx⟩ := hψ
    exact hx (AddChar.one_apply x)
  have hone : ∀ t ∈ T, Module.rank ℂ ↥(isoPart τ ψ t) = 1 := by
    intro t ht
    have ht0 : ∀ i, t i ≠ 0 := by
      intro i h
      have := hTval t ht i
      rw [h, map_zero] at this
      exact zero_ne_one this
    obtain ⟨l, hl⟩ := hMove k n W τ hKir ψ t hψ.1 hψne ht0
    exact UpperTheory.V.Z.Desc.V0.rank_eq_one_of_inj _ l
      (hNe k n W τ hsm ψ t l hψ (hTval t ht) hl hfix)
      (hLe k n W τ ψ t l hψ (hTval t ht) hl)
  rw [hrank W τ, Finset.sum_congr rfl hone]
  simp
end

open UpperTheory.V.Z.J.D

namespace UpperTheory.V.Z.Desc.V0

theorem flathE : Flath :=
  flath (isotS secSp schurGL (boxIsot step) (piIsot (boxIsot step) (piIrr boxIrr)) (piIrr boxIrr) boxIrr) step boxIrr (piIrr boxIrr)
    schurGL infDim wtEx secSp

end UpperTheory.V.Z.Desc.V0

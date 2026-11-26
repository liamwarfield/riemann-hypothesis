module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace FiniteInfinitePlaceProduct

open Neutral.B1

variable {L : Type} [Field L] [NumberField L]

theorem loc_eq_one_of_val {ν : HChar L} {v : HeightOneSpectrum (𝓞 L)} (hu : ν.UnrAt v) (hv : ν.val v = 1)
    (x : (v.adicCompletion L)ˣ) : ν.loc v x = 1 := by
  set π := atFin v (unif v) with hπ
  have hπv : Valued.v (π : v.adicCompletion L) = WithZero.exp (-1) := unif_spec v
  have hπ1 : ν.loc v π = 1 := by rw [HChar.val_eq ν hu π (unif_spec v)]; exact hv
  have hx0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  set n := WithZero.log (Valued.v (x : v.adicCompletion L))
  have hxv : Valued.v (x : v.adicCompletion L) = WithZero.exp n := (WithZero.exp_log hx0).symm
  have hy : IsUnitAt v (x * π ^ n) := by
    show Valued.v ((x * π ^ n : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπv, hxv,
      ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
    simp
  have h2 := hu _ hy
  rw [map_mul, map_zpow, hπ1, _root_.one_zpow, mul_one] at h2
  exact h2

theorem inf_eq_prod (ν : HChar L) (k : Lˣ) :
    ν.inf k = ∏ w ∈ (Finset.univ : Finset (InfinitePlace L)), ν.locInf w (atInf w k) := by
  classical
  simp only [HChar.inf, HChar.locInf, infDiag, MonoidHom.comp_apply]
  have hp : ∀ (s : Finset (InfinitePlace L)) (f : InfinitePlace L → Lˣ →* Ideles L),
      (∏ w ∈ s, f w) k = ∏ w ∈ s, f w k := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [ha, ih, MonoidHom.mul_apply]
  rw [hp, map_prod]
  rfl


set_option maxHeartbeats 400000 in
theorem eq_one (ν : HChar L) (h : ∀ᶠ w in cofinite, ν.val w = 1) : ν = 1 := by
  classical
  have hνc : Continuous (ν : Ideles L →* ℂˣ) := ν.2.1
  have hfin := (GlobalTheory.Mem.UnrAe.finite_ramified ν).union (Filter.eventually_cofinite.mp h)
  set S := hfin.toFinset with hSdef
  have hS : ∀ v ∉ S, ν.UnrAt v ∧ ν.val v = 1 := by
    intro v hv
    simpa [S, not_or] using hv
  have hgood : ∀ v ∉ S, ∀ x, ν.loc v x = 1 := fun v hv x =>
    loc_eq_one_of_val (hS v hv).1 (hS v hv).2 x
  have hprod : ∀ k : Lˣ, ν.inf k * ∏ v ∈ S, ν.locK v k = 1 := by
    intro k
    have h0 : (ν.inf k * ∏ v ∈ S, ν.locK v k) *
        ∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), ν.val v ^ GlobalTheory.Mem.Chr.ordF v k = 1 :=
      GlobalTheory.Mem.Chr.CharModel.productRule (ν : GlobalTheory.Mem.Chr.HChar L) S (fun v hv => (hS v hv).1) k
    have hf : ∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), ν.val v ^ GlobalTheory.Mem.Chr.ordF v k = 1 := by
      apply finprod_eq_one_of_forall_eq_one
      intro v
      rw [finprod_eq_if]
      by_cases hv : v ∈ S
      · rw [if_neg (not_not.mpr hv)]
      · rw [if_pos hv, (hS v hv).2, _root_.one_zpow]
    rw [hf, mul_one] at h0
    exact h0
  have key : ∀ p : ((v : S) → (v.1.adicCompletion L)ˣ) ×
      ((w : (Finset.univ : Finset (InfinitePlace L))) → (w.1.Completion)ˣ),
      (∏ v : S, ν.loc v.1 (p.1 v)) *
        ∏ w : (Finset.univ : Finset (InfinitePlace L)), ν.locInf w.1 (p.2 w) = 1 := by
    have hc : Continuous fun p : ((v : S) → (v.1.adicCompletion L)ˣ) ×
        ((w : (Finset.univ : Finset (InfinitePlace L))) → (w.1.Completion)ˣ) =>
        (∏ v : S, ν.loc v.1 (p.1 v)) *
          ∏ w : (Finset.univ : Finset (InfinitePlace L)), ν.locInf w.1 (p.2 w) := by
      apply Continuous.mul
      · apply continuous_finsetProd
        intro v _
        exact (hνc.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele v.1)).comp
          ((continuous_apply v).comp continuous_fst)
      · apply continuous_finsetProd
        intro w _
        exact (hνc.comp (GlobalTheory.InfTypeLocal.continuous_infIdele L w.1)).comp
          ((continuous_apply w).comp continuous_snd)
    have hd := GroundTheory.Global.denseRange_units_prod_pi S (Finset.univ : Finset (InfinitePlace L))
    intro p
    refine hd.induction_on p (isClosed_eq hc continuous_const) (fun k => ?_)
    beta_reduce
    have e1 : (∏ v : S, ν.loc v.1 (Units.map ↑(algebraMap L (v.1.adicCompletion L)) k)) =
        ∏ v ∈ S, ν.locK v k := Finset.prod_coe_sort S (fun v => ν.locK v k)
    have e2 : (∏ w : (Finset.univ : Finset (InfinitePlace L)),
        ν.locInf w.1 (Units.map ↑(algebraMap L w.1.Completion) k)) = ν.inf k := by
      rw [inf_eq_prod]
      exact Finset.prod_coe_sort _ (fun w => ν.locInf w (atInf w k))
    exact (congrArg₂ (· * ·) e1 e2).trans (by rw [mul_comm]; exact hprod k)
  have hlocS : ∀ v ∈ S, ∀ x, ν.loc v x = 1 := by
    intro v hv x
    have h0 := key (Pi.mulSingle ⟨v, hv⟩ x, 1)
    dsimp only at h0
    rw [Fintype.prod_eq_single ⟨v, hv⟩ (fun v' hne => by rw [Pi.mulSingle_eq_of_ne hne, map_one]),
      Pi.mulSingle_eq_same] at h0
    simpa using h0
  have hinf : ∀ w x, ν.locInf w x = 1 := by
    intro w x
    have h0 := key (1, Pi.mulSingle ⟨w, Finset.mem_univ w⟩ x)
    dsimp only at h0
    rw [Fintype.prod_eq_single (⟨w, Finset.mem_univ w⟩ : (Finset.univ : Finset (InfinitePlace L)))
      (fun w' hne => by rw [Pi.mulSingle_eq_of_ne hne, map_one]), Pi.mulSingle_eq_same] at h0
    simpa using h0
  have hall := GlobalTheory.Mem.Chr.Determ.eq_one_of_components (ψ := (ν : Ideles L →* ℂˣ)) hνc
    (fun v k => by
      by_cases hv : v ∈ S
      · exact hlocS v hv _
      · exact hgood v hv _)
    (fun k => by
      have h0 := inf_eq_prod ν k
      rw [Finset.prod_eq_one (fun w _ => hinf w _)] at h0
      exact h0)
  exact Subtype.ext (MonoidHom.ext fun a => by rw [hall a]; rfl)

end FiniteInfinitePlaceProduct

theorem finite_infinite_product_eq_one : HeckeCharacterRigidity := by
  intro E _ _ _ ω ω' h
  have h1 := FiniteInfinitePlaceProduct.eq_one (ω * ω'⁻¹) (h.mono fun w hw => by
    rw [HChar.val_mul, HChar.val_inv, hw, mul_inv_cancel])
  exact mul_inv_eq_one.1 h1

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.UnipotentCharacter
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace UnipotentCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def chi (ψ : AddChar (Ad E) ℂ) (w : Pl E) : AddChar (w.adicCompletion E) ℂ where
  toFun y := ψ (sFin E (sLoc E w y))
  map_zero_eq_one' := by simp only [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' x y := by simp only [map_add (f := _), AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar (Ad E) ℂ) (w : Pl E) (y : w.adicCompletion E) :
    chi ψ w y = ψ (sFin E (sLoc E w y)) := rfl

theorem chi_cont {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (w : Pl E) : Continuous (chi ψ w) :=
  hψ.cont.comp ((continuous_const.prodMk continuous_id : Continuous fun x : Af E =>
    ((0, x) : InfiniteAdeleRing E × Af E)).comp (CuspSub.continuous_sLoc w))

theorem lastE_loc (w : Pl E) {k : ℕ} (y : UnipotentBlockColumnIndex a k k → w.adicCompletion E) :
    lastE k (fun t => sFin E (sLoc E w (y t))) = sFin E (sLoc E w (lastE k y)) := by
  unfold lastE
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem sum_of {X : Type} [AddCommMonoid X] [Module ℂ X] (P : X → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsm : ∀ (c : ℂ) x, P x → P (c • x)) {ι : Type}
    (T : Finset ι) (c : ι → ℂ) (f : ι → X) (hf : ∀ t, P (f t)) : P (∑ t ∈ T, c t • f t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using h0
  | insert t T ht ih => rw [Finset.sum_insert ht]; exact hadd _ _ (hsm _ _ (hf t)) ih

end UnipotentCharacter

open UnipotentCharacter in
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem whittaker_expansion_cuspidal : S2 → S9 → MirabolicColumnBlock → G0 → G5 → G5b → G7 := by
  intro hS2 hS9 hS10 hG0 hG5 hG5b E _ _ _ a ψ hψ S Y Y' hY hY' n m w hw hmw hSt
  obtain ⟨φ, hφY, φ', hφY', hsm, hsm', hlev, hlev', h1, hWh⟩ := hSt
  obtain ⟨-, -, i3, i4, i5, -, -, i8, -, i10, -⟩ := hG0 E a
  obtain ⟨g5a, g5r, -, g5c⟩ := hG5 E a ψ hψ
  obtain ⟨b1, b2, b3, b4, b5⟩ := hG5b E a S
  obtain ⟨s10dec, -, -, s10blk1, -⟩ := hS10 (w.adicCompletion E) a (m w + 1)
  have hpoly : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
    rw [pow_zero, mul_one, one_mul]
    exact le_of_eq (norm_Rt (infGL E a g) x)⟩
  obtain ⟨s0, sadd, ssmul, -, -, -⟩ := hS2 (InfinitePlace E) a (XB E a) (repI E a) hpoly
  let U : Set (GL (Fin a) (w.adicCompletion E)) := {u | repW a w u φ = φ} ∩ {u | repW a w u φ' = φ'}
  have hU : U ∈ 𝓝 (1 : GL (Fin a) (w.adicCompletion E)) := Filter.inter_mem (hlev w hw) (hlev' w hw)
  have hne : ∃ x, chi ψ w x ≠ 1 := by
    obtain ⟨y, hy⟩ := hψ.loc w
    exact ⟨y, hy⟩
  obtain ⟨T, c, η, r, hη1, hr1, hrMir, -, -, hmain⟩ :=
    hS9 (w.adicCompletion E) a (m w) hmw (chi ψ w) (chi_cont hψ w) hne (XB E a) (repW a w) U hU
  have inS : ∀ u, InS S (fl a w u : GA E a) := fun u v hv => i5 w v u (fun e => hv (e ▸ hw))
  have stab : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ u, ∀ x ∈ Z, repW a w u x ∈ Z :=
    fun Z hZ u x hx => hZ.stable _ (inS u) x hx
  have memZ : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, ∑ t ∈ T, c t • repW a w t x ∈ Z :=
    fun Z hZ x hx => Z.sum_mem fun t _ => Z.smul_mem _ (stab Z hZ t x hx)
  have smZ : ∀ x : XB E a, SmV (repI E a) x → SmV (repI E a) (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ s0 sadd ssmul T c _ fun t => b1 _ x hx
  have levZ : ∀ x : XB E a, Lev S x → Lev S (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ b5 b4 b3 T c _ fun t => b2 _ x hx

  have key : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
      ∀ g' : GA E a, cLoc w g' = 1 → ∀ h, GlobalTheory (m w + 1) h →
      Wh ψ (∑ t ∈ T, c t • repW a w t x) (g' * fl a w h) = η h * Wh ψ x (g' * fl a w (r h)) := by
    intro Z hZ x hx hxU g' hg' h hh
    obtain ⟨Λ, hΛ⟩ := g5a g'
    have hcond : ∀ z ∈ Z, ∀ y : UnipotentBlockColumnIndex a (m w + 1) (m w + 1) → w.adicCompletion E,
        (Λ : XB E a →ₗ[ℂ] ℂ) (repW a w (blkU y) z) = chi ψ w (lastE (m w + 1) y) * (Λ : XB E a →ₗ[ℂ] ℂ) z := by
      intro z hz y
      show Λ _ = _ * Λ _
      rw [hΛ _ (hZ.good _ (stab Z hZ _ z hz)),
        hΛ _ (hZ.good _ hz), repW_apply, g5r, i8 w g' hg', i10,
        (g5c z (hZ.good _ hz)).2.2 (m w + 1) (Nat.succ_pos _), lastE_loc, chi_apply]
    have := hmain x hxU Z (stab Z hZ) hx (Λ : XB E a →ₗ[ℂ] ℂ) hcond h hh
    change Λ _ = η h * Λ _ at this
    rw [hΛ _ (hZ.good _ (stab Z hZ _ _ (memZ Z hZ x hx))), hΛ _ (hZ.good _ (stab Z hZ _ _ hx)),
      repW_apply, repW_apply, g5r, g5r] at this
    exact this
  refine ⟨_, memZ Y hY φ hφY, _, memZ Y' hY' φ' hφY', smZ φ hsm, smZ φ' hsm', levZ φ hlev, levZ φ' hlev', ?_, ?_⟩
  · have := key Y hY φ hφY (fun u hu => hu.1) 1 (map_one _) 1 s10blk1
    rw [hr1] at this
    simp only [map_one, mul_one] at this
    rw [this]
    exact mul_ne_zero hη1 h1
  · intro g hg
    obtain ⟨hgI, hgL⟩ := hg
    have hgw : Mir (m w + 1) (cLoc w g) := by simpa using hgL w
    obtain ⟨y, h, hh, hdec⟩ := s10dec _ hgw
    set g' : GA E a := g * (fl a w (cLoc w g))⁻¹ with hg'def
    have hg' : cLoc w g' = 1 := by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]
    have red : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
        Wh ψ (∑ t ∈ T, c t • repW a w t x) g =
          ψ (lastE (m w + 1) fun t => sFin E (sLoc E w (y t))) * (η h * Wh ψ x (g' * fl a w (r h))) := by
      intro Z hZ x hx hxU
      have e : g = blkU (fun t => sFin E (sLoc E w (y t))) * (g' * fl a w h) := by
        rw [← i10, ← mul_assoc, ← i8 w g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]
      rw [e, (g5c _ (hZ.good _ (memZ Z hZ x hx))).2.2 (m w + 1) (Nat.succ_pos _), key Z hZ x hx hxU g' hg' h hh]
    rw [red Y hY φ hφY (fun u hu => hu.1), red Y' hY' φ' hφY' (fun u hu => hu.2)]
    by_cases hη : η h = 0
    · rw [hη]; simp
    congr 2
    refine hWh _ ⟨?_, fun v => ?_⟩
    · rw [map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]
      exact hgI
    · rcases eq_or_ne v w with rfl | hv
      · rw [map_mul, hg', i4, one_mul]
        exact hrMir h hh hη
      · rw [map_mul, hg'def, map_mul, map_inv, i5 w v _ hv, i5 w v _ hv, inv_one, mul_one, mul_one]
        simpa [hv] using hgL v

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CharacterNondegenerate
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace CharacterNondegenerate

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def chi (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ := ψ.compAddMonoidHom (sInf E).toAddMonoidHom

theorem chi_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chi ψ z = ψ (sInf E z) := rfl

theorem pInf_sInf (z : Cinf E) : pInf E (sInf E z) = z := (infEq E).symm_apply_apply z

theorem pFin_sInf (z : Cinf E) : pFin E (sInf E z) = 0 := rfl

theorem sInf_mul (z : Cinf E) (x : Ad E) : sInf E z * x = sInf E (z * pInf E x) := by
  refine ad_ext ?_ ?_
  · rw [map_mul, pInf_sInf, pInf_sInf]
  · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

theorem continuous_chi {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : Continuous (chi ψ) :=
  hψ.cont.comp continuous_sInf

theorem chi_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E) (hz : ∀ w, chi ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by rw [sInf_mul]; exact hz _
  have hd0 : d = 0 := by
    by_contra h0
    obtain ⟨w⟩ := nonempty_pl (E := E)
    have h1 : sInf E z * algebraMap E (Ad E) d⁻¹ = 1 := by
      rw [hd, ← map_mul, mul_inv_cancel₀ h0, map_one]
    have h2 := congrArg (fun x => pLoc E w (pFin E x)) h1
    simp only [map_mul, pFin_sInf, zero_mul, map_zero, map_one] at h2
    exact zero_ne_one h2
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

theorem sInf_lastE (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Cinf E) :
    sInf E (lastE k y) = lastE k (fun t => sInf E (y t)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lastE, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem polyBd : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
  show ‖Rt E a (infGL E a g) x‖ ≤ 1 * _ ^ 0 * ‖x‖
  rw [pow_zero, mul_one, one_mul, norm_Rt]⟩

end CharacterNondegenerate

open CharacterNondegenerate in
theorem whittaker_nondegenerate_character : S7 → MirabolicColumnBlock → G0 → G5 → G6 := by
  intro hS7 hS10 hG0 hG5 E _ _ _ a ψ hψ S Y Y' hY hY' n m hn hSt
  obtain ⟨φ, hφY, φ', hφY', hsm, hsm', hlev, hlev', hW1, hWeq⟩ := hSt
  obtain ⟨hcI, hcLI, hcIf, -, -, -, hcomm, -, hb, -⟩ := hG0 E a
  obtain ⟨hΛ, hRt, hGood, hlaw⟩ := hG5 E a ψ hψ
  obtain ⟨hdec, -, -, hBlk1, -⟩ := hS10 (Cinf E) a (n + 1)
  obtain ⟨η, r, hη1, hr1, hmir, -, -, hv⟩ := hS7 (InfinitePlace E) a (XB E a) (repI E a) polyBd n hn (chi ψ)
    (continuous_chi hψ) (fun z => hψ.norm _) (chi_nondeg hψ) Set.univ Filter.univ_mem
  have memY : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ g, ∀ x ∈ Z, repI E a g x ∈ Z :=
    fun Z hZ g x hx => hZ.stable _ (fun w _ => hcLI w g) x hx
  have whB : ∀ x : XB E a, Good ψ (a - 1) x → ∀ (y : UnipotentBlockColumnIndex a (n + 1) (n + 1) → Cinf E) (g : GA E a),
      Wh ψ x (infGL E a (blkU y) * g) = chi ψ (lastE (n + 1) y) * Wh ψ x g := by
    intro x hx y g
    rw [hb, chi_apply, sInf_lastE]
    exact (hlaw x hx).2.2 (n + 1) n.succ_pos _ g
  have lawOf : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ g' : GA E a, cInf g' = 1 →
      ∀ Λ : XB E a →L[ℂ] ℂ, (∀ x : XB E a, Good ψ (a - 1) x → Λ x = Wh ψ x g') →
      ∀ x ∈ Z, ∀ y : UnipotentBlockColumnIndex a (n + 1) (n + 1) → Cinf E,
        Λ (repI E a (blkU y) x) = chi ψ (lastE (n + 1) y) * Λ x := by
    intro Z hZ g' hg' Λ hΛg x hx y
    have hx' := hZ.good x hx
    change Λ (Rt E a (infGL E a (blkU y)) x) = _
    rw [hΛg _ (hGood x _ hx'), hΛg x hx', hRt, hcomm g' hg', whB x hx']
  have levOf : ∀ x x' : XB E a, Lev S x → (∀ Z : Submodule ℂ (XB E a), IsClosed (Z : Set (XB E a)) →
      (∀ g, ∀ y ∈ Z, repI E a g y ∈ Z) → x ∈ Z → x' ∈ Z) → Lev S x' := by
    intro x x' hx hZ w hw
    refine Filter.mem_of_superset (hx w hw) fun u hu => ?_
    have hu' : Rt E a (fl a w u) x = x := hu
    let T : XB E a →L[ℂ] XB E a := Rt E a (fl a w u) - ContinuousLinearMap.id ℂ _
    have hmem : ∀ y, T y = 0 ↔ Rt E a (fl a w u) y = y := fun y => by simp [T, sub_eq_zero]
    have hk := hZ _ T.isClosed_ker (fun g y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        refine (hmem _).2 ?_
        have hy' := (hmem y).1 hy
        change Rt E a (fl a w u) (Rt E a (infGL E a g) y) = Rt E a (infGL E a g) y
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcomm _ (hcIf w u), map_mul,
          ContinuousLinearMap.mul_apply, hy'])
      (LinearMap.mem_ker.2 ((hmem x).2 hu'))
    rw [LinearMap.mem_ker] at hk
    exact (hmem x').1 hk
  obtain ⟨v, hvs, hvP⟩ := hv φ hsm
  obtain ⟨v', hvs', hvP'⟩ := hv φ' hsm'
  obtain ⟨hvY, hvΛ⟩ := hvP Y hY.closed (memY Y hY) hφY
  obtain ⟨hvY', hvΛ'⟩ := hvP' Y' hY'.closed (memY Y' hY') hφY'
  have conv : ∀ (g' : GA E a) (Λ : XB E a →L[ℂ] ℂ), (∀ x : XB E a, Good ψ (a - 1) x → Λ x = Wh ψ x g') →
      ∀ x : XB E a, Good ψ (a - 1) x → ∀ k, Λ (repI E a k x) = Wh ψ x (g' * infGL E a k) := by
    intro g' Λ hΛg x hx k
    change Λ (Rt E a (infGL E a k) x) = _
    rw [hΛg _ (hGood x _ hx), hRt]
  have hgY := hY.good
  have hgY' := hY'.good
  refine ⟨v, hvY, v', hvY', hvs, hvs', levOf φ v hlev fun Z hc hs hx => (hvP Z hc hs hx).1,
    levOf φ' v' hlev' fun Z hc hs hx => (hvP' Z hc hs hx).1, ?_, ?_⟩
  · obtain ⟨Λ₁, hΛ₁⟩ := hΛ 1
    have e1 := hvΛ Λ₁ (lawOf Y hY 1 (map_one _) Λ₁ hΛ₁) 1 hBlk1
    rw [conv 1 Λ₁ hΛ₁ v (hgY v hvY), conv 1 Λ₁ hΛ₁ φ (hgY φ hφY), hr1, map_one, one_mul] at e1
    rw [e1]
    exact mul_ne_zero hη1 hW1
  · intro g hg
    obtain ⟨hgI, hgL⟩ := hg
    obtain ⟨y, h, hh, hyh⟩ := hdec (cInf g) hgI
    obtain ⟨g', hg'⟩ : ∃ g' : GA E a, g' = (infGL E a (cInf g))⁻¹ * g := ⟨_, rfl⟩
    have hg'1 : cInf g' = 1 := by rw [hg', map_mul, map_inv, hcI, inv_mul_cancel]
    have hgeq : g = infGL E a (blkU y) * (g' * infGL E a h) := by
      rw [hcomm g' hg'1 h, ← mul_assoc, ← map_mul, ← hyh, hg', mul_inv_cancel_left]
    obtain ⟨Λ, hΛg⟩ := hΛ g'
    have e := hvΛ Λ (lawOf Y hY g' hg'1 Λ hΛg) h hh
    have e' := hvΛ' Λ (lawOf Y' hY' g' hg'1 Λ hΛg) h hh
    rw [conv g' Λ hΛg v (hgY v hvY), conv g' Λ hΛg φ (hgY φ hφY)] at e
    rw [conv g' Λ hΛg v' (hgY' v' hvY'), conv g' Λ hΛg φ' (hgY' φ' hφY')] at e'
    rw [hgeq, whB v (hgY v hvY), whB v' (hgY' v' hvY'), e, e']
    by_cases hη : η h = 0
    · simp [hη]
    · rw [hWeq _ ⟨?_, fun w => ?_⟩]
      · rw [map_mul, hg'1, one_mul, hcI]
        exact hmir h hh hη
      · rw [map_mul, hcLI, mul_one, hg', map_mul, map_inv, hcLI, inv_one, one_mul]
        exact hgL w

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.GeneralLinearEntryConvergence
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace GeneralLinearEntryConvergence

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem tendsto_af {ι : Type} {l : Filter ι} (x : Af E) (z : ι → Af E)
    (h1 : ∀ w : Pl E, ∀ᶠ t in l, z t w = x w)
    (h2 : ∀ᶠ t in l, ∀ w : Pl E, z t w - x w ∈ w.adicCompletionIntegers E) :
    Tendsto z l (𝓝 x) := by
  classical
  let A : ∀ w : Pl E, Set (w.adicCompletion E) := fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))
  let sm : (∀ w : Pl E, A w) → Af E := fun y =>
    RestrictedProduct.structureMap (fun w : Pl E => w.adicCompletion E) A cofinite y
  have hsm : Continuous sm :=
    (RestrictedProduct.isEmbedding_structureMap (R := fun w : Pl E => w.adicCompletion E) (A := A)
      (𝓕 := cofinite)).continuous
  let u0 : ∀ w : Pl E, A w := fun w => ⟨0, zero_mem (w.adicCompletionIntegers E)⟩
  let u : ι → ∀ w : Pl E, A w := fun t w =>
    if h : z t w - x w ∈ w.adicCompletionIntegers E then ⟨_, h⟩ else u0 w
  have hu : Tendsto u l (𝓝 u0) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h1 w] with t ht
    have h0 : z t w - x w ∈ w.adicCompletionIntegers E := by
      rw [ht, sub_self]; exact zero_mem _
    simp only [u, dif_pos h0]
    apply Subtype.ext
    change (0 : w.adicCompletion E) = z t w - x w
    rw [ht, sub_self]
  have hv : Tendsto (fun t => sm (u t)) l (𝓝 (sm u0)) := (hsm.tendsto u0).comp hu
  have e0 : sm u0 = 0 := by
    ext w
    rfl
  rw [e0] at hv
  have hv' : Tendsto (fun t => z t - x) l (𝓝 0) := by
    refine hv.congr' ?_
    filter_upwards [h2] with t ht
    apply Subtype.ext
    funext w
    change (u t w : w.adicCompletion E) = z t w - x w
    simp only [u, dif_pos (ht w)]
  have := (tendsto_const_nhds (x := x)).add hv'
  simpa using this

theorem tendsto_ad {ι : Type} {l : Filter ι} (y : Ad E) (z : ι → Ad E) (h1 : ∀ t, (z t).1 = y.1)
    (h2 : Tendsto (fun t => (z t).2) l (𝓝 y.2)) : Tendsto z l (𝓝 y) := by
  refine (Prod.tendsto_iff _ _).2 ⟨?_, h2⟩
  simp only [h1]
  exact tendsto_const_nhds

theorem tendsto_gl {ι : Type} {l : Filter ι} (x : GA E a) (z : ι → GA E a)
    (h1 : ∀ i j, Tendsto (fun t => (z t).val i j) l (𝓝 (x.val i j)))
    (h2 : ∀ i j, Tendsto (fun t => (z t)⁻¹.val i j) l (𝓝 (x⁻¹.val i j))) : Tendsto z l (𝓝 x) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine Tendsto.prodMk_nhds ?_ ?_
  · exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h1 i j
  · exact (MulOpposite.continuous_op.tendsto _).comp
      (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h2 i j)

variable [_root_.NumberField.IsTotallyComplex E]

theorem tendsto_entry (S : Finset (Pl E)) (x : GA E a) (z : Finset (Pl E) → GA E a)
    (hinf : ∀ T, cInf (z T) = cInf x) (hloc : ∀ T w, (w ∈ S ∨ w ∈ T) → cLoc w (z T) = cLoc w x)
    (hone : ∀ T w, w ∉ S → w ∉ T → cLoc w (z T) = 1) (i j : Fin a) :
    Tendsto (fun T => (z T).val i j) atTop (𝓝 (x.val i j)) := by
  classical
  refine tendsto_ad _ _ (fun T => ?_) (tendsto_af _ _ (fun w => ?_) ?_)
  · have h := congrArg (fun m : GL (Fin a) (Cinf E) => m.val i j) (hinf T)
    exact (infEq E).symm.injective h
  · filter_upwards [eventually_ge_atTop {w}] with T hT
    exact congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j)
      (hloc T w (Or.inr (hT (Finset.mem_singleton_self w))))
  · have hx : ∀ᶠ w in cofinite, (x.val i j).2 w ∈ w.adicCompletionIntegers E := (x.val i j).2.2
    set F := (Filter.eventually_cofinite.1 hx).toFinset
    filter_upwards [eventually_ge_atTop F] with T hT w
    by_cases hw : w ∈ S ∨ w ∈ T
    · have h := congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j) (hloc T w hw)
      change ((z T).val i j).2 w = (x.val i j).2 w at h
      rw [h, sub_self]
      exact zero_mem _
    · rw [not_or] at hw
      have h := congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j) (hone T w hw.1 hw.2)
      change ((z T).val i j).2 w = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j at h
      have hwF : w ∉ F := fun h' => hw.2 (hT h')
      have hxw : (x.val i j).2 w ∈ w.adicCompletionIntegers E := by
        by_contra hc
        exact hwF ((Filter.eventually_cofinite.1 hx).mem_toFinset.2 hc)
      refine sub_mem ?_ hxw
      rw [h, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _

theorem step1 (hG : G0) (S : Finset (Pl E)) (f : GA E a → ℂ)
    (hf : ∀ w, w ∉ S → ∀ h, cLoc w h = 1 → f h = 0 → ∀ u, f (h * fl a w u) = 0)
    (g g₀ : GA E a) (hinf : cInf g₀ = cInf g) (hS : ∀ w ∈ S, cLoc w g₀ = cLoc w g) (hIn : InS S g₀)
    (h0 : f g₀ = 0) (T : Finset (Pl E)) :
    ∃ h : GA E a, f h = 0 ∧ cInf h = cInf g ∧ (∀ w, (w ∈ S ∨ w ∈ T) → cLoc w h = cLoc w g) ∧
      (∀ w, w ∉ S → w ∉ T → cLoc w h = 1) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -⟩ := hG E a
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨g₀, h0, hinf, fun w hw => ?_, fun w hw _ => hIn w hw⟩
    rcases hw with hw | hw
    · exact hS w hw
    · simp at hw
  | insert w T hwT ih =>
    obtain ⟨h, hf0, hi, hl, ho⟩ := ih
    by_cases hwS : w ∈ S
    · refine ⟨h, hf0, hi, fun v hv => ?_, fun v hv hv' => ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')⟩
      rcases hv with hv | hv
      · exact hl v (Or.inl hv)
      · rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hl v (Or.inl hwS)
        · exact hl v (Or.inr hv)
    · refine ⟨h * fl a w (cLoc w g), hf w hwS h (ho w hwS hwT) hf0 _, ?_, fun v hv => ?_, fun v hv hv' => ?_⟩
      · rw [map_mul, h3, mul_one, hi]
      · rw [map_mul]
        by_cases hvw : v = w
        · subst hvw
          rw [h4, ho v hwS hwT, one_mul]
        · rw [h5 _ _ _ hvw, mul_one]
          rcases hv with hv | hv
          · exact hl v (Or.inl hv)
          · exact hl v (Or.inr ((Finset.mem_insert.1 hv).resolve_left hvw))
      · have hvw : v ≠ w := fun e => hv' (e ▸ Finset.mem_insert_self w T)
        rw [map_mul, h5 _ _ _ hvw, mul_one]
        exact ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')

end GeneralLinearEntryConvergence

open GeneralLinearEntryConvergence in
theorem convergence_entries_general_linear : G0 → PlacewiseToOutsideS := by
  intro hG E _ _ _ a S f hfc hf g g₀ hinf hS hIn h0
  choose H hH using step1 hG S f hf g g₀ hinf hS hIn h0
  have hT : Tendsto H atTop (𝓝 g) := by
    refine tendsto_gl g H (tendsto_entry S g H (fun T => (hH T).2.1) (fun T => (hH T).2.2.1)
      (fun T => (hH T).2.2.2)) (tendsto_entry S g⁻¹ (fun T => (H T)⁻¹) (fun T => ?_) (fun T w hw => ?_)
      (fun T w hw hw' => ?_))
    · rw [map_inv, map_inv, (hH T).2.1]
    · rw [map_inv, map_inv, (hH T).2.2.1 w hw]
    · rw [map_inv, (hH T).2.2.2 w hw hw', inv_one]
  have h1 := (hfc.tendsto g).comp hT
  have h2 : Tendsto (f ∘ H) atTop (𝓝 0) := by
    have e : f ∘ H = fun _ => 0 := funext fun T => (hH T).1
    rw [e]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WeilJacquetShalikaLaw
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.jumpWindows

namespace WeilJacquetShalikaLaw

section Loc

variable {F : Type} [Field F] {a : ℕ}

def WS (χ : AddChar F ℂ) (a : ℕ) : Submodule ℂ (GL (Fin a) F → ℂ) where
  carrier := {W | ∀ n ∈ GroundTheory.Automorphic.Iwasawa.unipotent F a, ∀ g,
    W (n * g) = GroundTheory.Automorphic.Whittaker.psiN χ n * W g}
  add_mem' {W W'} hW hW' n hn g := by
    simp only [Pi.add_apply, hW n hn g, hW' n hn g, mul_add]
  zero_mem' n hn g := by simp
  smul_mem' c W hW n hn g := by
    simp only [Pi.smul_apply, smul_eq_mul, hW n hn g]
    ring

theorem WS_stable (χ : AddChar F ℂ) (a : ℕ) :
    ∀ g, ∀ v ∈ WS χ a, GlobalTheory.PRep.rightReg ℂ (GL (Fin a) F) ℂ g v ∈ WS χ a := by
  intro g v hv n hn x
  change v (n * x * g) = _ * v (x * g)
  rw [mul_assoc]
  exact hv n hn _

def rhoW (χ : AddChar F ℂ) (a : ℕ) : Representation ℂ (GL (Fin a) F) (WS χ a) :=
  GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) F) ℂ) (WS χ a) (WS_stable χ a)

@[simp] theorem rhoW_apply (χ : AddChar F ℂ) (g x : GL (Fin a) F) (v : WS χ a) :
    (rhoW χ a g v : GL (Fin a) F → ℂ) x = (v : GL (Fin a) F → ℂ) (x * g) := rfl

def ev (χ : AddChar F ℂ) (a : ℕ) : WS χ a →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) F => ℂ) 1).comp (WS χ a).subtype

theorem ev_apply (χ : AddChar F ℂ) (v : WS χ a) : ev χ a v = (v : GL (Fin a) F → ℂ) 1 := rfl

theorem sd_eq (M : Matrix (Fin a) (Fin a) F) :
    GroundTheory.Automorphic.Whittaker.superdiagSum M = ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, M p.1 p.2 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  rfl

end Loc

theorem exists_unit_one_add_generator {a : ℕ} (B : Multiset ℂˣ) (hB : B.card = a) : ∃ z : Fin a → ℂˣ, B = Finset.univ.val.map z := by
  subst hB
  refine ⟨fun i => B.toList.get ⟨i, by simp⟩, ?_⟩
  rw [Fin.univ_val_map]
  conv_lhs => rw [← Multiset.coe_toList B]
  congr 1
  refine List.ext_get (by simp) fun n h1 h2 => ?_
  simp

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def psiW (ψ : AddChar (Ad E) ℂ) (w : Pl E) : AddChar (w.adicCompletion E) ℂ :=
  ψ.compAddMonoidHom ((sFin E).toAddMonoidHom.comp (sLoc E w).toAddMonoidHom)

theorem psiOK {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {w : Pl E} (hc : Cond ψ w) :
    PositivityTheory.JacquetShalikaLocal.PsiOK (psiW ψ w) := by
  obtain ⟨h1, ϖ, y, hϖ, hy, hne⟩ := hc
  refine ⟨fun x hx => h1 x (by rw [← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w]; exact hx), ⟨y, ?_, hne⟩, fun x => hψ.norm _⟩
  refine (SetLike.ext_iff.1 (PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.O_eq w) _).2 ?_
  have hu := PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.isUnifV_uniformizer w
  change Valued.v (_ * y) ≤ 1
  change Valued.v (ϖ * y) ≤ 1 at hy
  rw [map_mul] at hy ⊢
  rw [hu]
  rw [hϖ] at hy
  exact hy

theorem dot_eLast {k : ℕ} (y : UnipotentBlockColumnIndex a k k → Ad E) : dot (eLast a k) y = lastE k y := by
  simp only [dot, eLast, lastE]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem law [_root_.NumberField.IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ} {f : GA E a → ℂ}
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) g, f (blkU y * g) = ψ (lastE k y) * f g)
    (w : Pl E) (n : GL (Fin a) (w.adicCompletion E)) (hn : n ∈ GroundTheory.Automorphic.Iwasawa.unipotent _ a)
    (g : GA E a) : f (fl a w n * g) = GroundTheory.Automorphic.Whittaker.psiN (psiW ψ w) n * f g := by
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w n (fun i j hij => hn.1 hij) hn.2
  have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ f (fun k hk y g => by rw [dot_eLast]; exact hf k hk y g) _ t1 t2 g
  change f (finGL E a (locGL E a w n) * g) = _
  rw [this, t3, GroundTheory.Automorphic.Whittaker.psiN, sd_eq]
  rfl

theorem whitW (w : Pl E) (χ : AddChar (w.adicCompletion E) ℂ) :
    PositivityTheory.JacquetShalikaLocal.Whit (rhoW χ a) χ (ev χ a) := by
  intro g hg u
  rw [ev_apply, ev_apply, rhoW_apply, one_mul]
  have := u.2 g hg 1
  rwa [mul_one] at this

end WeilJacquetShalikaLaw

theorem whittaker_uniqueness_local : PositivityTheory.JacquetShalikaLocal.L7 → PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂ → G0 → G5 → G9 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc B φ hφ hsat h hh hWh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w u)
    rw [← hΛ' 0 hφ, map_zero]
  obtain ⟨z, hz⟩ := WeilJacquetShalikaLaw.exists_unit_one_add_generator B hsat.2.2.1
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w (n := a), Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = 0 := by
    change Wh ψ φ (h * fl a w 1) = 0
    rw [map_one, mul_one]
    exact hWh
  by_cases h0 : vs = 0
  · exact congrFun (congrArg Subtype.val h0) u
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · rw [← hz]
      apply Subtype.ext
      have e := map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a)
        (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at e
      rw [e, Submodule.coe_smul]
      funext x
      obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w x)
      have hfin := finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v
      have hfin2 := finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ
      have e1 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin
      have e2 := (Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2
      have e3 := hsat.2.2.2 ϖ hϖ j hj
      have key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w (n := a),
          (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x =
            Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ) := by
        intro c
        rw [map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]
        change _ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)
        rw [hrt, smul_eq_mul]
        change _ * Wh ψ φ (h * fl a w (x * c.out)) = _
        rw [map_mul, mul_assoc]
      have LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w (n := a))
          (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ j) φ) := by
        rw [heckeVec, heckeVec]
        exact e1.trans ((finsum_congr key).trans e2.symm)
      refine LHS.trans ?_
      rw [e3, map_smul, hΛ' φ hφ]
      rfl
  have heig := (hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv
  have := hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig
    (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1, zero_mul] at this
  exact this

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AlmostEverywhereSphericalOfG1
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalAlmostEverywhereOfBounded
noncomputable section

open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.LFun Formalism.L2.Host PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.StrongMultOne

theorem spherical_almost_everywhere_of_bounded : G1 → AlmostEverywhereSpherical := by
  intro g1 E _ _ _ a π hN φ hφ x hx
  have hex : ∀ v : π.V, ∃ y : XB E a, (y : GA E a → ℂ) = v.1.1 := fun v =>
    (g1 E a π hN v.1 v.2).imp fun _ h => h.1
  choose f hf using hex
  let ι : π.V →ₗ[ℂ] XB E a :=
    { toFun := f
      map_add' := fun u v => by
        refine DFunLike.coe_injective ?_
        rw [BoundedContinuousFunction.coe_add, hf, hf, hf]
        rfl
      map_smul' := fun c v => by
        refine DFunLike.coe_injective ?_
        funext g
        rw [hf]
        change _ = c • f v g
        rw [congrFun (hf v) g]
        rfl }
  have hι : ∀ v, (ι v : GA E a → ℂ) = v.1.1 := hf
  filter_upwards [AeFix.eventually_mem_fixed E a π ⟨φ, hφ⟩] with w hw B hB
  by_cases h0 : x = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have hxι : ι ⟨φ, hφ⟩ = x := DFunLike.coe_injective ((hι _).trans hx.symm)
  have hne : (⟨φ, hφ⟩ : π.V) ≠ 0 := fun e => h0 (by rw [← hxι, e, map_zero])
  have hsat : IsSatVecGL w (π.locRep w) ⟨φ, hφ⟩ B := hB.2 _ hw hne
  have hint : ∀ g y, ι (π.locRep w g y) = repW a w g (ι y) := fun g y => by
    refine DFunLike.coe_injective ?_
    funext h
    rw [hι]
    change _ = (ι y) (h * fl a w g)
    have := congrFun (hι y) (h * fl a w g)
    rw [this]
    rfl
  have := hsat.map ι hint (by rw [hxι]; exact h0)
  rwa [hxι] at this

end GlobalTheory.CompanionTheory.StrongMultOne

end
end

namespace PositivityTheory.jumpWindows

theorem almost_everywhere_spherical_of_G1 : G1 → AlmostEverywhereSpherical :=
  GlobalTheory.CompanionTheory.StrongMultOne.spherical_almost_everywhere_of_bounded

end PositivityTheory.jumpWindows
end

module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfThetaTranslateEqUnitMul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundlePowSectionsEqThetaLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundlePowSectionsEqThetaLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.LevelDict

section Charts

variable {X : Scheme.{0}} (L : LB X) (n : ℕ)

theorem sec_ext {M : LB X} {s t : M.Sec} (h : ∀ i, s.f i = t.f i) : s = t := by
  obtain ⟨f, hf⟩ := s
  obtain ⟨f', hf'⟩ := t
  obtain rfl : f = f' := funext h
  rfl

theorem powChart_le (j : (lbPow L n).ι) : (lbPow L n).U j ≤ L.U (j PUnit.unit) :=
  fun _ hy => Set.mem_iInter.1 hy PUnit.unit

theorem le_powChart (j : (lbPow L n).ι) : L.U (j PUnit.unit) ≤ (lbPow L n).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem lbPow_g (j j' : (lbPow L n).ι) : ((lbPow L n).g j j').val =
    rs X (inf_le_inf (powChart_le L n j) (powChart_le L n j'))
      (L.g (j PUnit.unit) (j' PUnit.unit) ^ (n : ℤ)).val := by
  have h : (lbPow L n).g j j' = res (inf_le_inf (powChart_le L n j) (powChart_le L n j'))
      (L.g (j PUnit.unit) (j' PUnit.unit) ^ (n : ℤ)) := by
    rw [map_zpow]
    unfold lbPow LB.LinComb
    dsimp only
    rw [Fintype.prod_unique]
    rfl
  rw [h]
  rfl

def powSecEquiv : (lbPow L n).Sec ≃ (pw L (n : ℤ)).Sec where
  toFun s := ⟨fun i => rs X (le_powChart L n fun _ => i) (s.f fun _ => i), fun i k => by
    have h := congrArg (rs X (inf_le_inf (le_powChart L n fun _ => i) (le_powChart L n fun _ => k)))
      (s.compat (fun _ => i) (fun _ => k))
    refine (rs_rs _ _ _).trans ((rs_rs _ _ _).symm.trans (h.trans ((map_mul _ _ _).trans ?_)))
    exact congrArg₂ (· * ·) ((congrArg _ (lbPow_g L n _ _)).trans ((rs_rs _ _ _).trans (rs_self _ _)))
      ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)⟩
  invFun s := ⟨fun j => rs X (powChart_le L n j) (s.f (j PUnit.unit)), fun j k => by
    have h := congrArg (rs X (inf_le_inf (powChart_le L n j) (powChart_le L n k)))
      (s.compat (j PUnit.unit) (k PUnit.unit))
    rw [lbPow_g]
    refine (rs_rs _ _ _).trans ((rs_rs _ _ _).symm.trans (h.trans ((map_mul _ _ _).trans ?_)))
    exact congrArg _ ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)⟩
  left_inv s := sec_ext fun _ => (rs_rs _ _ _).trans (rs_self _ _)
  right_inv s := sec_ext fun _ => (rs_rs _ _ _).trans (rs_self _ _)

theorem valAt'_powSecEquiv (s : (lbPow L n).Sec) (x : Sp ℂ ⟶ X) (j : (lbPow L n).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit)) :
    valAt' x (L.U (j PUnit.unit)) ((powSecEquiv L n s).f (j PUnit.unit)) = valAt' x ((lbPow L n).U j) (s.f j) :=
  valAt'_map x (homOfLE (le_powChart L n j)).op (s.f j) h

end Charts

theorem transfer {S S' T T' : Type*} (E : S ≃ S') (G : T ≃ T') {P : T → Prop} {P' : T' → Prop} {Q : S → T → Prop}
    {Q' : S' → T' → Prop} (hP : ∀ t, P' (G t) ↔ P t) (hQ : ∀ s t, Q' (E s) (G t) ↔ Q s t)
    (h : (∀ s, ∃! t, P t ∧ Q s t) ∧ ∀ t, P t → ∃! s, Q s t) :
    (∀ s, ∃! t, P' t ∧ Q' s t) ∧ ∀ t, P' t → ∃! s, Q' s t := by
  refine ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨s, rfl⟩ := E.surjective s
    rw [← G.existsUnique_congr (p := fun t => P t ∧ Q s t) fun t => by rw [hP, hQ]]
    exact h.1 s
  · obtain ⟨t, rfl⟩ := G.surjective t
    rw [← E.existsUnique_congr (p := fun s => Q s t) fun s => by rw [hQ]]
    exact h.2 t ((hP t).1 ht)

theorem ext_of_ne_zero {g : ℕ} {θ f f' : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (hf : Continuous f)
    (hf' : Continuous f') (h : ∀ z, θ z ≠ 0 → f z = f' z) : ∀ z, f z = f' z :=
  congrFun (Continuous.ext_on (ThetaTangent.dense_ne_zero hθ h0) hf hf' h)

section Frames

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}


open PullHermitian in
theorem exists_frame_ratio (hL : L.IsLB) (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u₀.fr i (F z) = r z * u.fr i z := by
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (fun i => (u.hol _ 0).1)
    (fun z => PullHermitian.exists_chart (u.ex z).left hL)
    (fun i z => u₀.fr i (F z) / u.fr i z)
    (fun i => by
      have d2 := (u₀.fr_hol i).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have h1 := u.fr_compat i j z (inf_of _ hi hj)
      have h2 := u₀.fr_compat i j (F z) (tr (inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), h1, h2]
      ring)
  refine ⟨r, hr, fun z => ?_, fun i z hi => ?_⟩
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
    rw [hrφ i z hi]
    exact div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi)
  · rw [hrφ i z hi, div_mul_cancel₀ _ (u.fr_ne _ _ hi)]

end Frames

theorem isLevel_thetaChar {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (hab : charHalf g a b) :
    IsLevel τ a b 1 (thetaChar τ a b) ∧ thetaChar τ a b ≠ 0 := by
  obtain ⟨h0, h1, -⟩ := TorusAlg.thetaChar_level hs hp hab.1 hab.2
  have hm : thetaChar τ a b ∈ thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ := by
    rw [h1]
    exact Submodule.mem_span_singleton_self _
  rw [mem_thetaLevelChar, TorusAlg.ofRealVec_re hab.1, TorusAlg.ofRealVec_re hab.2] at hm
  refine ⟨⟨hm.1, fun m n z => ?_⟩, h0⟩
  have h := hm.2 n m z
  rw [add_assoc, add_comm (τ.mulVec _), ReciprocityTheory.PTheta.eC, ReciprocityTheory.PTheta.eC, ← Complex.exp_add] at h
  refine h.trans ?_
  rw [pow_one]
  congr 2
  unfold ReciprocityTheory.PTheta.ofIntVec
  push_cast
  ring

theorem sections_eq_level : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → Wit x h u τ a b → (∀ s : RR x l, ∃! F, IsLevel τ a b l F ∧ FnPw x u s F) ∧ ∀ F, IsLevel τ a b l F → ∃! s : RR x l, FnPw x u s F := by
  intro hT g x h u τ a b l hab ⟨hs, hp, hΛ, _, hth, _⟩
  subst h
  obtain ⟨u₀, H₀, χ₀, -, hu₀, -, hv, hw, -, hsec, -⟩ := hT x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have he : ∀ z, e z = F z := fun z => rfl
  have hed : Differentiable ℂ e := (LinearMap.toContinuousLinearMap F).differentiable
  have hed' : Differentiable ℂ e.symm := (LinearMap.toContinuousLinearMap e.symm.toLinearMap).differentiable
  obtain ⟨r, hr, hr0, hrf⟩ := exists_frame_ratio x.P.isLB u u₀ F hF
  obtain ⟨hθ, hθ0⟩ := isLevel_thetaChar hs hp hab
  let G : ((Fin x.P.g → ℂ) → ℂ) ≃ ((Fin x.P.g → ℂ) → ℂ) :=
    { toFun := fun f z => f (e z) * r z ^ l
      invFun := fun f w => f (e.symm w) * (r (e.symm w) ^ l)⁻¹
      left_inv := fun f => funext fun w => by
        simp only [e.apply_symm_apply]
        exact mul_inv_cancel_right₀ (pow_ne_zero _ (hr0 _)) _
      right_inv := fun f => funext fun z => by
        simp only [e.symm_apply_apply]
        exact inv_mul_cancel_right₀ (pow_ne_zero _ (hr0 _)) _ }
  have hG : ∀ f z, G f z = f (e z) * r z ^ l := fun _ _ => rfl

  have key : ∀ (m n : Fin x.P.g → ℤ) (k : u₀.Λ), (k : Fin x.P.g → ℂ) =
      e ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) → ∀ z,
      χ₀ k * Complex.exp (Real.pi * hermForm H₀ (e z) k + Real.pi / 2 * hermForm H₀ k k) *
        r (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (m i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
        ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) * r z := by
    intro m n k hk
    have hec := hed.continuous
    have hrc := hr.continuous
    refine ext_of_ne_zero hθ.1 hθ0 ?_ ?_ fun z hz => ?_
    · unfold hermForm
      fun_prop
    · fun_prop
    · have h1 := hθ.2 m n z
      rw [pow_one] at h1
      set w := (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) with hw
      have hper : u.ex (z + w) = u.ex z := by
        rw [u.ex_add, (u.ker w).2 ((hΛ w).2 ⟨m, n, hw⟩), _root_.mul_one]
      obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left x.P.isLB
      have hi' : ⊤ ≤ (u.ex (z + w)).left ⁻¹ᵁ x.P.L.U i := by rwa [hper]
      have h2 := hth i z hi
      have h3 := hth i _ hi'
      rw [hper, h2, h1] at h3
      have h4 := hu₀.2.2.2 k i (e z) (by rw [he, hF]; exact hi)
      rw [hk, ← map_add (f := _), he, he (z + w), hrf i z hi, hrf i _ hi', ← he, ← hk] at h4
      refine mul_right_cancel₀ (mul_ne_zero hz (u.fr_ne i _ hi')) ?_
      unfold hermForm
      linear_combination r z * h3 - thetaChar τ a b z * h4
  refine transfer (powSecEquiv x.P.L l) G (fun f => ?_) (fun s f => ?_) (hsec l)
  on_goal 1 => refine ⟨fun hf => ⟨?_, fun k w => ?_⟩, fun hf => ⟨?_, fun m n z => ?_⟩⟩
  on_goal 5 => refine ⟨fun hf j w hj => ?_, fun hf i z hi => ?_⟩
  · rw [← G.symm_apply_apply f]
    exact (hf.1.comp hed').mul (((hr.comp hed').pow l).inv fun w => pow_ne_zero _ (hr0 _))
  · obtain ⟨z, rfl⟩ := e.surjective w
    obtain ⟨m, n, hmn⟩ := (hΛ (e.symm k)).1 ((UnifCompare.mem_iff u u₀ F hF _).1 (by
      rw [← he, e.apply_symm_apply]; exact k.2))
    have hk := e.symm_apply_eq.1 hmn
    have h1 := hf.2 m n z
    rw [hG, hG, map_add (f := _), ← hk, mul_comm (f (e z)), ← _root_.mul_assoc, ← mul_pow, ← key m n k hk z, mul_pow] at h1
    refine mul_right_cancel₀ (pow_ne_zero l (hr0 _)) (h1.trans ?_)
    ring
  · exact (hf.1.comp hed).mul (hr.pow l)
  · have hk := (UnifCompare.mem_iff u u₀ F hF _).2 ((hΛ _).2 ⟨m, n, rfl⟩)
    have h1 := hf.2 ⟨e _, hk⟩ (e z)
    rw [hG, hG, map_add (f := _), mul_comm (f (e z)), ← _root_.mul_assoc, ← mul_pow, ← key m n ⟨e _, hk⟩ rfl z, mul_pow, h1]
    ring
  · obtain ⟨z, rfl⟩ := e.surjective w
    rw [he] at hj ⊢
    rw [hF] at hj ⊢
    have hi := top_le_preimage_mono _ (powChart_le _ _ j) hj
    rw [← valAt'_powSecEquiv _ _ s _ j hi, hrf _ z hi, mul_pow, ← _root_.mul_assoc]
    exact hf _ z hi
  · have h1 := hf (fun _ => i) (F z) (by rw [hF]; exact top_le_preimage_mono _ (le_powChart _ _ fun _ => i) hi)
    rw [hF, hrf i z hi, mul_pow, ← _root_.mul_assoc] at h1
    exact (valAt'_powSecEquiv _ _ s _ (fun _ => i) hi).trans h1

end GlobalTheory.LevelDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundlePowSectionsEqThetaLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundlePow_sections_eq_theta_level : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → Wit x h u τ a b → (∀ s : RR x l, ∃! F, IsLevel τ a b l F ∧ FnPw x u s F) ∧ ∀ F, IsLevel τ a b l F → ∃! s : RR x l, FnPw x u s F := by
  first | exact @GlobalTheory.LevelDict.sections_eq_level | exact GlobalTheory.LevelDict.sections_eq_level | (intros; apply GlobalTheory.LevelDict.sections_eq_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacEqUnitMulDetPderiv
noncomputable section

namespace GlobalTheory.JacSer

section Algebra

open IsLocalRing MvPowerSeries GlobalTheory.SqZero

variable {O : Type} [CommRing O] [IsLocalRing O]

theorem isLocalRing_trivSqZeroExt (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] :
    IsLocalRing (TrivSqZeroExt O M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _


omit [IsLocalRing O] in
def dirPt {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) :
    MvPowerSeries (Fin n) O →ₐ[O] DualNumber O :=
  addDer ((inlS O O).comp e) (TrivSqZeroExt.inrHom O O ∘ₗ
      ∑ j, c j • (e.toLinearMap ∘ₗ (pderiv (R := O) j).toLinearMap))
    (fun a b => by
      ext
      · simp [TrivSqZeroExt.fst_sum]
      · simp [TrivSqZeroExt.snd_sum, Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
        exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)

omit [IsLocalRing O] in
theorem dirPt_fst {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (a : MvPowerSeries (Fin n) O) :
    (dirPt e c a).fst = e a := add_zero (e a)

omit [IsLocalRing O] in
theorem dirPt_snd {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (a : MvPowerSeries (Fin n) O) :
    (dirPt e c a).snd = ∑ j, c j * e (pderiv (R := O) j a) :=
  (zero_add _).trans ((TrivSqZeroExt.snd_inr _ _).trans (by simp))

omit [IsLocalRing O] in
theorem dirPt_snd_X {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (c : Fin n → O) (i : Fin n) :
    (dirPt e c (X i)).snd = c i := by
  simp [dirPt_snd, pderiv_X, Pi.single_apply, apply_ite e]

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

theorem snd_eq_sum {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O)
    (ψ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) (hψ : ∀ a, (ψ a).fst = e a) (a : MvPowerSeries (Fin n) O) :
    (ψ a).snd = ∑ j, (ψ (X j)).snd * e (pderiv (R := O) j a) := by
  have := isLocalRing_trivSqZeroExt (O := O) O
  have : Module.Finite O (DualNumber O) := inferInstanceAs (Module.Finite O (O × O))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (DualNumber O)
  have h : ψ = dirPt e fun j => (ψ (X j)).snd :=
    mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal (DualNumber O))
      (fun i h => he i (hψ _ ▸ TrivSqZeroExt.isUnit_iff_isUnit_fst.1 h))
      (fun i => TrivSqZeroExt.ext (by rw [hψ, dirPt_fst]) (by rw [dirPt_snd_X]))
  exact (congrArg (fun q => (q a).snd) h).trans (dirPt_snd _ _ _)

omit [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] in
theorem isLocalHom_of_X_mem {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O) :
    IsLocalHom e.toRingHom := by
  refine ((IsLocalRing.local_hom_tfae _).out 1 4).2 fun g hg => ?_
  have h1 := algHom_sub_constantCoeff_mem e he g
  have h2 := (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff (g := g)).1 hg
  simpa using add_mem h1 h2

end Algebra

section Group

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing MvPowerSeries

attribute [local instance] Over.cartesianMonoidalCategory

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR O ⟶ G)}

theorem exists_matrix (hv : IsLieBasis v) (j : sp (R₀ := O) (MvPowerSeries (Fin n) O) ⟶ G)
    (inj : ∀ {T : Type} [CommRing T] [Algebra O T] (φ ψ : MvPowerSeries (Fin n) O →ₐ[O] T),
      spMap φ ≫ j = spMap ψ ≫ j → ∀ i, φ (X i) = ψ (X i))
    (z : 𝟙_ _ ⟶ G) (u : MvPowerSeries (Fin n) O →ₐ[O] O) (hu0 : ∀ i, u (X i) ∈ maximalIdeal O)
    (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : MvPowerSeries (Fin n) O →ₐ[O] TrivSqZeroExt O (Fin n → O))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ C : Matrix (Fin n) (Fin n) O, IsUnit C.det ∧
      ∀ k, ∃ φ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧
        ∀ a, (φ a).snd = ∑ i, u (pderiv (R := O) i a) * C i k := by
  have hz : ∀ {T T' : Type} [CommRing T] [Algebra O T] [CommRing T'] [Algebra O T'] (φ : T →ₐ[O] T'),
      spMap φ ≫ toUnit _ ≫ z = toUnit _ ≫ z := fun φ => by
    rw [← Category.assoc, comp_toUnit]
  have hfst : ∀ a, (χ a).fst = u a := by
    refine fun a => (AlgHom.congr_fun (mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal O) hu0
      (inj u ((TrivSqZeroExt.fstHom O O _).comp χ) ?_)) a).symm
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp,
      lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, hu]
  let φ : (Fin n → O) → (MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) := fun c =>
    (vecTo (inlS O O) (fun i => inr (c i)) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = (toUnit _ ≫ z) * tanExp v c := fun c => by
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp]
    exact congrArg _ (lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _)
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, (χ a).snd k * c k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  obtain ⟨-, hsurj⟩ := isLieBasisOver_self hv
  have hM : ∀ l : Fin n, ∃ c : Fin n → O, ∀ i, ∑ k, (χ (X i)).snd k * c k = (Pi.single l 1 : Fin n → O) i := by
    intro l
    have h1 : (fstS O O).comp (dirPt u (Pi.single l 1)) = u := AlgHom.ext fun a => dirPt_fst _ _ a
    obtain ⟨c, hc⟩ := hsurj ((toUnit _ ≫ z)⁻¹ * (spMap (dirPt u (Pi.single l 1)) ≫ j)) (by
      rw [IsTanOver, MonObj.comp_mul, GrpObj.comp_inv, hz, ← Category.assoc, spMap_comp, h1, hu,
        inv_mul_cancel])
    have h2 := inj (dirPt u (Pi.single l 1)) (φ c) (by rw [hφ, ← hc, mul_inv_cancel_left])
    exact ⟨c, fun i => by rw [← hφ2, ← h2, dirPt_snd_X]⟩
  choose M hM using hM
  refine ⟨Matrix.of fun i k => (χ (X i)).snd k, ?_, fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k l => M l k) (Matrix.ext fun i l => ?_)
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact (hM l i).trans (Pi.single_apply _ _ _)
  · rw [hφ, tanExp_single hv.1]
  · rw [snd_eq_sum u hu0 _ (hφ1 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφ2, mul_comm]
    simp [Pi.single_apply]

end Group

end GlobalTheory.JacSer

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (θ : Sp (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A.left) (z : Pt x) (e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] O), θ ≫ x.P.A.hom = spMap (algebraMap O (MvPowerSeries (Fin x.P.g) O)) → (∃ (V : x.P.A.left.Opens) (t : Fin x.P.g → Γ(x.P.A.left, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin x.P.g) O)) θ V (t i) = MvPowerSeries.X i) → (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ x.P.A.left), w ≫ x.P.A.hom = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) → ∃ e : (MvPowerSeries (Fin x.P.g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) → (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → spMap e.toRingHom ≫ θ = z.left → ∃ u : Oˣ, ∀ (n : ℕ) (s : Fin x.P.g → RR x n) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → jac x s z c = u * e (Matrix.of fun i j => MvPowerSeries.pderiv (R := O) j (valT (T := (MvPowerSeries (Fin x.P.g) O)) θ (x.P.L.U c) ((s i).f c))).det := by
  intro O _ _ _ _ x θ z e hθ ⟨V, t, hV, ht⟩ hlift he hz
  let j : Chart.sp (R₀ := O) (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A := Over.homMk θ hθ
  have hloc := GlobalTheory.JacSer.isLocalHom_of_X_mem e he
  have hcl : z.left (IsLocalRing.closedPoint O) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) := by
    rw [← hz, ← IsLocalRing.comap_closedPoint e.toRingHom]
    rfl
  have hu : Chart.spMap e ≫ j = toUnit _ ≫ z := by
    apply Over.OverMorphism.ext
    have e1 : (toUnit (Chart.sp (R₀ := O) O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    rw [Over.comp_left, Over.comp_left, e1]
    exact hz.trans (Category.id_comp _).symm
  have := GlobalTheory.JacSer.isLocalRing_trivSqZeroExt (O := O) (Fin x.P.g → O)
  have : Module.Finite O (TrivSqZeroExt O (Fin x.P.g → O)) :=
    inferInstanceAs (Module.Finite O (O × (Fin x.P.g → O)))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (TrivSqZeroExt O (Fin x.P.g → O))
  let w : Chart.sp (R₀ := O) (TrivSqZeroExt O (Fin x.P.g → O)) ⟶ x.P.A :=
    (toUnit _ ≫ z) * GlobalTheory.SqZero.lieExp x.v (fun i => TrivSqZeroExt.inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  obtain ⟨χ, -, hχ⟩ := hlift (TrivSqZeroExt O (Fin x.P.g → O)) w.left (Over.w w) (by
    have h1 : IsLocalHom (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    have h2 : Chart.spMap (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)) ≫ w = Chart.spMap e ≫ j := by
      rw [hu, MonObj.comp_mul, GlobalTheory.SqZero.comp_lieExp, GlobalTheory.SqZero.lieExp_eq_one x.basis.1 _ (fun i => by rfl),
        _root_.mul_one, ← Category.assoc, comp_toUnit]
    have h3 := congrArg (fun q => q.left (IsLocalRing.closedPoint O)) h2
    rw [← IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom O O (Fin x.P.g → O)).toRingHom,
      ← IsLocalRing.comap_closedPoint e.toRingHom]
    exact h3)
  obtain ⟨C, hC, hφ⟩ := GlobalTheory.JacSer.exists_matrix x.basis j (fun φ ψ h i => by
    have h1 : spMap φ.toRingHom ≫ θ = spMap ψ.toRingHom ≫ θ := congrArg (·.left) h
    have h2 := EtBaseChange.valT_spMap φ.toRingHom θ hV (t i)
    rw [h1, EtBaseChange.valT_spMap ψ.toRingHom θ hV, ht] at h2
    exact h2.symm) z e he hu χ (Over.OverMorphism.ext hχ)
  refine ⟨hC.unit, fun n s c hc => ?_⟩
  have hθc : ⊤ ≤ θ ⁻¹ᵁ x.P.L.U c := fun p _ =>
    ((IsLocalRing.specializes_closedPoint p).map θ.continuous).mem_open (x.P.L.U c).isOpen
      (hcl ▸ hc (x := IsLocalRing.closedPoint O) trivial)
  rw [IsUnit.unit_spec, _root_.mul_comm, AlgHom.map_det, ← Matrix.det_mul]
  refine congrArg Matrix.det (Matrix.ext fun i k => ?_)
  obtain ⟨φ, h1, h2⟩ := hφ k
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine Eq.trans (congrArg TrivSqZeroExt.snd ?_) (h2 _)
  exact (congrArg (fun q : epsR O ⟶ x.P.A => valT (T := DualNumber O) q.left (x.P.L.U c) ((s i).f c)) h1.symm).trans
    (EtBaseChange.valT_spMap φ.toRingHom θ hθc _)

end
end
end

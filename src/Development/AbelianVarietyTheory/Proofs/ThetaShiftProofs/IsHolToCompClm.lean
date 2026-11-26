module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyProjCoordsConvergentCoefficients
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentConstantCoordsGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelPointTangentVectorTransportIffStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CharEqOfThetaCharEqMul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRigidifiedTwist
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcSectionValueAtSpecialisedPointsTheta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelOneSectionEqKappaTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TwoRigidifiedThetaFramesOnFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TwoRigidifiedThetaFramesOnFibre
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.TwoFrames

theorem valR_eq_valAt' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valR x U f = valAt' x U f := by
  unfold valR valAt' valAt
  congr

theorem map_map {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (f : Γ(X, U)) :
    (X.presheaf.map (homOfLE k).op).hom ((X.presheaf.map (homOfLE h).op).hom f) =
      (X.presheaf.map (homOfLE (k.trans h)).op).hom f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_sec_of_pow_one {Z Z' : Scheme.{0}} {L : LB Z} {p : Z' ⟶ Z} (σ : SecP L p 1) :
    ∃ s : (L.pull p).Sec, ∀ (j : L.ι) (x : Sp ℂ ⟶ Z'), ⊤ ≤ (x ≫ p) ⁻¹ᵁ L.U j →
      valAt' x ((L.pull p).U (fun _ => j)) (s.f (fun _ => j)) = ArcPts.sval σ x j := by
  have le : ∀ J : PUnit → L.ι, (L.pull p).U J ≤ LB.wchart L (fun _ : Fin 1 => p) (fun _ => J PUnit.unit) :=
    fun J y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy PUnit.unit
  refine ⟨⟨fun J => (Z'.presheaf.map (homOfLE (le J)).op).hom (σ.f (fun _ => J PUnit.unit)), fun J J' => ?_⟩,
    fun j x hx => ?_⟩
  · have h := congrArg (Z'.presheaf.map (homOfLE (inf_le_inf (le J) (le J'))).op).hom
      (σ.compat (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit))
    refine ((map_map _ _ _).trans (map_map _ _ _).symm).trans (h.trans ((map_mul _ _ _).trans ?_))
    refine congrArg₂ (· * ·) ?_ ((map_map _ _ _).trans (map_map _ _ _).symm)
    simp only [LB.LinComb, Finset.univ_unique, Finset.prod_singleton, Nat.cast_one, zpow_one]
    refine (map_map _ _ _).trans ?_
    symm
    refine Eq.trans (congrArg Units.val (?_ : (L.pull p).g J J' = res (le_inf (inf_le_left.trans
      (LB.wchart_le L _ J PUnit.unit)) (inf_le_right.trans (LB.wchart_le L _ J' PUnit.unit)))
      (pullU p _ (L.g (J PUnit.unit) (J' PUnit.unit))))) rfl
    show ∏ k : PUnit, _ = _
    have hp : ∀ {G : Type} [CommGroup G] (x : G), ∏ _k : PUnit.{1}, x ^ (1 : ℤ) = x := fun x => by simp
    exact hp _
  · refine Eq.trans ?_ (valR_eq_valAt' x _ _).symm
    exact GlobalTheory.valAt'_map x _ _ (fun q hq => mem_pull.2 ((top_le_preimage_comp _ _ _).1 hx hq))

theorem two_frames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) lin cst (w : ℂ) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr (g : ℕ) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) (ϑ : (Fin g → ℂ) → ℂ) fr', IsFibAt A Xo.univ.t lin cst w y₀ π fr → (∀ v, e (h v) = (π v).left) → IsThetaFrameAt Xo.univ.t.PP y₀ e ϑ fr' → (∃ z, ϑ z ≠ 0) → ∀ th ∈ A.Theta 1 0, (∃ v, A.Sum 1 0 th w v ≠ 0) → ∃ (lam : ℂ) (f : A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧ (∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = f v * fr j v) ∧ ∀ v, A.Sum 1 0 th w v = lam * ϑ (h v) * f v := by
  intro hL _ E _ _ _ H _ D l Xo A lin cst w y₀ π fr g h e ϑ fr' hF he hT hϑ th hth hS
  obtain ⟨d', n', c', r', s', hs'⟩ := hT
  have ch : ∀ v, ∃ j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun v => by
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB ((π v).left (default : PrimeSpectrum ℂ))
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  choose J hJ using ch
  have n : ∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j v ≠ 0 := fun v j hj => ((hF.frm v).1 j hj).ne_zero
  have key : ∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = fr' (J v) (h v) / fr (J v) v * fr j v := by
    intro v j hj
    have hi := (top_le_preimage_inf _ _ _).2 ⟨hj, hJ v⟩
    have a := (hF.frm v).2 j (J v) hi
    have b := c' j (J v) (h v) (by rw [he]; exact hi)
    rw [he] at b
    rw [valR_eq_valAt'] at a
    beta_reduce at a
    have := n v _ (hJ v)
    rw [b, a]
    field_simp
  obtain ⟨σ, hσ⟩ := hF.sec th hth
  obtain ⟨s, hs⟩ := exists_sec_of_pow_one σ
  obtain ⟨u, hu⟩ := ThetaFamily.exists_values_line_fibre hL.globalSectionsRank Xo.univ y₀
  obtain ⟨a, ha⟩ := hu s
  obtain ⟨a', ha'⟩ := hu s'
  have f1 : ∀ v, fib (π v) ≫ pullback.fst _ _ = (π v).left := fun v => pullback.lift_fst _ _ _
  have f2 : ∀ v, fib (π v) ≫ pullback.snd _ _ = 𝟙 _ := fun v => pullback.lift_snd _ _ _
  have m : ∀ v, ⊤ ≤ (fib (π v) ≫ pullback.fst _ _) ⁻¹ᵁ Xo.univ.t.PP.L.U (J v) := fun v => by
    rw [f1]; exact hJ v
  have m' : ∀ v, ⊤ ≤ fib (π v) ⁻¹ᵁ (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y₀)).U (fun _ => J v) :=
    fun v q hq => mem_pull.2 ((top_le_preimage_comp _ _ _).1 (m v) hq)
  have e1 : ∀ v, A.Sum 1 0 th w v * fr (J v) v = a * u (fun _ => J v) (fib (π v)) := fun v => by
    rw [← ha _ _ (f2 v) (m' v), hs _ _ (m v), hσ v _ (m v), pow_one]
  have e2 : ∀ v, ϑ (h v) * fr' (J v) (h v) = a' * u (fun _ => J v) (fib (π v)) := fun v => by
    rw [← ha' _ _ (f2 v) (m' v),
      hs' _ (h v) _ ((f1 v).trans (he v).symm) (f2 v) (by rw [he]; exact hJ v)]
  have n'' : ∀ v, fr' (J v) (h v) ≠ 0 := fun v => n' _ _ (by rw [he]; exact hJ v)
  have a0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hS
    exact mul_ne_zero hv (n v _ (hJ v)) ((e1 v).trans (zero_mul _))
  have a0' : a' ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hϑ
    obtain ⟨v, rfl⟩ := h.surjective z
    exact mul_ne_zero hz (n'' v) ((e2 v).trans (zero_mul _))
  refine ⟨a / a', fun v => fr' (J v) (h v) / fr (J v) v, div_ne_zero a0 a0', fun v₀ => ?_,
    fun v => div_ne_zero (n'' v) (n v _ (hJ v)), ?_, key, fun v => ?_⟩
  · have op : IsOpen {v | ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U (J v₀)} := by
      simpa using (hF.hol (Xo.univ.t.PP.L.U (J v₀)) 0).1
    have nh := op.mem_nhds (hJ v₀)
    have d1 : DifferentiableOn ℂ (fun v => fr' (J v₀) (h v))
        {v | ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U (J v₀)} :=
      (d' (J v₀)).comp h.differentiable.differentiableOn fun v hv => by
        show ⊤ ≤ e (h v) ⁻¹ᵁ _
        rw [he]; exact hv
    have d2 := ((d1.mul ((hF.fr_hol (J v₀)).inv fun v hv => n v _ hv)).differentiableAt nh)
    refine d2.congr_of_eventuallyEq (Filter.mem_of_superset nh fun v hv => ?_)
    show fr' (J v) (h v) / fr (J v) v = fr' (J v₀) (h v) * (fr (J v₀) v)⁻¹
    rw [key v _ hv, mul_inv_cancel_right₀ (n v _ hv)]
  · show fr' (J 0) (h 0) / fr (J 0) 0 = 1
    have h0 : e 0 = (π 0).left := by rw [← he, map_zero]
    rw [div_eq_one_iff_eq (n 0 _ (hJ 0)), map_zero, r' _ (by rw [h0]; exact hJ 0), hF.rig _ (hJ 0)]
  · have := n v _ (hJ v)
    have b1 := e1 v
    have b2 := e2 v
    field_simp
    linear_combination a' * b1 - a * b2

end GlobalTheory.TwoFrames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TwoRigidifiedThetaFramesOnFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_rigidified_theta_frames_on_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) lin cst (w : ℂ) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr (g : ℕ) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) (ϑ : (Fin g → ℂ) → ℂ) fr', IsFibAt A Xo.univ.t lin cst w y₀ π fr → (∀ v, e (h v) = (π v).left) → IsThetaFrameAt Xo.univ.t.PP y₀ e ϑ fr' → (∃ z, ϑ z ≠ 0) → ∀ th ∈ A.Theta 1 0, (∃ v, A.Sum 1 0 th w v ≠ 0) → ∃ (lam : ℂ) (f : A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧ (∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = f v * fr j v) ∧ ∀ v, A.Sum 1 0 th w v = lam * ϑ (h v) * f v := by
  first | exact @GlobalTheory.TwoFrames.two_frames | exact GlobalTheory.TwoFrames.two_frames | (intros; apply GlobalTheory.TwoFrames.two_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelOneSectionEqKappaTheta
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem eq_at_zero_of_eq_off_zeros {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F p q : V → ℂ}
    (hF : Continuous F) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q) {v₀ : V} (h₀ : F v₀ ≠ 0)
    (h : ∀ v, F v ≠ 0 → p v = q v) : p 0 = q 0 := by
  have hl : Differentiable ℂ fun t : ℂ => t • v₀ := differentiable_id.smul_const _
  have h1 : AnalyticOnNhd ℂ (fun t : ℂ => p (t • v₀)) Set.univ := fun t _ => (hp.comp hl).analyticAt t
  have h2 : AnalyticOnNhd ℂ (fun t : ℂ => q (t • v₀)) Set.univ := fun t _ => (hq.comp hl).analyticAt t
  have h3 : ∀ᶠ t in nhds (1 : ℂ), F (t • v₀) ≠ 0 :=
    (hF.comp hl.continuous).continuousAt.eventually_ne (by simpa using h₀)
  have h4 := AnalyticOnNhd.eq_of_eventuallyEq h1 h2 (h3.mono fun t ht => h _ ht)
  simpa using congrFun h4 0

theorem isFnInRigFrame_of_isFn {D₀ : Out.DegPre ℂ} {n g : ℕ} (u : HolUnif D₀.P.A D₀.P.L n) (hr : u.IsRig D₀.rig)
    {th : D₀.P.L.Sec} {θ : (Fin n → ℂ) → ℂ} (hθ : u.IsFn th θ) {p : (Fin g → ℂ) → (Fin n → ℂ)}
    (hp : Differentiable ℂ p) (hp0 : p 0 = 0) {Q ϑ : (Fin g → ℂ) → ℂ} (hQ : Differentiable ℂ Q) (hQ0 : Q 0 = 0)
    (h : ∀ z, θ (p z) = Complex.exp (Q z) * ϑ z) :
    IsFnInRigFrame D₀ (fun z => (u.ex (p z)).left) th ϑ := by
  refine ⟨fun j z => Complex.exp (Q z) * u.fr j (p z), fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_,
    fun j hj => ?_, fun j z hz => ?_⟩
  · exact hQ.cexp.differentiableOn.mul ((u.fr_hol j).comp hp.differentiableOn fun z hz => hz)
  · exact mul_ne_zero (Complex.exp_ne_zero _) (u.fr_ne j _ hz)
  · beta_reduce
    rw [u.fr_compat j j' _ hz]
    ring
  · have e1 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
    have e2 : (u.ex 0).left = eSec D₀.P.A := by
      rw [e1, Hom.one_def, toUnit_unit, Category.id_comp]
      rfl
    beta_reduce at hj ⊢
    rw [hp0, e2] at hj
    rw [hQ0, hp0, Complex.exp_zero, _root_.one_mul]
    exact hr (fun _ => j) fun x hx => Set.mem_iInter.2 fun _ => hj hx
  · beta_reduce
    rw [hθ j _ hz, h]
    ring


set_option maxHeartbeats 800000 in
theorem arc_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → ∃ T₂ : ℝ, ∀ T ≥ T₂, ∀ (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fu.Di K.i).La) (S : Finset (Fin g)) (h : Matrix (Fin g) (Fin g) ℂ) (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)), ThetaHyp W th σ fam → (∀ u v, (Fu.Di K.i).EF (bas u) (bas v) = -omegaStd u v) → (∀ u, Λ.ε (K.gam (bas u)).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0) → (∀ w k, h.mulVec (K.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ h.mulVec (K.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → (∃ w fr, T < w.im ∧ IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr) → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ k ∈ S, c₁ k = 0) ∧ (∀ w : ℂ, T < w.im → IsFnInRigFrame a.D₀ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) th (fun z => κ * thetaCharOff S (τ w) c₁ c₂ (h.mulVec z))) ∧ ∀ (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), ⊤ ≤ χ ⁻¹ᵁ U → s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U) → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (κ * rw * thetaChar (τ w) c₁ c₂ (h.mulVec z) * fr j₀ z) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin lin cst T₁ hfib
  obtain ⟨T₀, hT⟩ := Λ.A.exists_isConvLine
  refine ⟨max T₀ (max T₁ K.T), fun T hTT th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ hth hEF hS hP hc₁ hc₂ r₂ r₁ r₀ hex => ?_⟩
  have hT0 : T₀ ≤ T := (le_max_left _ _).trans hTT
  have hT1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hTT
  have hTK : K.T ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hTT
  obtain ⟨θ, hθ, hθ0, hfn⟩ := (ArcThetaSpaces.sections_theta hL hL2 E H D l c O β _ a Λ).2.2 th hth.1
  let bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ.A.La := bas.trans (K.gam.toAddEquiv.toIntLinearEquiv)
  have hb : ∀ u, bas' u = K.gam (bas u) := fun _ => rfl
  obtain ⟨hu, hτ, d₁, d₂, -, -, hdS, ⟨Q, κ, -, hQ, hQ0, hκ, hSum, hoff⟩, huniq⟩ :=
    Λ.A.theta_comparison hT K.h.toLinearEquiv hθ hθ0 bas' (fun u v => by rw [hb, hb, K.EF_eq, hEF]) S
      (fun u => by rw [← hS, hb, map_eq_zero_iff _ Λ.ε.injective]) h τ
      (fun w k => by simpa only [hb, K.Pw_eq, ContinuousLinearEquiv.coe_toLinearEquiv] using hP w k)
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv] at hSum hoff huniq
  have hSne : ∀ w : ℂ, T₀ < w.im → ∃ v, Λ.A.Sum 1 0 θ w v ≠ 0 := fun w hw => by
    obtain ⟨v, hv⟩ := Λ.A.exists_Sum_ne_zero one_ne_zero 0 hθ0 fun z =>
      AnArc.summable_term hT one_ne_zero hθ hw (0, z)
    exact ⟨_, hv⟩
  have key : ∀ w : ℂ, T < w.im → ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w))
      (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr →
      ∃ (lam : ℂ) (f : Λ.A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧
        (∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (K.h v) = f v * Ψ.fr w j v) ∧
        ∀ v, Λ.A.Sum 1 0 θ w v = lam * thetaChar (τ w) c₁ c₂ (h.mulVec (K.h v)) * f v := by
    intro w hw fr hfr
    have hw0 := hT0.trans_lt hw
    have tr : ∀ (y y' : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) ϑ, y = y' →
        IsThetaFrameAt Xo.univ.t.PP y e ϑ fr → IsThetaFrameAt Xo.univ.t.PP y' e ϑ fr := by
      rintro y _ e ϑ rfl h
      exact h
    refine GlobalTheory.T.two_rigidified_theta_frames_on_fibre hL hL2 E H D l Xo Λ.A lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w) g K.h _ _ fr
      (hfib w (hT1.trans_lt hw)) (K.ex_eq w (hTK.trans_lt hw)) (tr _ _ _ _ (K.u_eq w (hTK.trans_lt hw)) hfr) ?_ θ hθ
      (hSne w hw0)
    obtain ⟨z, hz⟩ := Function.ne_iff.1 (TorusAlg.thetaChar_level (hτ w hw0).1 (hτ w hw0).2 hc₁ hc₂).1
    obtain ⟨z', rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu z
    exact ⟨z', hz⟩
  obtain ⟨rfl, rfl⟩ : c₁ = d₁ ∧ c₂ = d₂ := by
    obtain ⟨w, fr, hw, hfr⟩ := hex
    obtain ⟨lam, f, hlam, hf, hf0, -, -, hfS⟩ := key w hw fr hfr
    exact huniq c₁ c₂ hc₁ hc₂ w (hT0.trans_lt hw) (fun v => lam * f v) (hf.const_mul _)
      (fun v => mul_ne_zero hlam (hf0 v)) fun v => by rw [hfS]; ring
  refine ⟨κ, hκ, hdS, fun w _ => ?_, fun U s r hU _ hpull => ?_⟩
  · have e : (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) =
        fun z => (Λ.u.ex (K.h.symm z).2).left := funext fun z => Λ.ex0_b _
    rw [e]
    refine isFnInRigFrame_of_isFn Λ.u Λ.rig hfn (p := fun z => (K.h.symm z).2) K.h.symm.differentiable.snd
      (by simp) (Q := fun z => Q (K.h.symm z)) (hQ.comp K.h.symm.differentiable) (by simp [hQ0]) fun z => ?_
    rw [hoff w, ContinuousLinearEquiv.apply_symm_apply]
    ring
  · obtain ⟨T', hT'⟩ := GlobalTheory.T.arcSection_value_at_specialised_points_theta hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ th σ fam θ w₂ w₁ w₀ U s r hfin hth hθ
      hθ0 hfn r₂ r₁ r₀ hU hpull
    refine ⟨max T T', fun w hw => ?_⟩
    have hw1 : T < w.im := (le_max_left _ _).trans_lt hw
    have hw0 := hT0.trans_lt hw1
    obtain ⟨rw, hrw, hval⟩ := hT' w ((le_max_right _ _).trans_lt hw)
    refine ⟨rw, hrw, fun fr hfr z x j k j₀ hx hx' hj hj₀ => ?_⟩
    obtain ⟨v, rfl⟩ := K.h.surjective z
    obtain ⟨lam, f, hlam, hf, hf0, hf1, hfr', hfS⟩ := key w hw1 fr hfr
    obtain ⟨v₀, hv₀⟩ := hSne w hw0
    have hlk : lam = κ := by
      have := eq_at_zero_of_eq_off_zeros (AnArc.differentiable_Sum hT one_ne_zero hθ hw0).continuous
        (hf.const_mul lam) (hQ.cexp.const_mul κ) hv₀ fun v hv => by
          have h1 := hfS v
          have h2 : thetaChar (τ w) c₁ c₂ (h.mulVec (K.h v)) ≠ 0 := fun h0 => hv (by rw [h1, h0]; simp)
          refine mul_right_cancel₀ h2 ?_
          rw [← hSum w hw0 v, h1]
          ring
      simpa [hf1, hQ0] using this
    have hx2 : x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left := hx.trans (K.ex_eq w (hTK.trans_lt hw1) v)
    have hch : ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j₀ := by
      rw [← hx2]
      exact fun p hp => Set.mem_iInter.1 (hj₀ hp).1 PUnit.unit
    rw [hval v x j k j₀ hx2 hx' hj hj₀, hfr' v j₀ hch, hfS, hlk]
    ring

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelOneSectionEqKappaThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_levelOne_section_eq_kappa_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → ∃ T₂ : ℝ, ∀ T ≥ T₂, ∀ (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fu.Di K.i).La) (S : Finset (Fin g)) (h : Matrix (Fin g) (Fin g) ℂ) (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)), ThetaHyp W th σ fam → (∀ u v, (Fu.Di K.i).EF (bas u) (bas v) = -omegaStd u v) → (∀ u, Λ.ε (K.gam (bas u)).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0) → (∀ w k, h.mulVec (K.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ h.mulVec (K.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → (∃ w fr, T < w.im ∧ IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr) → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ k ∈ S, c₁ k = 0) ∧ (∀ w : ℂ, T < w.im → IsFnInRigFrame a.D₀ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) th (fun z => κ * thetaCharOff S (τ w) c₁ c₂ (h.mulVec z))) ∧ ∀ (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), ⊤ ≤ χ ⁻¹ᵁ U → s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U) → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (κ * rw * thetaChar (τ w) c₁ c₂ (h.mulVec z) * fr j₀ z) := by
  first | exact @GlobalTheory.ArcPts.arc_theta | exact GlobalTheory.ArcPts.arc_theta | (intros; apply GlobalTheory.ArcPts.arc_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExponentialFamilyDerivSumsAtPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentConstantDirectionSpecialisesDeriv
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentConstantDirectionSpecialisesDeriv
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecTangent

open TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem eq_dualMapR (φ : R →+* R') (ρ : DualNumber R →+* DualNumber R') (h : ∀ r, ρ (inl r) = inl (φ r))
    (he : ρ DualNumber.eps = DualNumber.eps) : ρ = dualMapR φ := by
  refine RingHom.ext fun a => ?_
  have e : a = inl a.fst + inl a.snd * DualNumber.eps := by ext <;> simp
  rw [e, map_add (f := _), map_mul, h, h, he]
  ext <;> simp [dualMapR]

theorem dualMapR_add (φ : R →+* R') (a b : R) : dualMapR φ (inl a + inr b) = inl (φ a) + inr (φ b) := by
  ext <;> simp [dualMapR]

theorem dualMapR_comp (φ : R →+* R') :
    (dualMapR φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem base_dualMapR {R₀ : Type} [CommRing R₀] (ψ : R₀ →+* R) (φ : R →+* R') {Z : Scheme.{0}} (y : Sp R₀ ⟶ Z) :
    spMap (dualMapR φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ spMap ψ ≫ y =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap (φ.comp ψ) ≫ y := by
  rw [← Category.assoc, ← spMap_comp, dualMapR_comp, spMap_comp _ (algebraMap R' _), spMap_comp ψ, Category.assoc,
    Category.assoc]

theorem dualMapR_injective {φ : R →+* R'} (h : Function.Injective φ) : Function.Injective (dualMapR φ) := by
  intro a b e
  ext
  · exact h (by simpa [dualMapR] using congrArg fst e)
  · exact h (by simpa [dualMapR] using congrArg snd e)

theorem isLocalRing_dual [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa only [isUnit_iff_isUnit_fst, fst_sub, fst_one] using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem isLocalHom_dualMapR (φ : R →+* R') [IsLocalHom φ] : IsLocalHom (dualMapR φ) :=
  ⟨fun a ha => isUnit_iff_isUnit_fst.2 (IsUnit.of_map φ _ (by
    simpa [dualMapR] using isUnit_iff_isUnit_fst.1 ha))⟩

theorem le_of_isLocalHom [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] {Z : Scheme.{0}}
    (x : Sp R ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  refine ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ U)).1 ?_).ge
  have := h (x := IsLocalRing.closedPoint R') trivial
  rw [← IsLocalRing.comap_closedPoint φ]
  exact this

end Dual

theorem exists_lift_open {X Z : Scheme.{0}} (x : X ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ z : X ⟶ U.toScheme, z ≫ U.ι = x :=
  ⟨IsOpenImmersion.lift U.ι x (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact h (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_sec_fibre {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {U : S.Opens} {N : ℕ}
    {K : Type} [CommRing K] {y : Sp K ⟶ S} (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ h : pullback G.hom y ⟶ (G.hom ⁻¹ᵁ U).toScheme, h ≫ (G.hom ⁻¹ᵁ U).ι = pullback.fst _ _ ∧
      ∀ b : LB.Sec (Out.powOver G L U N), ∃ s : SecP L (pullback.fst G.hom y) N,
        ∀ (R : Type) [CommRing R] (q : Sp R ⟶ pullback G.hom y) (j : L.ι), ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ L.U j →
          valR (q ≫ h) ((Out.powOver G L U N).U (fun _ => j)) (b.f (fun _ => j)) = sval s q j := by
  obtain ⟨h, e⟩ := exists_lift_open (pullback.fst G.hom y) (G.hom ⁻¹ᵁ U) (by
    rw [← Scheme.Hom.comp_preimage, pullback.condition]
    exact SpecCoord.comp_le_preimage _ _ _ hy)
  refine ⟨h, e, fun b => ?_⟩
  obtain ⟨s, hs, -⟩ := AmpleSpan.existsUnique_secScal hL (φ := fun _ : Fin N => (G.hom ⁻¹ᵁ U).ι) (ε := fun _ => 1)
    (φ' := fun _ : Fin 1 => pullback.fst G.hom y) (ε' := fun _ => (N : ℤ)) (h := h)
    (AmpleSpan.formEq_const e (by simp)) b
  exact ⟨s, fun R _ q j hj => SpanFrame.valR_of_secScal e hs q j hj⟩

theorem exists_deriv_comb {O : Type} [CommRing O] [StarRing O] (A : AnArc O) : ∃ T₀ : ℝ, ∀ (T T₁ : ℝ) (hT : T ≤ T₁),
    T₀ ≤ T₁ → ∀ (j : ℕ) [NeZero j] (f : A.V → Conv.halfRing T), IsComb A j (Conv.halfRing T) (fun v => f v) →
    ∀ z₀ : A.V, ∃ (n : ℕ) (r : Fin n → ℂ⸨X⸩) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ)
      (F : Fin n → ℂ⸨X⸩) (d : Conv.halfRing T₁), (∀ i, th i ∈ A.Theta j (α i)) ∧
      (∀ v, (f v : ℂ⸨X⸩) = ∑ i, r i * A.FSum j (α i) (th i) v) ∧ (∀ i, IsDFSum A j (α i) (th i) z₀ (F i)) ∧
      (d : ℂ⸨X⸩) = ∑ i, r i * F i ∧ ∀ w (hw : T₁ < w.im),
        Differentiable ℂ (fun v => Conv.ev T w (hT.trans_lt hw) (f v)) ∧
        Conv.ev T₁ w hw d = fderiv ℂ (fun v => Conv.ev T w (hT.trans_lt hw) (f v)) 0 z₀ := by
  obtain ⟨T₀, h₀⟩ := exists_formal_convergence O A
  refine ⟨T₀, fun T T₁ hT hT₀ j _ f hf z₀ => ?_⟩
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  obtain ⟨hS, hD⟩ := h₀ T₁ hT₀ j
  choose hm hv using fun i => (hS (α i) (th i) (h1 i).2).1
  choose F hF hFv using fun i => (hS (α i) (th i) (h1 i).2).2 z₀
  let r₁ : Fin n → Conv.halfRing T₁ := fun i => ⟨r i, Conv.halfRing_mono hT (h1 i).1⟩
  refine ⟨n, r, α, th, fun i => F i, ∑ i, r₁ i * F i, fun i => (h1 i).2, h2, hF,
    AddSubmonoidClass.coe_finsetSum _ _, fun w hw => ?_⟩
  have hd : ∀ i, Differentiable ℂ (A.Sum j (α i) (th i) w) := fun i => by
    have := hD (fun v => ⟨_, hm i v⟩) ⟨1, fun _ => 1, fun _ => α i, fun _ => th i,
      fun _ => ⟨one_mem _, (h1 i).2⟩, fun v => by simp⟩ w hw
    simpa only [hv] using this
  have key : (fun v => Conv.ev T w (hT.trans_lt hw) (f v)) =
      fun v => ∑ i, Conv.ev T₁ w hw (r₁ i) * A.Sum j (α i) (th i) w v := by
    funext v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Conv.ev_congr (hT.trans_lt hw) hw (s' := ∑ i, r₁ i * ⟨_, hm i v⟩)
      (by rw [AddSubmonoidClass.coe_finsetSum]; exact h2 v), map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv]
  rw [key]
  refine ⟨Differentiable.fun_sum fun i _ => (hd i).const_mul _, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fderiv_fun_sum fun i _ => ((hd i).const_mul _) 0, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hFv, fderiv_const_mul (hd i 0)]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ : GenPts A t y}

theorem exists_coords_tan {N : ℕ} [NeZero N] (C : Coords Φ N) {z₀ : A.V}
    {ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom y} (hν : Φ.IsTan z₀ ν) :
    ∃ (T₁ : ℝ) (hT : C.T ≤ T₁) (d : Fin C.n → Conv.halfRing T₁)
      (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ (t.G.hom ⁻¹ᵁ C.U).toScheme), ν' ≫ (t.G.hom ⁻¹ᵁ C.U).ι = ν ≫ pullback.fst _ _ ∧
      (∀ j, ⊤ ≤ (ν ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U j → ∃ u : (DualNumber ℂ⸨X⸩)ˣ, ∀ i,
        valR ν' ((Out.powOver t.G t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
          (inl (C.cf i 0 : ℂ⸨X⸩) + inr (d i : ℂ⸨X⸩)) * (u : DualNumber ℂ⸨X⸩)) ∧
      ∀ i w (hw : T₁ < w.im), Differentiable ℂ (fun v => Conv.ev C.T w (hT.trans_lt hw) (C.cf i v)) ∧
        Conv.ev T₁ w hw (d i) = fderiv ℂ (fun v => Conv.ev C.T w (hT.trans_lt hw) (C.cf i v)) 0 z₀ := by
  obtain ⟨T₀, h₀⟩ := exists_deriv_comb A
  choose n r α th F d hth hf hF hd hev using
    fun i => h₀ C.T (max C.T T₀) (le_max_left _ _) (le_max_right _ _) N (C.cf i) (C.comb i) z₀
  obtain ⟨h, e, hs⟩ := exists_sec_fibre (N := N) t.PP.isLB C.mem
  obtain ⟨h1, -, τ, hτ, hval⟩ := hν
  refine ⟨_, le_max_left _ _, d, ν ≫ h, by rw [Category.assoc, e], fun j hj => ⟨(hτ.1 j hj).unit ^ N, fun i => ?_⟩, hev⟩
  obtain ⟨s, hs⟩ := hs (C.b i)
  have hx : ∀ v, fib (Φ.x v) ≫ pullback.fst t.G.hom y = (Φ.x v).left := fun v => pullback.lift_fst _ _ _
  rw [hs _ ν j hj, sval_eq_sum_of_hasVal E H S A t y Φ N s (n i) (r i) (α i) (th i) (hth i) (fun v k hk => by
    rw [← hs _ _ k hk, ← hf]
    exact C.val i v _ k (by rw [Category.assoc, e, hx]) (hx v ▸ hk)) _ _ ν h1 j hj, hf, hd,
    Units.val_pow_eq_pow_val, IsUnit.unit_spec, inl_sum, inr_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hval N _ _ (hth i k) _ (hF i k) j hj, ← _root_.mul_assoc]
  congr 1
  ext1 <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem spec_tangent : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (z₀ : A.V) (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback o.t.G.hom y), Φ.IsTan z₀ ν → ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ νt : Sp (DualNumber (Γ.R w)) ⟶ o.t.G.left, νt ≫ o.t.G.hom = spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT ∧ (∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ⸨X⸩, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (r : ℂ⸨X⸩)) → ρ DualNumber.eps = DualNumber.eps → spMap ρ ≫ νt = ν ≫ pullback.fst _ _) ∧ ∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Γ.ev w r)) → ρ DualNumber.eps = DualNumber.eps → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ ≫ νt = (Ψ.pi w 0).left ∧ ∀ (W : o.t.G.left.Opens) (f : Γ(o.t.G.left, W)), ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (spMap ρ ≫ νt) W f) = fderiv ℂ (fun v => valAt' (Ψ.pi w v).left W f) 0 z₀ := by
  intro hL hL₂ E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hΦ z₀ ν hν
  obtain ⟨C⟩ := T.nonempty_projCoords_convergent_coefficients hL hL₂ E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨T₁, hT₁, d, ν', eν, hc, hd⟩ := exists_coords_tan C hν
  obtain ⟨T₂, hT₂, hT₃, hs⟩ := SpecCoord.spec_coords E H D l B bb S s o A y Φ Γ Ψ 4 C
  refine ⟨max T₁ T₂, le_max_of_le_right hT₂, fun w hw hw' => ?_⟩
  have hw₁ : T₁ < w.im := (le_max_left _ _).trans_lt hw'
  have hwC : C.T < w.im := hT₁.trans_lt hw₁
  obtain ⟨hy, hg, hv⟩ := hs w ((le_max_right _ _).trans_lt hw')
  haveI := ArcSectionValue.isLocalRing_germ Γ w
  haveI := isLocalRing_dual (R := Γ.R w)
  haveI := o.proper
  haveI : IsLocalHom (Γ.ev w).toRingHom := ⟨fun a ha => Γ.unit w a ha.ne_zero⟩
  haveI := isLocalHom_dualMapR (Γ.ev w).toRingHom
  obtain ⟨j, hj⟩ := ArcSectionValue.exists_chart_local (ν ≫ pullback.fst o.t.G.hom y) o.t.PP.isLB
  obtain ⟨u, hu⟩ := hc j hj
  obtain ⟨i₀, hi₀⟩ := C.bpf w hwC 0
  obtain ⟨x, ⟨x1, x2, x3⟩, -⟩ := T.existsUnique_lift_coords_localSubring S o.t.G o.t.PP.L C.U 4 C.n C.b (DualNumber (Γ.R w)) (DualNumber ℂ⸨X⸩)
    (dualMapR (Γ.R w).val.toRingHom)
    (spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫
      spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ν'
    (fun i => inl (Subalgebra.inclusion (Γ.le C.T w hwC) (C.cf i 0)) +
      inr (Subalgebra.inclusion (Γ.le T₁ w hw₁) (d i))) j u o.t.PP.isLB C.aff C.emb
    (dualMapR_injective Subtype.val_injective) (SpecCoord.comp_le_preimage _ _ _ (hg hw))
    (by
      rw [reassoc_of% eν, pullback.condition, reassoc_of% hν.1, base_dualMapR]
      exact congrArg _ Ψ.yT_gen.symm)
    (eν ▸ hj) (fun i => by rw [hu, dualMapR_add]; rfl)
    ⟨i₀, isUnit_iff_isUnit_fst.2 (by
      rw [fst_add, fst_inl, fst_inr, add_zero]
      exact Γ.unit w _ (by rwa [Γ.ev_eq]))⟩
  refine ⟨x ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι, (Category.assoc _ _ _).trans x1, fun ρ h he => ?_, fun ρ h he => ?_⟩
  · rw [eq_dualMapR (Γ.R w).val.toRingHom ρ h he, reassoc_of% x2, eν]
  obtain rfl := eq_dualMapR (Γ.ev w).toRingHom ρ h he
  choose p hp using fun v => exists_lift_open (Ψ.pi w v).left (o.t.G.hom ⁻¹ᵁ C.U) (by
    rw [← Scheme.Hom.comp_preimage, Over.w]
    exact hy)
  have key := ((coords_determine_family S o.t.G o.t.PP.L C.U 4 C.n C.b (Ψ.yw w) A.V p
    (fun i v => Conv.ev C.T w hwC (C.cf i v)) o.t.PP.isLB C.aff C.emb
    (fun v => by rw [reassoc_of% hp v]; exact Over.w _)
    (fun v k hk => by
      rw [hp] at hk
      refine ⟨Ψ.fr w k v ^ 4, pow_ne_zero _ ?_, fun i => hv i v _ k (hp v) hk⟩
      refine (((Ψ.τt_frm w hw v).1 k (SpecCoord.germ_le_preimage Γ w _ _ ?_)).map (Γ.ev w)).ne_zero
      rwa [← Ψ.pi_eq w hw v])).2 fun i => (hd i w hw₁).1).2 z₀ (spMap (dualMapR (Γ.ev w).toRingHom) ≫ x)
    (by
      rw [Category.assoc, x1, base_dualMapR, Ψ.yw_eq w hw]
      congr 3
      exact RingHom.ext fun r => Γ.ev_eq Ψ.T w hw r)
    (fun k hk => by
      rw [Category.assoc] at hk
      have hk' := le_of_isLocalHom _ _ hk
      obtain ⟨u', hu'⟩ := x3 k hk'
      set_option synthInstance.maxHeartbeats 200000 in
      refine ⟨Units.map (dualMapR (Γ.ev w).toRingHom).toMonoidHom u', fun i => ?_⟩
      have hx : ⊤ ≤ x ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U 4).U (fun _ => k) :=
        fun z hz => Set.mem_iInter.2 fun _ => hk' hz
      rw [HolHom.valR_spMap _ _ _ hx, hu', map_mul, dualMapR_add,
        ← (hd i w hw₁).2, ← Γ.ev_eq, ← Γ.ev_eq]
      rfl)
  simp only [hp, Category.assoc] at key
  refine ⟨?_, fun W f hW => (key W f).2 hW⟩
  rw [← hp 0, ← (key ⊤ 0).1, Category.assoc, Category.assoc]

end GlobalTheory.SpecTangent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentConstantDirectionSpecialisesDerivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_constant_direction_specialises_deriv : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (z₀ : A.V) (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback o.t.G.hom y), Φ.IsTan z₀ ν → ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ νt : Sp (DualNumber (Γ.R w)) ⟶ o.t.G.left, νt ≫ o.t.G.hom = spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT ∧ (∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ⸨X⸩, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (r : ℂ⸨X⸩)) → ρ DualNumber.eps = DualNumber.eps → spMap ρ ≫ νt = ν ≫ pullback.fst _ _) ∧ ∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Γ.ev w r)) → ρ DualNumber.eps = DualNumber.eps → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ ≫ νt = (Ψ.pi w 0).left ∧ ∀ (W : o.t.G.left.Opens) (f : Γ(o.t.G.left, W)), ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (spMap ρ ≫ νt) W f) = fderiv ℂ (fun v => valAt' (Ψ.pi w v).left W f) 0 z₀ := by
  first | exact @GlobalTheory.SpecTangent.spec_tangent | exact GlobalTheory.SpecTangent.spec_tangent | (intros; apply GlobalTheory.SpecTangent.spec_tangent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExponentialFamilyDerivSumsAtPeriod
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcDeriv

open TrivSqZeroExt HolHom
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem dual_inl (φ : R →+* R') (r : R) : dualMapR φ (inl r) = inl (φ r) := by
  ext <;> simp [dualMapR]

theorem dual_eps (φ : R →+* R') : dualMapR φ DualNumber.eps = DualNumber.eps := by
  ext <;> simp [dualMapR]

theorem snd_dual (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).snd = φ a.snd := by
  simp [dualMapR]

theorem fst_dual (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).fst = φ a.fst := by
  simp [dualMapR]

theorem dual_comp (φ : R →+* R') :
    (dualMapR φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ :=
  RingHom.ext fun a => dual_inl φ a

theorem dual_injective {φ : R →+* R'} (h : Function.Injective φ) : Function.Injective (dualMapR φ) := by
  intro a b e
  ext
  · exact h (by rw [← fst_dual, e, fst_dual])
  · exact h (by rw [← snd_dual, e, snd_dual])

theorem fst_alg {Z : Scheme.{0}} (y : Sp R ⟶ Z) :
    spMap (fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) ≫ y = y := by
  rw [← Category.assoc, ← Spec.map_comp]
  convert Category.id_comp y
  rw [← Spec.map_id]
  congr 1

theorem le_of_unit (ψ : R →+* ℂ) (hψ : ∀ a, ψ a ≠ 0 → IsUnit a) {Z : Scheme.{0}} (x : Sp R ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  let p : PrimeSpectrum R := spMap ψ (default : PrimeSpectrum ℂ)
  have hp : p ∈ (show Set (PrimeSpectrum R) from (x ⁻¹ᵁ U).carrier) :=
    hU (x := (default : PrimeSpectrum ℂ)) trivial
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp (x ⁻¹ᵁ U).isOpen
  have hu : IsUnit r := hψ r fun h => hr (by
    change ψ r ∈ (default : PrimeSpectrum ℂ).asIdeal
    rw [h]; exact Ideal.zero_mem _)
  exact fun q _ => hle (a := q) fun hq => q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)

end Dual

section Core

variable {K F : Type} [CommRing K] [CommRing F] {GX GF Z : Scheme.{0}} {p : GF ⟶ GX} {q : GF ⟶ Sp F}
  {t : GX ⟶ Sp K} {κ : K →+* F}

theorem exists_lift (H : IsPullback p q t (spMap κ)) {A B : Type} [CommRing A] [CommRing B] (i : A →+* B)
    (hi : Function.Injective i) (x : Sp A ⟶ GX) (n : Sp B ⟶ GF) (ρ : F →+* A) (hx : spMap i ≫ x = n ≫ p)
    (hn : n ≫ q = spMap (i.comp ρ)) : ∃ x' : Sp A ⟶ GF, x' ≫ p = x ∧ x' ≫ q = spMap ρ ∧ spMap i ≫ x' = n := by
  have hover : x ≫ t = spMap ρ ≫ spMap κ := by
    rw [← spMap_comp]
    refine ArcPoint.eq_spMap_of_injective i hi _ _ ?_
    rw [reassoc_of% hx, H.w, reassoc_of% hn, ← spMap_comp, RingHom.comp_assoc]
  refine ⟨H.lift x _ hover, H.lift_fst _ _ _, H.lift_snd _ _ _, H.hom_ext ?_ ?_⟩
  · rw [Category.assoc, H.lift_fst, hx]
  · rw [Category.assoc, H.lift_snd, hn, spMap_comp]

theorem isDerivAt_of_fst (H : IsPullback p q t (spMap κ)) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {c : V → (Sp ℂ ⟶ GF)} {z w : V} {b : Sp ℂ ⟶ Sp F} (hc : ∀ s, c s ≫ q = b) (hol : HolAt (fun s => c s ≫ p) z)
    {v : Sp (DualNumber ℂ) ⟶ GF} (hv : IsDerivAt (fun s => c s ≫ p) z w (v ≫ p)) (hq : v ≫ q = constVec b) :
    IsDerivAt c z w v := by
  have e : (fun s => c s ≫ q) = fun _ => b := funext hc
  obtain ⟨u, hu⟩ := (holAt_of_isPullback H hol (e ▸ holAt_const b z)).exists_isDerivAt w
  have : v = u := H.hom_ext (hv.unique (hu.comp p)) (hq.trans ((isDerivAt_const b z w).unique (e ▸ hu.comp q)))
  exact this ▸ hu

theorem sumsAt_fderiv (H : IsPullback p q t (spMap κ)) (bF : F →+* ℂ) (φ : GF ⟶ Z) (U : Z.Opens) (f : Γ(Z, U))
    (Γ : Germs) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (z₀ : V) (n : Sp (DualNumber ℂ⸨X⸩) ⟶ GF)
    (hn : n ≫ q = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) ≫ spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    (hU : ⊤ ≤ (n ≫ φ) ⁻¹ᵁ U) (S : ℂ⟦X⟧) (hS : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ S = snd (valR (n ≫ φ) U f))
    {T T₀ : ℝ} (o : Sp (Conv.halfRing T) ⟶ GX)
    (ho : spMap (Conv.halfRing T).val.toRingHom ≫ o = spMap (fstHom ℂ⸨X⸩ ℂ⸨X⸩ ℂ⸨X⸩).toRingHom ≫ n ≫ p)
    (e : ℂ → V → (Sp ℂ ⟶ GX))
    (he : ∀ (w : ℂ) (hw : T < w.im), T₀ < w.im → HolAt (e w) 0 ∧ e w 0 = spMap (Conv.ev T w hw).toRingHom ≫ o ∧
      ∃ ν : Sp (DualNumber (Γ.R w)) ⟶ GX, spMap (dualMapR (Γ.R w).val.toRingHom) ≫ ν = n ≫ p ∧
        IsDerivAt (e w) 0 z₀ (spMap (dualMapR (Γ.ev w).toRingHom) ≫ ν)) :
    ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ c : V → (Sp ℂ ⟶ GF), (∀ z, c z ≫ p = e w z ∧ c z ≫ q = spMap bF) →
      SumsAt S w (fderiv ℂ (fun z => valAt' (c z ≫ φ) U f) 0 z₀) := by
  obtain ⟨o', o1, o2, o3⟩ := exists_lift H (Conv.halfRing T).val.toRingHom Subtype.val_injective o
    (spMap (fstHom ℂ⸨X⸩ ℂ⸨X⸩ ℂ⸨X⸩).toRingHom ≫ n) ((algebraMap ℂ (Conv.halfRing T)).comp bF)
    (by rw [ho, Category.assoc]) (by rw [Category.assoc, hn, fst_alg]; rfl)
  obtain ⟨T₁, hT₁, h₁, -⟩ := Conv.exists_valAt'_halfCurve (yT := o' ≫ φ) (U := U) rfl (by
    intro x _
    have h1 : ⊤ ≤ (spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ o' ≫ φ) ⁻¹ᵁ U := by
      rw [← Category.assoc, ← spMap_comp]
      erw [reassoc_of% o3]
      exact fun y _ => hU (x := spMap _ y) trivial
    obtain rfl : x = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact h1 (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial)
  have key : ∀ w : ℂ, max T₀ T₁ < w.im → ∃ s : Γ.R w, (s : ℂ⸨X⸩) = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ S ∧
      ∀ c : V → (Sp ℂ ⟶ GF), (∀ z, c z ≫ p = e w z ∧ c z ≫ q = spMap bF) →
        Γ.ev w s = fderiv ℂ (fun z => valAt' (c z ≫ φ) U f) 0 z₀ := by
    intro w hw
    have hw₁ : T₁ < w.im := (le_max_right _ _).trans_lt hw
    have hwT : T < w.im := hT₁.trans_lt hw₁
    obtain ⟨hol, e0, ν, ν1, ν2⟩ := he w hwT ((le_max_left _ _).trans_lt hw)
    obtain ⟨ν', a1, a2, a3⟩ := exists_lift H (dualMapR (Γ.R w).val.toRingHom) (dual_injective Subtype.val_injective)
      ν n ((algebraMap (Γ.R w) (DualNumber (Γ.R w))).comp ((algebraMap ℂ (Γ.R w)).comp bF)) ν1
      (by rw [hn, ← RingHom.comp_assoc, dual_comp, ← spMap_comp]; rfl)
    have hq : (spMap (dualMapR (Γ.ev w).toRingHom) ≫ ν') ≫ q = constVec (spMap bF) := by
      rw [Category.assoc, a2, ← spMap_comp, ← RingHom.comp_assoc, dual_comp, constVec, ← spMap_comp,
        RingHom.comp_assoc]
      congr 3
      exact RingHom.ext fun x => (Γ.ev w).commutes (bF x)
    have h0 : spMap (fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (dualMapR (Γ.ev w).toRingHom) ≫ ν' =
        spMap (Conv.ev T w hwT).toRingHom ≫ o' := by
      refine H.hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [a1, ν2.1, e0, o1]
      · rw [Category.assoc, hq, fst_constVec, Category.assoc, o2, ← spMap_comp]
        congr 2
        exact RingHom.ext fun x => ((Conv.ev T w hwT).commutes (bF x)).symm
    have hz : ⊤ ≤ (spMap (Conv.ev T w hwT).toRingHom ≫ o' ≫ φ) ⁻¹ᵁ U := by
      have := h₁ w hw₁
      rwa [Conv.halfCurve_eq _ hwT] at this
    have hν : ⊤ ≤ (ν' ≫ φ) ⁻¹ᵁ U := by
      refine le_of_unit ((fstHom ℂ ℂ ℂ).toRingHom.comp (dualMapR (Γ.ev w).toRingHom)) (fun a ha => ?_) _ ?_
      · exact isUnit_iff_isUnit_fst.2 (Γ.unit w _ fun h => ha ((fst_dual _ a).trans h))
      · rw [spMap_comp, Category.assoc, reassoc_of% h0]
        exact hz
    refine ⟨snd (valR (ν' ≫ φ) U f), ?_, fun c hc => ?_⟩
    · rw [hS, ← a3, Category.assoc, valR_spMap _ _ _ hν, snd_dual]
      rfl
    · have ec : (fun z => c z ≫ p) = e w := funext fun z => (hc z).1
      have hd := isDerivAt_of_fst H (fun z => (hc z).2) (ec ▸ hol) (w := z₀)
        (v := spMap (dualMapR (Γ.ev w).toRingHom) ≫ ν') (by rw [ec, Category.assoc, a1]; exact ν2) hq
      have := (hd.comp φ).2 U (by beta_reduce; rw [← hd.1, h0, Category.assoc]; exact hz) f
      rw [← this, Category.assoc, valR_spMap _ _ _ hν, snd_dual]
      rfl
  obtain ⟨T₂, h₂⟩ : ∃ T₂, algebraMap ℂ⟦X⟧ ℂ⸨X⸩ S ∈ Conv.halfRing T₂ := by
    obtain ⟨s, hs, -⟩ := key (((max T₀ T₁ + 1 : ℝ) : ℂ) * Complex.I) (by simp)
    obtain ⟨T₃, hw₃, a, b, hb, hab⟩ := Γ.frac _ s
    have hb0 : (b : ℂ⸨X⸩) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h, map_zero])
    rw [← Conv.mem_convLaurent_iff_halfRing, ← hs, ← (eq_inv_mul_iff_mul_eq₀ hb0).2 hab |>.symm]
    exact mul_mem (Conv.convLaurent.inv_mem (Conv.halfRing_le_convLaurent _ b.2))
      (Conv.halfRing_le_convLaurent _ a.2)
  refine ⟨max (max T₀ T₁) T₂, fun w hw c hc => ?_⟩
  have hw₂ : T₂ < w.im := (le_max_right _ _).trans_lt hw
  obtain ⟨s, hs, h⟩ := key w ((le_max_left _ _).trans_lt hw)
  rw [← h c hc, show s = Subalgebra.inclusion (Γ.le T₂ w hw₂) ⟨_, h₂⟩ from Subtype.ext hs, Γ.ev_eq]
  exact Conv.sumsAt_ev_of_eq hw₂ rfl

end Core

section Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {A : AnArc (𝓞 E)}

def IsTanPt {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} (Φ : GenPts A t y) (z₀ : A.V)
    (n : Sp (DualNumber ℂ⸨X⸩) ⟶ t.G.left) : Prop :=
  ∃ ν, Φ.IsTan z₀ ν ∧ ν ≫ pullback.fst _ _ = n

theorem isTanPt_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} {m : SABMap t' t f}
    {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {y' : Sp ℂ⸨X⸩ ⟶ S'} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ' : GenPts A t' y'}
    {Φ : GenPts A t y} (hw : w.IsGen) (h : GenPts.Rel m w Φ' Φ) (z₀ : A.V)
    {n : Sp (DualNumber ℂ⸨X⸩) ⟶ t'.G.left} (hn : n ≫ t'.G.hom = spMap (algebraMap ℂ⸨X⸩ _) ≫ y') :
    IsTanPt Φ' z₀ n ↔ IsTanPt Φ z₀ (n ≫ m.φ) := by
  have key := (T.arcLevelPoint_tangentVector_transport_iff E H S S' A t t' f m w y' y Φ' Φ hw h).2 z₀
  have hn' : (n ≫ m.φ) ≫ t.G.hom = spMap (algebraMap ℂ⸨X⸩ _) ≫ y := by
    rw [Category.assoc, m.cart.1.w, reassoc_of% hn, h.1]
  constructor
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨pullback.lift _ _ hn', (key ν _ (by rw [pullback.lift_fst, Category.assoc]) (by rw [pullback.lift_snd, hν.1])).1 hν,
      pullback.lift_fst _ _ _⟩
  · rintro ⟨ν, hν, e⟩
    exact ⟨pullback.lift _ _ hn, (key _ ν (by rw [pullback.lift_fst_assoc, e]) (by rw [pullback.lift_snd, hν.1])).2 hν,
      pullback.lift_fst _ _ _⟩

end Move

theorem deriv_sumsAt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → C.Φ.Rational → ∀ (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (V : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, V)), DiffHyp W (fun z => Λ.ex0 (K.h.symm z)) z₀ ν v → ⊤ ≤ (v.left ≫ W.m.φ) ⁻¹ᵁ V → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left), (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left ∧ xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF) → SumsAt (TrivSqZeroExt.snd (valR (A := DualNumber (PowerSeries ℂ)) (v.left ≫ W.m.φ) V f)) w (fderiv ℂ (fun z => valAt' (xF z ≫ Y.m.φ) V f) 0 z₀) := by
  intro hL hL₂ E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hA hΦ z₀ ν v V f hd hV
  let ρ := dualMapR (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)
  have hW : (spMap ρ ≫ v.left) ≫ W.t.G.hom = spMap (algebraMap ℂ⸨X⸩ _) ≫ gen := by
    rw [Category.assoc, Over.w v]
    exact (spMap_comp _ _).symm.trans ((congrArg spMap (dual_comp _)).trans (spMap_comp _ _))
  have tW : IsTanPt C.ΦW (K.h.symm z₀) (spMap ρ ≫ v.left) :=
    ⟨pullback.lift _ _ hW, T.isTangent_constant_coords_generic_fibre hL hL₂ E H D l Xo c O β Y _ a χ W Λ C.Ξ C.ΦW g K.h z₀ ν v ρ _ C.isGen hd
      (dual_inl _) (dual_eps _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  have tY := (isTanPt_iff C.rig₂.1 C.rel₂ _ hW).1 tW
  have hY : ((spMap ρ ≫ v.left) ≫ W.m.φ) ≫ Y.t.G.hom = (spMap (algebraMap ℂ⸨X⸩ _) ≫ C.yF) ≫ Y.j := by
    rw [Category.assoc, W.m.cart.1.w, ← Category.assoc, hW, Category.assoc, Category.assoc, C.yF_j]
  obtain ⟨n, n1, n2⟩ : ∃ n : Sp (DualNumber ℂ⸨X⸩) ⟶ Y.oF.t.G.left, n ≫ Y.m.φ = (spMap ρ ≫ v.left) ≫ W.m.φ ∧
      n ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ⸨X⸩ _) ≫ C.yF :=
    ⟨Y.m.cart.1.lift _ _ hY, Y.m.cart.1.lift_fst _ _ _, Y.m.cart.1.lift_snd _ _ _⟩
  have tF := (isTanPt_iff C.rig₁.1 C.rel₁ _ n2).2 (n1 ▸ tY)
  obtain ⟨νU, tU, eU⟩ := (isTanPt_iff C.rig₀.1 C.rel₀ _ n2).1 tF
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨T₀, -, h₀⟩ := T.tangent_constant_direction_specialises_deriv hL hL₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hA hΦ _ νU tU
  have HP : IsPullback Y.m0.toSABMap.φ (Y.oF.t.G.hom ≫ pullback.snd _ _) (Xo.univ.t.G.hom ≫ Xo.s)
      (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    Y.m0.toSABMap.cart.1.paste_vert (IsPullback.of_hasPullback _ _)
  refine sumsAt_fderiv HP bF Y.m.φ V f Γ z₀ n (by rw [reassoc_of% n2, C.yF_over]) ?_ _ ?_ (T := Ψ.T)
    (T₀ := max T₀ K.T) (Ψ.yT ≫ eSec Xo.univ.t.G) ?_ (fun w z => (Fu.ex K.i (K.Pw w) z).left) fun w hw hw' => ?_
  · rw [n1, Category.assoc]
    exact fun x _ => hV (x := spMap ρ x) trivial
  · rw [n1, Category.assoc, valR_spMap _ _ _ hV, snd_dual]
  · rw [← eU, reassoc_of% tU.2.1, fib, pullback.lift_fst, map_zero_eq_one C.Φ.add, reassoc_of% Ψ.yT_gen]
    rfl
  have hK : K.T < w.im := (le_max_right _ _).trans_lt hw'
  have hP := K.period w hK
  obtain ⟨νt, -, b1, b2⟩ := h₀ w hw ((le_max_left _ _).trans_lt hw')
  obtain ⟨b2, b3⟩ := b2 (dualMapR (Γ.ev w).toRingHom) (dual_inl _) (dual_eps _)
  have ex : ∀ z, (Fu.ex K.i (K.Pw w) z).left = (Ψ.pi w (K.h.symm z)).left := fun z => by
    rw [← K.ex_eq w hK, K.h.apply_symm_apply]
  refine ⟨holAt_of_isHolTo (isHolTo_ex Fu K.i hP) trivial, ?_, νt, (b1 _ (dual_inl _) (dual_eps _)).trans eU, ?_,
    fun U hU k => ?_⟩
  · rw [map_zero_eq_one (Fu.ex_add K.i _ hP), ← Category.assoc, ← Ψ.yw_eq w hw, ← K.u_eq w hK]
    rfl
  · beta_reduce
    rw [b2, ex, map_zero]
  · simp only [ex, map_zero] at hU ⊢
    rw [b3 U k hU]
    have := K.h.symm.comp_right_fderiv (f := fun v => valAt' (Ψ.pi w v).left U k) (x := 0)
    rw [map_zero] at this
    exact (congrArg (· z₀) this).symm

end GlobalTheory.ArcDeriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExponentialFamilyDerivSumsAtPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialFamily_deriv_sumsAt_period : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → C.Φ.Rational → ∀ (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (V : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, V)), DiffHyp W (fun z => Λ.ex0 (K.h.symm z)) z₀ ν v → ⊤ ≤ (v.left ≫ W.m.φ) ⁻¹ᵁ V → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left), (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left ∧ xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF) → SumsAt (TrivSqZeroExt.snd (valR (A := DualNumber (PowerSeries ℂ)) (v.left ≫ W.m.φ) V f)) w (fderiv ℂ (fun z => valAt' (xF z ≫ Y.m.φ) V f) 0 z₀) := by
  first | exact @GlobalTheory.ArcDeriv.deriv_sumsAt | exact GlobalTheory.ArcDeriv.deriv_sumsAt | (intros; apply GlobalTheory.ArcDeriv.deriv_sumsAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtAnOrthKerIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem gtAn_orth_ker_iff : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (v : Λ.A.La), (∀ v' : Λ.A.La, Λ.ε v'.y = 0 → Λ.A.EF v v' = 0) ↔ (Λ.ε v.y = 0 ∧ ∀ s : ℂ, ∃ x, IsTorusPt (Λ.ex0 (s • Λ.A.P0 v)) x ∧ ∀ v' : Λ.A.La, x (Λ.ε v'.y) = eTwoPi (-(s * Λ.A.EF v v'))) := by
  intro _ _ E _ _ _ H _ D l c O _ β _ _ b a Λ v
  obtain ⟨-, -, htor, hlam⟩ := GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints E H D l c O β b a Λ
  have hε : ∀ x : Λ.A.X, Λ.ε x = 0 ↔ x = 0 := fun x => map_eq_zero_iff _ Λ.ε.injective
  simp only [hε]
  constructor
  · intro h
    refine ⟨((Λ.A.orth_ker_iff v).1 h).1, fun s => ?_⟩
    obtain ⟨h2, h1⟩ := Λ.A.smul_periodMap_of_orthogonal_ker h s
    have hz : s • Λ.A.P0 v = ((s • Λ.A.P0 v).1, 0) := Prod.ext rfl h2
    refine ⟨fun x => eTwoPi ((s • Λ.A.P0 v).1 (Λ.ε.symm x)), ?_, fun v' => ?_⟩
    · have := htor (s • Λ.A.P0 v).1
      rwa [← hz] at this
    · have h3 : Λ.ε.symm (Λ.ε v'.y) = v'.y := Λ.ε.symm_apply_apply _
      simp only [h3, h1]
  · rintro ⟨hv, h⟩
    refine (Λ.A.orth_ker_iff_forall_smul_mem v).2 ⟨hv, fun s => ?_⟩
    obtain ⟨x, hx, -⟩ := h s
    exact hlam _ x hx

end GlobalTheory.ArcPts
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem isHolTo_comp_clm {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V']
    [NormedSpace ℂ V'] {X : Scheme.{0}} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo Set.univ y) (φ : V' →L[ℂ] V) :
    IsHolTo Set.univ (fun z => y (φ z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hy U f
  exact ⟨h1.preimage φ.continuous, h2.comp φ.differentiable.differentiableOn fun _ hz => hz⟩

theorem nonempty_holArc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), C.Φ.Rational → (∀ v, Λ.Rep l.A (a.etaA v) (laA v)) → (∀ v, Λ.Rep l.M (a.eta v) (laM v)) → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → Nonempty (HolArc Y bF a χ W Fu) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hrat hA hM lin cst T₁ hfib
  obtain ⟨hadd, honto, hlin⟩ := ex0_additive_surjective_equivariant hL hL2 E H D l c O β _ a Λ
  obtain ⟨hb, hchi⟩ := analyticDictionaryExp_holomorphic_over_unif E H D l c O β _ a Λ
  obtain ⟨hker, hiota, htor, -⟩ := GtKer.ker_iota_torus E H D l c O β _ a Λ
  have hfin : AnFin Λ.A := (ArcThetaSpaces.sections_theta hL hL2 E H D l c O β _ a Λ).2.1
  have hrie := gtAn_orth_ker_iff hL hL2 E H D l c O β _ a Λ
  have hpt := ArcPoint.point_sumsAt E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K
  have hdiff := GlobalTheory.T.exponentialFamily_deriv_sumsAt_period hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin hrat
  obtain ⟨T₂, hth⟩ := GlobalTheory.T.arc_levelOne_section_eq_kappa_theta hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin lin cst T₁ hfib
  have hrep := GlobalTheory.T.exists_latticeVector_rep_and_shift hL hL2 E H D l c O β _ a Λ
  have hsm : ∀ (s : ℂ) (v : Λ.A.V), K.h.symm (s • K.h v) = s • v := fun s v => by
    rw [map_smul, K.h.symm_apply_apply]
  refine ⟨{
    i := K.i
    T := max K.T T₂
    P₀ := (K.h.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp Λ.A.P0).comp K.gam.toAddEquiv.toAddMonoidHom
    N := (K.h.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp Λ.A.N).comp K.gam.toAddEquiv.toAddMonoidHom
    Pw := K.Pw
    Pw_eq := fun w v => ?_
    y := Λ.ε.toLinearMap ∘ₗ Λ.A.yLin ∘ₗ K.gam.toLinearMap
    y_onto := Λ.ε.surjective.comp (Λ.A.yLin_surjective.comp K.gam.surjective)
    ex₀ := fun z => Λ.ex0 (K.h.symm z)
    period := fun w hw => K.period w (lt_of_le_of_lt (le_max_left _ _) hw)
    add := fun z z' => ?_
    onto := honto.comp K.h.symm.surjective
    lin := fun x z => ?_
    hol_b := isHolTo_comp_clm hb (K.h.symm : (Fin g → ℂ) →L[ℂ] Λ.A.V)
    hol_chi := fun x j => (hchi x j).1.comp K.h.symm.differentiable.differentiableOn fun _ hz => hz
    ker := fun z => ?_
    iota := fun v => ?_
    shift := fun w v => ?_
    levelA := fun v => ?_
    levelM := fun v hv => ?_
    riemann := fun v => ?_
    point := hpt
    diff := fun z₀ ν v V f h1 h2 h3 => hdiff z₀ ν v V f ⟨h1, h2, h3⟩
    theta := fun th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ h1 h2 h3 =>
      hth _ (le_max_right _ _) th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ ⟨h1, h2, h3⟩ }⟩
  · show K.Pw w v = K.h (Λ.A.P0 (K.gam v)) + w • K.h (Λ.A.N (K.gam v))
    rw [K.Pw_eq, AnArc.Pw_apply, map_add (f := _), map_smul]
  · rw [map_add (f := _)]; exact hadd _ _
  · have : K.h.symm (fun k => ty k (x : E) * z k) = Λ.A.actV x (K.h.symm z) := by
      apply K.h.injective
      funext k
      rw [K.h_act, K.h.apply_symm_apply, K.h.apply_symm_apply]
    rw [this]
    exact hlin x _
  · refine (hker _).trans ⟨?_, ?_⟩
    · rintro ⟨la, h0, hz⟩
      obtain ⟨v, rfl⟩ := K.gam.surjective la
      refine ⟨v, ?_, ?_⟩
      · show Λ.ε (K.gam v).y = 0
        rw [h0, map_zero]
      · show z = K.h (Λ.A.P0 (K.gam v))
        rw [← hz, K.h.apply_symm_apply]
    · rintro ⟨v, h0, hz⟩
      refine ⟨K.gam v, (map_eq_zero_iff _ Λ.ε.injective).1 h0, ?_⟩
      rw [hz]
      exact K.h.symm_apply_apply _
  · show Out.GtPtF.IsIota (Λ.ε (K.gam v).y) (Λ.ex0 (K.h.symm (K.h (Λ.A.P0 (K.gam v)))))
    rw [K.h.symm_apply_apply]
    exact hiota _
  · show IsTorusPt (Λ.ex0 (K.h.symm (w • K.h (Λ.A.N (K.gam v))))) (fun x => eTwoPi (w * a.be (Λ.ε (K.gam v).y) x))
    have h1 : w • Λ.A.N (K.gam v) = ((w • Λ.A.N (K.gam v)).1, 0) := Prod.ext rfl (by simp [AnArc.N])
    rw [hsm, h1]
    convert htor (w • Λ.A.N (K.gam v)).1 using 3 with x
    show _ = w * ((Λ.A.be (K.gam v).y (Λ.ε.symm x) : ℤ) : ℂ)
    rw [Λ.be_eq, Λ.ε.apply_symm_apply]
  · obtain ⟨e, he⟩ := K.levA v
    obtain ⟨q, h1, h2, h3⟩ := (hrep l.A l.A_pos).2 _ _ e (hA v)
    rw [← he] at h1 h2
    exact ⟨q, h1, h2.trans (congrArg Λ.ex0 (hsm _ _).symm), h3⟩
  · obtain ⟨e, he⟩ := K.levM v hv
    obtain ⟨q, h1, h2, h3⟩ := (hrep l.M (le_trans (by norm_num) l.three_le)).2 _ _ e (hM v)
    rw [← he] at h1 h2
    exact ⟨q, h1, h2.trans (congrArg Λ.ex0 (hsm _ _).symm), h3⟩
  · show (∀ v', Λ.ε (K.gam v').y = 0 → (Fu.Di K.i).EF v v' = 0) ↔ (Λ.ε (K.gam v).y = 0 ∧ ∀ s : ℂ, ∃ x,
      IsTorusPt (Λ.ex0 (K.h.symm (s • K.h (Λ.A.P0 (K.gam v))))) x ∧
        ∀ v', x (Λ.ε (K.gam v').y) = eTwoPi (-(s * (Fu.Di K.i).EF v v')))
    simp only [hsm, ← K.EF_eq]
    have := hrie (K.gam v)
    simp only [K.gam.surjective.forall] at this
    exact this

end GlobalTheory.ArcPts

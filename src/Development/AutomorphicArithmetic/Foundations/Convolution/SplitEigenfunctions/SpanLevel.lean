module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ProdBd
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.IILaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Stable
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEigAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Cap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.PairEx
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DerCurve
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc UpperTheory.ConvolutionTheory.R2.Ff
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem vol_lt (N : MeasE E) : N.μ N.D < ⊤ := by
  have hb : Bd (fun _ : GL (Fin 2) (A E) => (1 : ℂ)) :=
    ⟨continuous_const, fun _ _ => rfl, fun _ _ => ⟨1, fun _ _ _ => by simp⟩⟩
  have h := (meanLaws E N _ hb).1 1
  have h' : IntegrableOn (fun _ : G1 E => (1 : ℂ)) N.D N.μ := h
  exact (integrableOn_const_iff (by simp)).1 h' |>.resolve_left (by simp)

private theorem inner_der (N : MeasE E) {Ψ Q : GL (Fin 2) (A E) → ℂ} (hΨ : Bd Ψ) (hQ : Bd Q)
    {g : ℝ → GL (Fin 2) (A E)} (hg : Continuous g)
    (hd : ∀ y s, HasDerivAt (fun u => Ψ (y * g u)) (Q (y * g s)) s) (y : GL (Fin 2) (A E)) (s : ℝ) :
    HasDerivAt (fun u => mean N fun x => Ψ (x * (y * g u))) (mean N fun x => Q (x * (y * g s))) s := by
  obtain ⟨B, hB⟩ := hQ.bdd ((fun u => y * g u) '' Metric.closedBall s 1)
    ((isCompact_closedBall s 1).image (continuous_const.mul hg))
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using vol_lt N⟩
  have hm : ∀ {P : GL (Fin 2) (A E) → ℂ}, Continuous P → ∀ k,
      AEStronglyMeasurable (fun h : G1 E => P (gl h * k)) (N.μ.restrict N.D) := fun hP k =>
    (hP.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := N.μ.restrict N.D)
    (F := fun u h => Ψ (gl h * (y * g u))) (F' := fun u h => Q (gl h * (y * g u)))
    (x₀ := s) (s := Metric.ball s 1) (bound := fun _ => B)
    (Metric.ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun u => hm hΨ.cont _
  · exact (meanLaws E N Ψ hΨ).1 _
  · exact hm hQ.cont _
  · exact ae_of_all _ fun h u hu => hB h _ ⟨u, Metric.ball_subset_closedBall hu, rfl⟩
  · exact integrable_const _
  · refine ae_of_all _ fun h u _ => ?_
    have := hd (gl h * y) u
    simpa only [mul_assoc] using this

private theorem outer_der (N : MeasE E) {Ψ Q : GL (Fin 2) (A E) → ℂ} (hΨ : Bd Ψ) (hQ : Bd Q)
    {g : ℝ → GL (Fin 2) (A E)} (hg : Continuous g) (g0 : g 0 = 1)
    (hd : ∀ y s, HasDerivAt (fun u => Ψ (y * g u)) (Q (y * g s)) s) :
    HasDerivAt (fun s => II N fun x => Ψ (x * g s)) (II N Q) 0 := by
  set Mp : GL (Fin 2) (A E) → ℂ := fun y => mean N fun x => Ψ (x * y) with hMp
  set Mq : GL (Fin 2) (A E) → ℂ := fun y => mean N fun x => Q (x * y) with hMq
  have cp : Continuous Mp := (meanLaws E N Ψ hΨ).2.1
  have cq : Continuous Mq := (meanLaws E N Q hQ).2.1
  have ip : ∀ γ y, Mp (ratGL E 2 γ * y) = Mp y := (meanLaws E N Ψ hΨ).2.2.2
  have iq : ∀ γ y, Mq (ratGL E 2 γ * y) = Mq y := (meanLaws E N Q hQ).2.2.2
  have inv : ∀ (M : GL (Fin 2) (A E) → ℂ), (∀ γ y, M (ratGL E 2 γ * y) = M y) → ∀ k (e : Eˣ) t,
      M (aE (IdeleGroup.diagonal E e * t) * k) = M (aE t * k) := by
    intro M hM k e t
    obtain ⟨γ, hγ⟩ := exists_ratGL_aE (F := E) e
    rw [aE_mul, ← hγ, mul_assoc, hM]
  have hK : IsCompact (Metric.closedBall (0 : ℝ) 1) := isCompact_closedBall 0 1
  set b : (A E)ˣ → ℝ := fun t => sSup ((fun s => ‖Mq (aE t * g s)‖) '' Metric.closedBall (0 : ℝ) 1) with hb
  have cb : Continuous b := IsCompact.continuous_sSup (f := fun t s => ‖Mq (aE t * g s)‖) hK
    (cq.comp ((continuous_aE.comp continuous_fst).mul (hg.comp continuous_snd))).norm
  have ib : ∀ (e : Eˣ) t, b (IdeleGroup.diagonal E e * t) = b t := fun e t => by
    simp only [hb, inv Mq iq]
  obtain ⟨-, ⟨B, hB⟩, -⟩ := uiLaws E (fun t => (b t : ℂ)) (Complex.continuous_ofReal.comp cb)
    (fun e t => by simp only [ib])
  have hbd : ∀ z : IdeleGroup.normOneSubgroup E, ∀ s ∈ Metric.closedBall (0 : ℝ) 1,
      ‖Mq (aE (z : IdeleGroup E) * g s)‖ ≤ B := by
    intro z s hs
    have hab : ab (z : IdeleGroup E) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 z.2)
    have h1 : ‖Mq (aE (z : IdeleGroup E) * g s)‖ ≤ b z :=
      le_csSup (hK.image (cq.comp (continuous_const.mul hg)).norm).bddAbove ⟨s, hs, rfl⟩
    calc _ ≤ b z := h1
      _ ≤ ‖(b z : ℂ)‖ := by rw [Complex.norm_real]; exact le_abs_self _
      _ ≤ B := hB _ hab
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by simpa using normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  have hint : ∀ (M : GL (Fin 2) (A E) → ℂ), Continuous M → (∀ γ y, M (ratGL E 2 γ * y) = M y) → ∀ k,
      IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => M (aE (z : IdeleGroup E) * k))
        (normOneFundamentalDomain E) (normOneMeasure E) := fun M cM iM k =>
    (uiLaws E (fun t => M (aE t * k)) (cM.comp (continuous_aE.mul continuous_const)) (inv M iM k)).1
  have e1 : ∀ s, (II N fun x => Ψ (x * g s)) =
      ∫ z in normOneFundamentalDomain E, Mp (aE (z : IdeleGroup E) * g s) ∂normOneMeasure E := by
    intro s
    simp only [II, UI, hMp, mul_assoc]
  have e2 : II N Q = ∫ z in normOneFundamentalDomain E, Mq (aE (z : IdeleGroup E) * g 0) ∂normOneMeasure E := by
    simp only [II, UI, hMq, g0, mul_one]
  simp only [e1]
  rw [e2]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (μ := (normOneMeasure E).restrict (normOneFundamentalDomain E))
    (F := fun s z => Mp (aE (z : IdeleGroup E) * g s)) (F' := fun s z => Mq (aE (z : IdeleGroup E) * g s))
    (x₀ := 0) (s := Metric.ball (0 : ℝ) 1) (bound := fun _ => B)
    (Metric.ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun s => (hint Mp cp ip (g s)).aestronglyMeasurable
  · exact hint Mp cp ip (g 0)
  · exact (hint Mq cq iq (g 0)).aestronglyMeasurable
  · exact ae_of_all _ fun z s hs => hbd z s (Metric.ball_subset_closedBall hs)
  · exact integrable_const _
  · exact ae_of_all _ fun z s _ => inner_der N hΨ hQ hg hd _ s

variable [_root_.NumberField.IsTotallyComplex E]

private theorem ex_zero' (X : Lie E 2) : ex X 0 = 1 := by
  have h := (exPar E X).1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

private theorem der_curve (Φ : Sm E 2) (X : Lie E 2) (y : GL (Fin 2) (A E)) (s : ℝ) :
    HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X u))) ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s))) s := by
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ (y * infGL E 2 (ex X s)) (ex X) X (ex_zero' X) (exPar E X).2.2.1
  have h2 : HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X s) * infGL E 2 (ex X (u - s))))
      ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s))) s :=
    HasDerivAt.comp_sub_const s s (by simpa using h1)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
  show Φ.1 (y * infGL E 2 (ex X u)) = Φ.1 (y * infGL E 2 (ex X s) * infGL E 2 (ex X (u - s)))
  rw [mul_assoc, ← map_mul, ← (exPar E X).1, add_sub_cancel]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.iiLie :
    IILie := by
  intro E _ _ _ N Φ φ X h0 hP h1 h2
  have hg : Continuous fun s => infGL E 2 (ex X s) :=
    (GlobalTheory.CompanionTheory.LieSkew.continuous_infGL_map E 2).comp (exPar E X).2.1
  have g0 : infGL E 2 (ex X 0) = 1 := by rw [ex_zero', map_one]
  have hQ : Bd fun x => (act (.lie X) Φ).1 x * φ.1 x + (1 : ℂ) * (Φ.1 x * (act (.lie X) φ).1 x) := by
    refine ⟨h1.cont.add (continuous_const.mul h2.cont), fun γ g => ?_, fun C hC => ?_⟩
    · exact congrArg₂ (fun p q => p + (1 : ℂ) * q) (h1.left γ g) (h2.left γ g)
    · obtain ⟨B₁, hB₁⟩ := h1.bdd C hC
      obtain ⟨B₂, hB₂⟩ := h2.bdd C hC
      refine ⟨B₁ + B₂, fun h k hk => ?_⟩
      have a := hB₁ h k hk
      have b := hB₂ h k hk
      rw [one_mul]
      exact (norm_add_le _ _).trans (add_le_add a b)
  have hd : ∀ y s, HasDerivAt (fun u => Φ.1 (y * infGL E 2 (ex X u)) * φ.1 (y * infGL E 2 (ex X u)))
      ((act (.lie X) Φ).1 (y * infGL E 2 (ex X s)) * φ.1 (y * infGL E 2 (ex X s)) +
        (1 : ℂ) * (Φ.1 (y * infGL E 2 (ex X s)) * (act (.lie X) φ).1 (y * infGL E 2 (ex X s)))) s := by
    intro y s
    rw [one_mul]
    exact (der_curve Φ X y s).mul (der_curve φ X y s)
  have hD := outer_der N h0 hQ hg g0 hd
  have hc : (fun s => II N fun x => Φ.1 (x * infGL E 2 (ex X s)) * φ.1 (x * infGL E 2 (ex X s))) =
      fun _ => II N fun x => Φ.1 x * φ.1 x :=
    funext fun s => (iiLaws E N _ h0).2 hP (infGL E 2 (ex X s))
  rw [hc] at hD
  have hz := hD.unique (hasDerivAt_const (0 : ℝ) _)
  rw [(iiLaws E N _ h1).1 _ h2 1, one_mul] at hz
  exact hz
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefZero
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent
open GroundTheory.Automorphic.FourierWhittaker

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.VanishingCoefficients

variable {E : Type} [Field E] [NumberField E]

private theorem vn (q : A E) : (nU q).val = !![1, q; 0, 1] := rfl

private theorem n_add (x y : A E) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem n_zero : gl (nU (0 : A E)) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem cont_n : Continuous fun q : A E => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

private theorem rat_n (k : E) : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap E (A E) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem rat_w : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = gl (wW E) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap E (A E) (!![0, 1; -1, 0] i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (A E)) i j
  fin_cases i <;> fin_cases j <;> simp

private theorem ψ_add (x y : A ℚ) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

private theorem ψ_rt (k : ℚ) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

private theorem n_aE (t : (A E)ˣ) (y : A E) : gl (nU ((t : A E) * y)) * aE t = aE t * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, aE, Matrix.mul_apply, Fin.sum_univ_two]

private def Fh (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) (x : Fin 2 → A ℚ) : ℂ :=
  Φ (gl (nU (D.mkE (x 0) (x 1))) * h)

private theorem cont_Fh (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ) (h : GL (Fin 2) (A E)) :
    Continuous (Fh D Φ h) :=
  hΦ.comp ((cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))).mul continuous_const)

private theorem per_Fh (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, Fh D Φ h (l + x) = Fh D Φ h x := by
  intro l hl x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hl
  obtain ⟨γ, hγ⟩ := rat_n (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ)
  simp only [Fh, Pi.add_apply]
  rw [D.mkE_add, n_add]
  change Φ (gl (nU (D.mkE (rt (η 0)) (rt (η 1)))) * gl (nU (D.mkE (x 0) (x 1))) * h) = _
  rw [D.mkE_rt, ← hγ, mul_assoc, hL]

private theorem lin_ne (D : Dat ℚ E) {a b : ℚ} (h : a ≠ 0 ∨ b ≠ 0) : algebraMap ℚ E a + algebraMap ℚ E b * D.θ ≠ 0 := by
  intro h0
  have h1 : algebraMap ℚ E a - algebraMap ℚ E b * D.θ = 0 := by
    have e := congrArg D.σ h0
    simpa [D.conj, sub_eq_add_neg] using e
  have ha : algebraMap ℚ E a = 0 := by linear_combination (h0 + h1) / 2
  have hb : algebraMap ℚ E b * D.θ = 0 := by linear_combination (h0 - h1) / 2
  have inj := (algebraMap ℚ E).injective
  rcases h with h | h
  · exact h (inj (by rw [ha, map_zero]))
  · refine h (inj ?_)
    rw [map_zero]
    exact (mul_eq_zero.1 hb).resolve_right D.θ_ne_zero

private theorem norm_ne (D : Dat ℚ E) {a b : ℚ} (h : a ≠ 0 ∨ b ≠ 0) : a * a - D.δ * b * b ≠ 0 := by
  intro h0
  have e : (algebraMap ℚ E a + algebraMap ℚ E b * D.θ) * (algebraMap ℚ E a + algebraMap ℚ E (-b) * D.θ) =
      algebraMap ℚ E (a * a - D.δ * b * b) := by
    have hs := D.sq
    simp only [map_sub, map_mul, map_neg]
    linear_combination (-(algebraMap ℚ E b) ^ 2) * hs
  rw [h0, map_zero] at e
  exact mul_ne_zero (lin_ne D h) (lin_ne D (a := a) (b := -b) (by simpa using h)) e

private theorem mat0 (a b d : ℚ) (x : Fin 2 → A ℚ) :
    matVec !![a, d; b, a] x 0 = UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt d * x 1 := by
  rw [matVec_apply, Fin.sum_univ_two]; rfl

private theorem mat1 (a b d : ℚ) (x : Fin 2 → A ℚ) :
    matVec !![a, d; b, a] x 1 = UpperTheory.ConvolutionTheory.R2.rt b * x 0 + UpperTheory.ConvolutionTheory.R2.rt a * x 1 := by
  rw [matVec_apply, Fin.sum_univ_two]; rfl

private def Gh (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) (u : Fin 2 → A ℚ) : ℂ :=
  Fh D Φ h u * ψ (2 * u 0)

private theorem int_Gh (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) :
    ∫ x in vecDomain ℚ (Fin 2), Gh D Φ h x ∂vecMeasure ℚ (Fin 2) = WE D Φ h := rfl

private theorem per_Gh (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, Gh D Φ h (l + x) = Gh D Φ h x := by
  intro l hl x
  have e1 := per_Fh D hL h l hl x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hl
  have e2 : (2 : A ℚ) * ((fun i => algebraMap ℚ (A ℚ) (η i)) + x) 0 = UpperTheory.ConvolutionTheory.R2.rt (2 * η 0) + 2 * x 0 := by
    simp only [UpperTheory.ConvolutionTheory.R2.rt, map_mul, map_ofNat, mul_add, Pi.add_apply]
  simp only [Gh]
  rw [e1, e2, ψ_add, ψ_rt, one_mul]

private theorem pt_id (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) (a b : ℚ) (t : (A E)ˣ) (ht : (t : A E) = D.mkE (UpperTheory.ConvolutionTheory.R2.rt a) (UpperTheory.ConvolutionTheory.R2.rt b))
    (hγ : ∃ γ, ratGL E 2 γ = aE t) (x : Fin 2 → A ℚ) :
    Gh D Φ (aE t * h) (matVec !![a, D.δ * b; b, a] x) = Fh D Φ h x * ψ (2 * (UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) * x 1)) := by
  obtain ⟨γ, hγ⟩ := hγ
  have e : UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) = UpperTheory.ConvolutionTheory.R2.rt D.δ * UpperTheory.ConvolutionTheory.R2.rt b := map_mul _ _ _
  have k1 : D.mkE (matVec !![a, D.δ * b; b, a] x 0) (matVec !![a, D.δ * b; b, a] x 1) =
      (t : A E) * D.mkE (x 0) (x 1) := by
    rw [ht, D.mkE_mul, mat0, mat1, e]
    congr 1
    · ring
    · ring
  simp only [Gh, Fh]
  rw [k1, mat0, ← mul_assoc, n_aE, ← hγ, mul_assoc, hL]

private theorem coef_zero (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (hW : ∀ h, WE D Φ h = 0) (h : GL (Fin 2) (A E)) (ξ : Fin 2 → ℚ) (hξ : ξ ≠ 0) :
    vecCoeff (Fh D Φ h) ξ = 0 := by
  have hδ := D.δ_ne_zero
  obtain ⟨a, ha⟩ : ∃ a : ℚ, 2 * a = -ξ 0 := ⟨-ξ 0 / 2, by ring⟩
  obtain ⟨b, hb⟩ : ∃ b : ℚ, 2 * (D.δ * b) = -ξ 1 := ⟨-ξ 1 / (2 * D.δ), by field_simp⟩
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    refine hξ (funext fun i => ?_)
    fin_cases i
    · simpa [h1] using ha.symm
    · simpa [h2] using hb.symm
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin 2) ℚ, (M : Matrix (Fin 2) (Fin 2) ℚ) = !![a, D.δ * b; b, a] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, D.δ * b; b, a]
      (by rw [Matrix.det_fin_two_of]; exact norm_ne D hab), rfl⟩
  obtain ⟨t, ht, hγ⟩ : ∃ t : (A E)ˣ, (t : A E) = D.mkE (UpperTheory.ConvolutionTheory.R2.rt a) (UpperTheory.ConvolutionTheory.R2.rt b) ∧ ∃ γ, ratGL E 2 γ = aE t :=
    ⟨IdeleGroup.diagonal E (Units.mk0 _ (lin_ne D hab)), (D.mkE_rt a b).symm, exists_ratGL_aE _⟩
  have h1 := setIntegral_comp_matVec M (per_Gh D hL (aE t * h))
  rw [int_Gh, hW, hM] at h1
  rw [vecCoeff, ← h1]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have k2 : (2 : A ℚ) * (UpperTheory.ConvolutionTheory.R2.rt a * x 0 + UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) * x 1) = -pair ξ x := by
    have e2 : (2 : A ℚ) = UpperTheory.ConvolutionTheory.R2.rt (2 : ℚ) := (map_ofNat _ 2).symm
    have e0 : (2 : A ℚ) * UpperTheory.ConvolutionTheory.R2.rt a = -UpperTheory.ConvolutionTheory.R2.rt (ξ 0) := by
      rw [← map_neg, ← ha, e2]; exact (map_mul _ _ _).symm
    have e1 : (2 : A ℚ) * UpperTheory.ConvolutionTheory.R2.rt (D.δ * b) = -UpperTheory.ConvolutionTheory.R2.rt (ξ 1) := by
      rw [← map_neg, ← hb, e2]; exact (map_mul _ _ _).symm
    rw [pair, Fin.sum_univ_two]
    linear_combination (x 0) * e0 + (x 1) * e1
  beta_reduce
  rw [pt_id D hL h a b t ht hγ x, k2]
  rfl

private theorem n_inv (D : Dat ℚ E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ)
    (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) (hW : ∀ h, WE D Φ h = 0) (b : A E) (h : GL (Fin 2) (A E)) :
    Φ (gl (nU b) * h) = Φ h := by
  obtain ⟨u, v, rfl⟩ := D.exists_mkE b
  set F := Fh D Φ h with hF
  have hFc : Continuous F := cont_Fh D hΦ h
  have hFper : ∀ l ∈ vecLattice ℚ (Fin 2), ∀ x, F (l + x) = F x := per_Fh D hL h
  set a : Fin 2 → A ℚ := ![u, v] with ha
  have hTper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ x, F (ξ + x + a) = F (x + a) := fun ξ hξ x => by
    rw [add_assoc, hFper ξ hξ]
  set G : (Fin 2 → A ℚ) → ℂ := fun y => F (y + a) - F y with hG
  have hGc : Continuous G := (hFc.comp (continuous_id.add continuous_const)).sub hFc
  have hGper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x := fun ξ hξ x => by
    simp only [hG]
    rw [hTper ξ hξ, hFper ξ hξ]
  have hint : ∀ (f : (Fin 2 → A ℚ) → ℂ), Continuous f → ∀ ξ : Fin 2 → ℚ,
      IntegrableOn (fun x => f x * (adelicChar ℚ (-pair ξ x) : ℂ)) (vecDomain ℚ (Fin 2))
        (vecMeasure ℚ (Fin 2)) := fun f hf ξ =>
    ((hf.mul (continuous_adelicChar_neg_pair ξ)).continuousOn.integrableOn_compact
      isCompact_closure_vecDomain).mono_set subset_closure
  have hcoef : ∀ ξ, vecCoeff G ξ = 0 := by
    intro ξ
    have e1 : vecCoeff G ξ = vecCoeff (fun x => F (x + a)) ξ - vecCoeff F ξ := by
      unfold vecCoeff
      refine Eq.trans ?_ (integral_sub (hint _ (hFc.comp (continuous_id.add continuous_const) :
        Continuous fun x => F (x + a)) ξ) (hint _ hFc ξ))
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (F (x + a) - F x) * _ = F (x + a) * _ - F x * _
      ring
    rw [e1, vecCoeff_translate hFper]
    by_cases h1 : ξ = 0
    · have hp : pair ξ a = 0 := by
        simp [pair, h1]
      rw [hp, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, sub_self]
    · rw [coef_zero D hL hW h ξ h1, mul_zero, sub_zero]
  have hG0 := congrFun (GlobalTheory.CompanionTheory.AdelicFourier.eq_zero_of_vecCoeff_eq_zero hGc hGper hcoef) 0
  have h1 : F (0 + a) = F 0 := sub_eq_zero.1 hG0
  have e2 : F (0 + a) = Φ (gl (nU (D.mkE u v)) * h) := by
    simp [hF, Fh, ha]
  have e3 : F 0 = Φ h := by
    simp only [hF, Fh, Pi.zero_apply]
    rw [D.mkE_zero, n_zero, one_mul]
  rw [← e2, h1, e3]

end UpperTheory.ConvolutionTheory.RankTwoDescent.VanishingCoefficients

end

open UpperTheory.ConvolutionTheory.RankTwoDescent.VanishingCoefficients in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.killW :
    KillW := by
  intro E _ _ D Φ hΦ hL hW h g
  have gm : ∀ x y : G1 E, gl (x * y) = gl x * gl y := fun _ _ => Units.ext rfl
  have g1 : gl (1 : G1 E) = 1 := Units.ext rfl
  let H : Subgroup (G1 E) :=
    { carrier := {s | ∀ g, Φ (gl s * g) = Φ g}
      mul_mem' := fun {x y} hx hy g => by
        rw [gm, mul_assoc, hx, hy]
      one_mem' := fun g => by rw [g1, one_mul]
      inv_mem' := fun {x} hx g => by
        rw [← hx (gl x⁻¹ * g), ← mul_assoc, ← gm, mul_inv_cancel, g1, one_mul] }
  have hH : H = ⊤ := eq_top_of_nU_wW H (fun b g => n_inv D hΦ hL hW b g) (fun g => by
    obtain ⟨γ, hγ⟩ := rat_w (E := E)
    rw [← hγ, hL])
  have : h ∈ H := hH ▸ Subgroup.mem_top h
  exact this g
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem bd_zero : Bd (fun _ : GL (Fin 2) (A E) => (0 : ℂ)) :=
  ⟨continuous_const, fun _ _ => rfl, fun _ _ => ⟨0, fun _ _ _ => by simp⟩⟩

private theorem ii_zero (N : MeasE E) : II N (fun _ => 0) = 0 := by
  simp [II, UI, mean]

private theorem ii_add (N : MeasE E) {Ψ Ψ' : GL (Fin 2) (A E) → ℂ} (h : Bd Ψ) (h' : Bd Ψ') :
    (II N fun x => Ψ x + Ψ' x) = II N Ψ + II N Ψ' := by
  simpa using (iiLaws E N Ψ h).1 Ψ' h' 1

private theorem ii_smul (N : MeasE E) {Ψ : GL (Fin 2) (A E) → ℂ} (h : Bd Ψ) (c : ℂ) :
    (II N fun x => c * Ψ x) = c * II N Ψ := by
  simpa [ii_zero] using (iiLaws E N _ bd_zero).1 Ψ h c

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.pairEx :
    PairEx := by
  intro E _ _ _ D W M N P hn π hπ
  have hb : ∀ (x : span W M π) (y : P.V), Bd fun g => x.1.1 g * y.1.1 g :=
    fun x y => (prodBd E D W M N P π x.1 x.2 y.1 y.2).1
  have hc : ∀ (x : span W M π) (y : P.V), PosC fun g => x.1.1 g * y.1.1 g :=
    fun x y => (prodBd E D W M N P π x.1 x.2 y.1 y.2).2 hπ hn
  have st : IsStable (span W M π) := UpperTheory.ConvolutionTheory.R2.stable ℚ E D W M π
  let B : span W M π →ₗ[ℂ] P.V →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x y => II N fun g => x.1.1 g * y.1.1 g)
    (fun x x' y => (congrArg (II N) (funext fun g => add_mul (x.1.1 g) (x'.1.1 g) (y.1.1 g))).trans
      (ii_add N (hb x y) (hb x' y)))
    (fun c x y => (congrArg (II N) (funext fun g => mul_assoc c (x.1.1 g) (y.1.1 g))).trans
      (ii_smul N (hb x y) c))
    (fun x y y' => (congrArg (II N) (funext fun g => mul_add (x.1.1 g) (y.1.1 g) (y'.1.1 g))).trans
      (ii_add N (hb x y) (hb x y')))
    (fun c x y => (congrArg (II N) (funext fun g => mul_left_comm (x.1.1 g) c (y.1.1 g))).trans
      (ii_smul N (hb x y) c))
  have hB : ∀ x y, B x y = II N fun g => x.1.1 g * y.1.1 g := fun _ _ => rfl
  refine ⟨B, ⟨st, P.stable, fun k x y => ?_, fun k x y => ?_, fun X x y => ?_⟩, hB, fun x hx => ?_⟩
  · exact (iiLaws E N _ (hb x y)).2 (hc x y) (finGL E 2 k)
  · exact (iiLaws E N _ (hb x y)).2 (hc x y) (infGL E 2 (Unitary.toUnits k))
  · exact iiLie E N x.1 y.1 X (hb x y) (hc x y) (hb ⟨_, st (.lie X) _ x.2⟩ y) (hb x ⟨_, P.stable (.lie X) _ y.2⟩)
  · refine LinearMap.ext fun y => ?_
    have hcx := UpperTheory.ConvolutionTheory.R2.H.spanCont ℚ E D W M π x.1 x.2
    have hk := killW E D x.1.1 hcx.1 hcx.2 hx
    have h0 : ∀ t : (A E)ˣ, (mean N fun g => x.1.1 (g * aE t) * y.1.1 (g * aE t)) = 0 := by
      intro t
      have e : ∫ h in N.D, y.1.1 (gl h * aE t) ∂N.μ = 0 := meanZero decE E D W M N P y.1 y.2 (aE t)
      show ∫ h in N.D, x.1.1 (gl h * aE t) * y.1.1 (gl h * aE t) ∂N.μ = 0
      simp only [hk]
      rw [integral_const_mul, e, mul_zero]
    show (II N fun g => x.1.1 g * y.1.1 g) = 0
    simp [II, UI, h0]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SatPair
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

section General

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G V} {ρ : Representation ℂ G W} {K : Subgroup G} {h : G → ℂ} {x : V} {y : W}

private theorem pair_heckeVec (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed σ K)
    (hy : y ∈ fixed ρ K) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (θ : G ≃* G) (hθ : ∀ k, k ∈ K ↔ θ k ∈ K)
    (hi : ∀ g v w, β (σ (θ g) v) (ρ g w) = β v w)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t⁻¹ = t ∧ g = a * t * b) :
    β (heckeVec σ K h x) y = β x (heckeVec ρ K h y) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have hg := GlobalTheory.LGrp.mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y := fun a ha b hb t => by
    obtain ⟨a, rfl⟩ := θ.surjective a
    rw [map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)
  have inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y) := fun t => by
    rw [← hi t⁻¹ x (ρ t y)]; simp
  have e1 := (β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh σ x)
  have e2 := (β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]

private theorem exists_fixed_pair [TopologicalSpace G] [IsTopologicalGroup G] (hρ : IsSmooth ρ)
    (hK : IsCompact (K : Set G)) (l : W →ₗ[ℂ] ℂ) (hl : ∀ k ∈ K, ∀ v, l (ρ k v) = l v) (y : W) :
    ∃ y' ∈ fixed ρ K, l y' = l y := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex := by
    have ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K) := (hρ y).preimage continuous_subtype_val
    haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨GlobalTheory.OrbitAvg.avg ρ K y,
    GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩
  haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)
  have hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y := fun q => hl _ q.out.2 y
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]

end General


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.ConjPlace in
private theorem sat_eq_of_eig {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (hσ : IsSmooth σ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n g) x) (ρ g y) = β x y)
    {Y : W} {C C' : Multiset ℂˣ} (hY : IsSatVecGL w ρ Y C') {x₀ : V} (hx₀ : β x₀ Y ≠ 0)
    (hE : ∀ x ∈ fixed σ (KGL w (n := n)), C.card = n ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n,
      β (heckeVec σ (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) x) Y = satEig (qV E w) n C j * β x Y) : C = C' := by
  classical
  have hKc : IsCompact (KGL w (n := n) : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  have hfY := GlobalTheory.LGrp.mem_fixed.1 hY.2.1
  obtain ⟨x, hxK, hx⟩ := exists_fixed_pair hσ hKc (β.flip Y) (fun k hk v => by
    obtain ⟨k', rfl⟩ := (GlobalTheory.LFun.ConjPlace.invT c n).surjective k
    have := hi k' v Y
    rwa [hfY _ ((hK k').2 hk)] at this) x₀
  have hne : β x Y ≠ 0 := fun h0 => hx₀ (hx.symm.trans h0)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  obtain ⟨hcard, hE'⟩ := hE x hxK
  refine eq_of_satEig_eq (qV_ne_zero w) hcard hY.2.2.1 fun j hj => ?_
  have key := pair_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hp j) hxK hY.2.1 β
    (GlobalTheory.LFun.ConjPlace.invT c n) hK hi
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, invT_dGL c ϖ j, e⟩)
  rw [hE' _ hp j hj, hY.2.2.2 _ hp j hj, map_smul, smul_eq_mul] at key
  exact mul_right_cancel₀ hne key

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.satPair :
    SatPair := by
  intro E _ _ _ V Q B hB hne w T hsm heq hker C C' hC hQ
  classical
  let σ : Representation ℂ (GL (Fin 2) (Kv w)) V :=
    (GlobalTheory.PRep.sub (finRep E 2) V fun k => hB.st (.fin k)).comp (locGL E 2 w)
  have hsmooth : GlobalTheory.PRep.IsSmooth σ := by
    intro x
    let S : Subgroup (GL (Fin 2) (Kv w)) :=
      { carrier := {g | σ g x = x}
        mul_mem' := fun {a b} ha hb => by
          change σ (a * b) x = x
          rw [map_mul, Module.End.mul_apply, show σ b x = x from hb]; exact ha
        one_mem' := by change σ 1 x = x; rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change σ a⁻¹ x = x
          conv_lhs => rw [← show σ a x = x from ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    refine Subgroup.isOpen_of_mem_nhds S (g := 1) ?_
    filter_upwards [hsm x] with y hy
    exact Subtype.ext (Subtype.ext (funext fun g => hy g))
  have hker0 : ∀ y : Q.V, (∀ x, B x y = 0) → y = 0 := by
    have hst : _root_.GlobalTheory.CuspRep.IsStable ((LinearMap.ker B.flip).map Q.V.subtype) := by
      rintro o _ ⟨y, hy, rfl⟩
      have hy' : ∀ x, B x y = 0 := fun x => LinearMap.congr_fun (LinearMap.mem_ker.1 hy) x
      refine ⟨Q.op o y, LinearMap.mem_ker.2 (LinearMap.ext fun x => ?_), rfl⟩
      change B x (Q.op o y) = 0
      cases o with
      | fin k =>
        let x' : V := ⟨act (.fin k⁻¹) x.1, hB.st _ _ x.2⟩
        have e : (⟨act (.fin k) x'.1, hB.st _ _ x'.2⟩ : V) = x := Subtype.ext (by
          change finRep E 2 k (finRep E 2 k⁻¹ x.1) = x.1
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
        exact (congrArg (fun u => B u (Q.op (.fin k) y)) e).symm.trans ((hB.fin k x' y).trans (hy' x'))
      | cpt k =>
        let x' : V := ⟨act (.cpt k⁻¹) x.1, hB.st _ _ x.2⟩
        have e : (⟨act (.cpt k) x'.1, hB.st _ _ x'.2⟩ : V) = x := Subtype.ext (by
          change cptRep E 2 k (cptRep E 2 k⁻¹ x.1) = x.1
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
        exact (congrArg (fun u => B u (Q.op (.cpt k) y)) e).symm.trans ((hB.cpt k x' y).trans (hy' x'))
      | lie X =>
        have h := hB.lie X x y
        rw [hy' _, zero_add] at h
        exact h
    intro y hy
    rcases Q.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · have hm : y.1 ∈ (LinearMap.ker B.flip).map Q.V.subtype :=
        ⟨y, LinearMap.mem_ker.2 (LinearMap.ext hy), rfl⟩
      rw [h] at hm
      exact Subtype.ext ((Submodule.mem_bot _).1 hm)
    · exfalso
      refine hne (LinearMap.ext fun x => LinearMap.ext fun z => ?_)
      have hz : z.1 ∈ (LinearMap.ker B.flip).map Q.V.subtype := by rw [h]; exact z.2
      obtain ⟨u, hu, e⟩ := hz
      have e' : u = z := Subtype.ext e
      subst e'
      exact LinearMap.congr_fun (LinearMap.mem_ker.1 hu) x
  have hD := TC.hasSatGL_dual ((CG.hasSat_mk Q w C').1 hQ)
  obtain ⟨Y, hY⟩ := hD.exists_vec
  let β : V →ₗ[ℂ] (TC.dual Q).V →ₗ[ℂ] ℂ := B.compl₂ (TC.toDual Q).symm.toLinearMap
  have hβ : ∀ x y, β x (TC.toDual Q y) = B x y := fun x y => by simp [β]
  have hβ' : ∀ x, β x Y = B x ((TC.toDual Q).symm Y) := fun _ => rfl
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, β x₀ Y ≠ 0 := by
    by_contra hn
    push_neg at hn
    refine hY.1 ?_
    have h0 := hker0 ((TC.toDual Q).symm Y) hn
    have h1 := congrArg (TC.toDual Q) h0
    simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] using h1
  have hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) 2 g) x) ((TC.dual Q).locRep w g y) = β x y := by
    intro g x y
    obtain ⟨y, rfl⟩ := (TC.toDual Q).surjective y
    rw [TC.locRep_toDual, hβ, hβ]
    have e := hB.fin (locGL E 2 w (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) 2 g)) x y
    refine Eq.trans ?_ e
    refine congrArg (B _) ?_
    rw [CuspSub.locRep_eq]
    refine Subtype.ext ?_
    change act (.fin _) y.1 = act (.fin _) y.1
    refine congrArg (fun k => act (.fin (locGL E 2 w k)) y.1) (Units.ext (Matrix.ext fun i j => ?_))
    rw [GlobalTheory.LFun.ConjPlace.invT_val]
    rfl
  have hfin := sat_eq_of_eig (n := 2) hsmooth β hi hY hx₀ (fun x hx => by
    have hfix : Fix w x.1.1 := fun g k hk => congrArg (fun u : V => u.1.1 g) (GlobalTheory.LGrp.mem_fixed.1 hx k hk)
    refine ⟨(hC x hfix 1).card, fun ϖ hϖ j hj => ?_⟩
    have hTz : ∀ g, T (GlobalTheory.LFun.heckeVec σ (GlobalTheory.LFun.KGL w (n := 2)) (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j) x) g =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 C j * T x g := by
      intro g
      let L : V →+ ℂ := (Pi.evalAddMonoidHom _ g).comp T.toAddMonoidHom
      have e1 := L.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w 2) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) σ x)
      have e2 := (hC x hfix g).eig ϖ hϖ j hj 1
      refine e1.trans (Eq.trans (finsum_congr fun c => ?_) (e2.trans ?_))
      · change T (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out • σ c.out x) g = _
        rw [map_smul, Pi.smul_apply, smul_eq_mul, heq x (σ c.out x) c.out (fun _ => rfl) g, one_mul]
        rfl
      · simp
    have hz : T (GlobalTheory.LFun.heckeVec σ (GlobalTheory.LFun.KGL w (n := 2)) (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j) x -
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 C j • x) = 0 := by
      funext g
      simp [map_sub, hTz]
    have h2 := LinearMap.congr_fun (hker _ hz) ((TC.toDual Q).symm Y)
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply, sub_eq_zero, smul_eq_mul] at h2
    exact h2)
  rw [hfin, Multiset.map_map]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfPair
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem neg_of_prod_eq {m m' : Multiset ℂ} (hc : m.card = 2) (hc' : m'.card = 2)
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (-u + ·)).prod) : m' = m.map Neg.neg := by
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 hc
  obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.1 hc'
  have key : ∀ u : ℂ, (u + a) * (u + b) = (-u + c) * (-u + d) := fun u => by
    simpa [Multiset.insert_eq_cons] using h u
  have h0 := key 0
  have h1 := key 1
  have hs : a + b = -(c + d) := by linear_combination h1 - h0
  have hz : (c + a) * (c + b) = 0 := by
    have := key c
    simpa using this
  rcases mul_eq_zero.1 hz with e | e
  · have e1 : c = -a := by linear_combination e
    have e2 : d = -b := by linear_combination hs - e
    simp [e1, e2, Multiset.insert_eq_cons]
  · have e1 : c = -b := by linear_combination e
    have e2 : d = -a := by linear_combination hs - e
    simp only [e1, e2, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    exact Multiset.cons_swap _ _ _

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.infPair :
    InfPair := by
  intro E _ _ _ V Q B hB hne τ m m' hc hm hm'
  obtain ⟨x, y, hxy⟩ : ∃ x y, B x y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (LinearMap.ext fun x => LinearMap.ext fun y => hcon x y)
  let S := GlobalTheory.CapPair.adjPairs V Q.V B
  have h1 : ∀ i j z, (GlobalTheory.CuspRep.lieS E 2 i j (GlobalTheory.CuspRep.atEmb τ z),
      -MulOpposite.op (GlobalTheory.CuspRep.lieS E 2 i j (GlobalTheory.CuspRep.atEmb τ z))) ∈ S := by
    intro i j z φ ψ
    have h := hB.lie (toL (Matrix.single i j (GlobalTheory.CuspRep.atEmb τ z))) φ ψ
    rw [add_eq_zero_iff_eq_neg, ← map_neg] at h
    exact ⟨hB.st (.lie _) _ φ.2, neg_mem (hB.st' (.lie _) _ ψ.2), h⟩
  have h2 : ∀ i j, (GlobalTheory.CuspRep.Eop (a := 2) τ i j, -MulOpposite.op (GlobalTheory.CuspRep.Eop (a := 2) τ i j)) ∈ S := fun i j => by
    convert S.smul_mem (S.sub_mem (h1 i j 1) (S.smul_mem (h1 i j Complex.I) Complex.I)) (1 / 2) using 1
    refine Prod.ext rfl ?_
    simp only [GlobalTheory.CuspRep.Eop, MulOpposite.op_smul, MulOpposite.op_sub, Prod.smul_snd, Prod.snd_sub]
    module
  have h3 : ∀ w, Formalism.REAL.qdet (fun i j => (GlobalTheory.CuspRep.Eop (a := 2) τ i j, -MulOpposite.op (GlobalTheory.CuspRep.Eop (a := 2) τ i j))) w ∈ S := fun w => by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (h2 _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  have h4 : ∀ u, (GlobalTheory.CuspRep.cap (a := 2) τ u, MulOpposite.op ((-1 : ℂ) ^ 2 • GlobalTheory.CuspRep.cap (a := 2) τ (-u) : Module.End ℂ (Sm E 2))) ∈ S := fun u => by
    convert h3 (u + (((2 : ℕ) : ℂ) - 1) / 2) using 1
    rw [GlobalTheory.CapPair.qdet_prod, GlobalTheory.CapPair.qdet_antipode (A := Module.End ℂ (Sm E 2)) (GlobalTheory.CuspRep.glRel_Eop (a := 2) τ),
      show ((2 : ℕ) : ℂ) - 1 - (u + (((2 : ℕ) : ℂ) - 1) / 2) = -u + (((2 : ℕ) : ℂ) - 1) / 2 by ring]
    rfl
  refine neg_of_prod_eq hc hm'.1 fun u => ?_
  obtain ⟨h, h', e'⟩ := h4 u x y
  have e1 : (⟨_, h⟩ : V) = (m.map (u + ·)).prod • x := Subtype.ext (hm u _ x.2)
  have e3 : (⟨_, h'⟩ : Q.V) = (m'.map (-u + ·)).prod • y := Subtype.ext (by
    change (-1 : ℂ) ^ 2 • GlobalTheory.CuspRep.cap (a := 2) τ (-u) y.1 = _ • y.1
    rw [hm'.2 _ _ y.2]
    simp)
  have e4 : B ((m.map (u + ·)).prod • x) y = B x ((m'.map (-u + ·)).prod • y) := by
    rw [← e1, ← e3]
    exact e'
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at e4
  exact mul_right_cancel₀ hxy e4
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem sat_below (π : TR.CuspSub ℚ 2) {E : Type} [Field E] [NumberField E] :
    ∀ᶠ w : P E in cofinite, ∀ v : P ℚ, Below v w → ∃ B, π.HasSat v B := by
  have h1 := UpperTheory.V.Af.Gk.satAE ℚ 2 π
  rw [Filter.eventually_cofinite] at h1 ⊢
  refine (h1.biUnion (t := fun v => {w : P E | Below v w}) fun v _ => ?_).subset fun w hw => ?_
  · have := v.isMaximal
    refine Set.Finite.of_finite_image (f := fun w => w.asIdeal) ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_)
      fun _ _ _ _ e => HeightOneSpectrum.ext e
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, ⟨hw⟩⟩
  · simp only [Set.mem_setOf_eq, not_forall] at hw
    obtain ⟨v, hv, hn⟩ := hw
    exact Set.mem_biUnion (show v ∈ {v | ¬ ∃ B, π.HasSat v B} from hn) hv

private theorem span_level {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D) (M : Meas ℚ)
    (π : TR.CuspSub ℚ 2) (w : P E) (Φ : Sm E 2) (hΦ : Φ ∈ span W M π) :
    ∀ᶠ y in 𝓝 (1 : GL (Fin 2) (Kv w)), ∀ g, Φ.1 (g * lc w y) = Φ.1 g := by
  induction hΦ using Submodule.span_induction with
  | mem Ψ h =>
    obtain ⟨f, hf, φ, hφ, e⟩ := h
    have hO := UpperTheory.ConvolutionTheory.R2.Ff.level ℚ E D W M π f hf φ hφ Ψ e
    have hc : Continuous (locGL E 2 w) := GlobalTheory.CuspRep.CuspSub.continuous_locGL w
    have hm : {k | GlobalTheory.CuspRep.finRep E 2 k Ψ = Ψ} ∈ 𝓝 (locGL E 2 w 1) := hO.mem_nhds (by simp)
    filter_upwards [hc.continuousAt.eventually hm] with y hy g
    exact congrFun (congrArg Subtype.val hy) g
  | zero => exact Filter.Eventually.of_forall fun _ _ => rfl
  | add x y _ _ ix iy =>
    filter_upwards [ix, iy] with z h1 h2 g
    exact congrArg₂ (· + ·) (h1 g) (h2 g)
  | smul c x _ ix =>
    filter_upwards [ix] with z h1 g
    exact congrArg (c • ·) (h1 g)

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.finS :
    FinS := by
  intro E _ _ _ D W M N Q hn π hπ ⟨f, hf, ph, hph, φ, hφ, hne⟩
  obtain ⟨B, hI, hB, hK⟩ := pairEx E D W M N Q hn π hπ
  obtain ⟨Φ, hΦ⟩ := UpperTheory.ConvolutionTheory.R2.smooth ℚ E D W M π f hf ph hph
  have hmem : Φ ∈ span W M π := Submodule.subset_span ⟨f, hf, ph, hph, hΦ⟩
  have hB0 : B ≠ 0 := by
    intro h0
    apply hne
    have h1 := hB ⟨Φ, hmem⟩ ⟨φ, hφ⟩
    rw [h0] at h1
    rw [← hΦ]
    exact h1.symm
  have hc : ∀ x : span W M π, Continuous x.1.1 := fun x => (UpperTheory.ConvolutionTheory.R2.H.spanCont ℚ E D W M π x.1 x.2).1
  let T : span W M π →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ) :=
    { toFun := fun x => WE D x.1.1
      map_add' := fun x y => by
        funext h
        have e := (UpperTheory.ConvolutionTheory.R2.H.weEig ℚ E D x.1.1 (hc x)).2.2 y.1.1 1 (hc y) h
        simpa using e
      map_smul' := fun c x => by
        funext h
        have e := (UpperTheory.ConvolutionTheory.R2.H.weEig ℚ E D 0 continuous_const).2.2 x.1.1 c (hc x) h
        simpa [WE] using e }
  have hsat : ∀ (w : P E) (v : P ℚ), SplitAt v w → ∀ C C', π.HasSat v C → (CG.mk Q).HasSat w C' → C' = C.map (·⁻¹) := by
    intro w v hsp C C' hC hC'
    refine satPair E (span W M π) Q B hI hB0 w T (fun x => span_level W M π w x.1 x.2) (fun x x' y h g => ?_)
      (fun x hx => hK x fun h => congrFun hx h) C C' (fun x hx => splitEig E D W M N Q π x.1 x.2 v w hsp C hC hx) hC'
    show WE D x'.1.1 g = WE D x.1.1 (g * lc w y)
    simp only [WE, h, mul_assoc]
  refine ⟨π.dual, ?_, fun τ m hm => ?_⟩
  · filter_upwards [sat_below π, placeAe ℚ E D, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat Q] with w h1 h2 ⟨C', hC'⟩ hnorm
    have hb : Below (w.under (𝓞 ℚ)) w := rfl
    obtain ⟨C, hC⟩ := h1 _ hb
    have h4 : 1 < normV (w.under (𝓞 ℚ)) := by
      have := GlobalTheory.LFun.one_lt_absNorm (w.under (𝓞 ℚ))
      simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
    rcases h2 _ hb with hsp | hi
    · exact ⟨C.map (·⁻¹), hC.dual, hsat w _ hsp C C' hC hC' ▸ hC'⟩
    · exfalso
      have h5 := hi.norm
      rw [hnorm] at h5
      nlinarith
  · obtain ⟨m₀, hm₀⟩ := UpperTheory.V.TR.Cen.exists_hasInfChar π (InfinitePlace.mk (τ.comp (algebraMap ℚ E)))
    have e := infPair E (span W M π) Q B hI hB0 τ m₀ m hm₀.1 (UpperTheory.ConvolutionTheory.R2.cap ℚ E D W M π τ m₀ hm₀) hm
    rw [e]
    exact hm₀.dual

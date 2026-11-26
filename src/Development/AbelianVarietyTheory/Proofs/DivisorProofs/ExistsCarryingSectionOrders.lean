module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionWeightBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentialVolumeSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqThetaConstantSpanningClassesLeExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqThetaConstantSpanningClassesLeExp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaConst.ArchBound

theorem norm_pow_le_at_unit_frame (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hA : AllTest Xo c) (R : ℕ) (hR : Odd R)
    (h1R : 1 < R) (xs : Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c)
    (hsp : Submodule.span (𝓞 E) (Set.range xs) = ⊤)
    (hf : GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f) (DF q m : ℕ) (R0 : ℝ)
    (hrun : RunOK E r DF q R0 m) (hm : Dw.p ≤ m ∨ Dw.q ≤ m) (k : U.Comp) (x : (U.X k).dom)
    (hx : ∀ τ i, ‖dmin (U.X k).Gm x.1 τ i‖ = 1) :
    ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ^ (2 * R ^ 4) ≤
      Real.exp (-((1 : ℕ) : ℝ) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) x.1 - p16 E r q m R 1)) := by
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨Hm, χl, fr, θ, Fd, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, hFd, hl2⟩ := Uw.norm k x hx
  have hy : (U.un k x).x = Uw.F.u (Uw.ik k) (Uw.Pm k x) := (Uw.lie k x).1
  have hP := Uw.period k x
  have hfn : IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr (U.un k x).x (U.un k x).s θ := a₉
  have hAH : AHFrame Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr :=
    ⟨a₁, a₂, a₃, a₄, a₅, a₆, fun j hj => by rw [← hy]; exact a₇ j hj, a₈⟩
  have hty := (GlobalTheory.T.relabelling_goodEmbedding_isTypeFn E H Dw l Xo c σ hσ).2.2 Uw.g Uw.e
  have hty' : IsTypeFn H (Uw.F.Di (Uw.ik k)).p (Uw.F.Di (Uw.ik k)).q
      (fun j => Formalism.L2.PjFree.relab c σ (Uw.e j).1) := by
    rw [(Uw.F.sig _).1, (Uw.F.sig _).2]
    exact hty
  obtain ⟨T, ψ, hT⟩ := GlobalTheory.T.exists_torus_of_period_hermitian E H _ _ _ _ Hm hty' hP a₁ a₂ a₃
  obtain ⟨-, hr, hph, hdim⟩ := GlobalTheory.T.periodTorus_isTorusAt_frame E H Dw l Xo c σ r U hσ hU Uw k x Hm T ψ ⟨a₁, a₂, a₃⟩ hT
  have hhol : Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) = χl (Uw.Pm k x a) *
      Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) + Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) *
        θ z := by
    have key : ∀ (x₀ : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x₀)), x₀ = Uw.F.u (Uw.ik k) (Uw.Pm k x) →
        IsFnOf Uw.F (Uw.ik k) (Uw.Pm k x) fr x₀ s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Uw.Pm k x a) =
          χl (Uw.Pm k x a) * Complex.exp (Real.pi * hermForm Hm z (Uw.Pm k x a) +
            Real.pi / 2 * hermForm Hm (Uw.Pm k x a) (Uw.Pm k x a)) * θ z := by
      intro x₀ s h₀ hs
      subst h₀
      exact GlobalTheory.T.appellHumbert_section_entire_with_factor E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH s θ hs
    exact key _ _ hy hfn
  have hchi := GlobalTheory.T.ahFrame_factor_eq_negOnePow_riemannForm E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr hP hAH
  obtain ⟨hsec, hl2', hpt⟩ := GlobalTheory.T.theta_function_torus_l2_norm E H _ _ _ _ Hm T ψ θ Fd hT hhol.1
    (fun a z => by rw [hhol.2 a z, hchi a]) hFd
  rw [hl2] at hl2'
  have hR4 : 0 < R ^ 4 := pow_pos hR.pos 4

  have hval₀ := hf.tauValAt_evR hR (hA _ (U.un k x))
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨ev, hevL⟩ := GlobalTheory.ThetaConst.exists_isLevOf_geometric Xo c hval₀.dvd (U.un k x).x
  have hev : IsFullLev Xo (R ^ 4) (U.un k x).x ev := hevL.2.1
  obtain ⟨a, ha, hgen⟩ := GlobalTheory.T.fullLinearLevel_eq_exp_periods_complexPoint E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) (U.un k x) hP hy (R ^ 4) hR4 ev hev
  have hR2 : Odd (R ^ 2) := hR.pow
  have htors : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := fun q => by rw [← pow_mul]; exact (ha q).2
  choose w hw using fun q =>
    ((GlobalTheory.nullValue_existsUnique_natural_linear GlobalTheory.firstFiveLaws.1 E H Dw l Xo c (R ^ 2) hR2).1 _ (U.un k x) (ev q)
      (htors q)).exists
  have hR0 : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR.pos.ne'
  let z : LatMod Dw (R ^ 4) → (Fin Uw.g → ℂ) := fun q =>
    ((R ^ 2 : ℕ) : ℂ) • ((R ^ 4 : ℕ) : ℂ)⁻¹ • Uw.Pm k x (a q)
  have hz : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) = ψ (Uw.Pm k x (a q)) := fun q => by
    rw [← map_smul]
    congr 1
    simp only [z, smul_smul]
    have : (R : ℂ) ^ 2 * (((R ^ 2 : ℕ) : ℂ) * ((R ^ 4 : ℕ) : ℂ)⁻¹) = 1 := by
      push_cast
      field_simp
    rw [this, one_smul]
  have hwn : ∀ q, ‖Formalism.L2.PjFree.toC (w q)‖ =
      Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ (z q))) := fun q => by
    rw [hpt]
    exact GlobalTheory.T.norm_nullVal_eq_norm_theta_alt E H Dw l Xo c σ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) Hm χl fr θ (U.un k x) hP hAH hy hfn (R ^ 2) hR2
      (ev q) _ (w q) (htors q) (ha q).1 (hw q)

  have hval : evR Xo c f (U.un k x) = ∏ b, w (xs b) := by
    rw [hval₀.unique hR (GlobalTheory.ThetaConst.tauValAt_self hevL hw), GlobalTheory.ThetaConst.tauExpr]
    simp
  obtain ⟨P, hq, hR0', hm'⟩ := hrun T hr (hdim m hm)
  rw [hval, ← hph, ← hq, ← hR0', ← hm']
  have hgen' : ∀ (g : Fin (2 * R ^ 4)) (j : Unit), ∀ v ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
      v = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • ψ (z (xs b))) + (R : ℂ) • y := fun g j => by
    simp only [hz]
    exact GlobalTheory.EtaAn.ArchPt.gen_mod hP hT R (fun b => a (xs b)) (hgen r _ hsp)
  have hmem : ∀ q, ((R : ℂ) ^ 2) • ψ (z q) ∈ T.L := fun q => by
    rw [hz]
    exact (hT.2.2.2.1 _).2 ⟨_, rfl⟩
  have key : ∀ (r : ℕ), T.r = r → Fintype.card Unit ≤ R ^ (2 * I2.PT.f E * r ^ 2) →
      ∀ (w : Fin (2 * R ^ 4) → Unit → Fin r → ℂ) (a : Fin (2 * R ^ 4) → Unit → Fin r → I2.Vsp T.dim),
      (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) →
      (∀ g j, ∀ x ∈ T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ T.L,
        x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) →
      (∀ g j b, ‖w g j b‖ =
        Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) fun _ => a g j b)) →
      ‖∏ g, ∑ j, ((fun _ : Unit => (1 : ℤ)) j : ℂ) * ∏ b, w g j b‖ ≤
        Real.exp (-((1 : ℕ) : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E r P.q P.m R 1)) := by
    intro r' hr' hJ' w' a'
    subst hr'
    exact GlobalTheory.T.norm_prod_sum_theta_le_exp_torus E T DF P R 1 1 h1R le_rfl _ hsec hl2' (Fin (2 * R ^ 4)) Unit
      (by simp) hJ' (fun _ => 1) w' a' (fun _ => by simp)
  have hJ : Fintype.card Unit ≤ R ^ (2 * I2.PT.f E * r ^ 2) := by
    rw [Fintype.card_unit]; exact Nat.one_le_pow _ _ hR.pos
  have := key r hr hJ (fun g j b => Formalism.L2.PjFree.toC (w (xs b))) (fun g j b => ψ (z (xs b)))
    (fun g j b => hmem _) hgen' (fun g j b => hwn _)
  have e : ‖Formalism.L2.PjFree.toC (∏ b, w (xs b))‖ = ∏ b, ‖Formalism.L2.PjFree.toC (w (xs b))‖ := by
    rw [← norm_prod]; rfl
  rw [e]
  simpa [Finset.prod_const, norm_pow] using this

end GlobalTheory.ThetaConst.ArchBound

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThetaConst

theorem normSq_thetaConst_le_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ), GoodEmb c σ → IsUnf U → ∀ R : ℕ, Odd R → 1 < R → ∀ (xs : Fin (Dw.p + Dw.q) → GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : Rul Xo c), Submodule.span (𝓞 E) (Set.range xs) = ⊤ → GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f → ∀ (DF q m : ℕ) (R0 : ℝ), GlobalTheory.EtaAn.RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ z : Σ k, Frame (U.X k).Ψ r, z.2 ∈ (U.X z.1).dom → homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) z ≤ Real.exp ((GlobalTheory.EtaAn.p16 E r q m R 1 - ReciprocityTheory.ChartRestriction.G.I2.phiFD (U.X z.1) (ReciprocityTheory.ChartRestriction.G.I2.th (E := E) q R0) z.2) / (R : ℝ) ^ 4) := by
  intro E _ _ _ H Dw l Xo c σ r U x hσ hU R hR h1R xs f hsp hf DF q m R0 hrun hm z hz
  obtain ⟨k, y⟩ := z
  have hr := hU.1
  subst hr
  have hA : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hsec1 : f ∈ sec Xo c 0 (Dw.p + Dw.q) := hf.mem_sec hR
  have hsec : f ^ 2 ∈ sec Xo c 0 (2 * (Dw.p + Dw.q)) := by
    have := sec_mul Xo c 0 0 _ _ hsec1 hsec1
    rw [add_zero, ← two_mul] at this
    rwa [sq]
  have hS : (U.X k).IsSec (laU U 0 (2 * (Dw.p + Dw.q)) k) (rdU U (f ^ 2) k) :=
    hU.2.2.2.2.1 0 _ ⟨fun _ => antitone_const, even_two_mul _⟩ (f ^ 2) hsec k
  obtain ⟨b, -, hb, hun, -, hphi, hp⟩ := GlobalTheory.T.exists_borel_orthonormal_flag_frame E _ (U.X k) y hz
  have hN : homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨k, y⟩ = ‖rdU U f k (rmul y b)‖ ^ 2 := by
    have h1 : lieFacZ Dw x (wtZ 0 (2 * (Dw.p + Dw.q))) = 1 := by simp [lieFacZ, wtZ]
    unfold homN ptN
    rw [modelWt_wtZ, h1, _root_.one_mul]
    show (U.X k).pnorm (laU U 0 (2 * (Dw.p + Dw.q)) k) (rdU U (f ^ 2) k) y = _
    rw [hp _ _ hS, sq f, GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, norm_mul, sq]
  rw [hN, ← hphi _]
  have hv : rdU U f k (rmul y b) =
      Formalism.L2.PjFree.toC (evR Xo c f ((Formalism.L2.PjFree.Unf.ofPj U).un k ⟨rmul y b, hb⟩)) := dif_pos hb
  have key := ArchBound.norm_pow_le_at_unit_frame E H Dw l Xo c σ _ (Formalism.L2.PjFree.Unf.ofPj U) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) hA R hR h1R xs f hsp hf DF q m R0 hrun hm k ⟨rmul y b, hb⟩ hun
  rw [hv]
  have hn : R ^ 4 ≠ 0 := pow_ne_zero _ hR.pos.ne'
  have hR4 : (R : ℝ) ^ 4 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hR.pos.ne')
  rw [← pow_le_pow_iff_left₀ (sq_nonneg _) (Real.exp_pos _).le hn, ← pow_mul, ← Real.exp_nat_mul]
  refine le_of_le_of_eq key ?_
  congr 1
  push_cast
  rw [mul_div_cancel₀ _ hR4]
  show -((1 : ℝ)) * (I2.phiFD (U.X k) (I2.th (E := E) q R0) (rmul y b) - p16 E (Dw.p + Dw.q) q m R 1) = _
  ring

end GlobalTheory.ThetaConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqThetaConstantSpanningClassesLeExpStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_thetaConstant_spanning_classes_le_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ), GoodEmb c σ → IsUnf U → ∀ R : ℕ, Odd R → 1 < R → ∀ (xs : Fin (Dw.p + Dw.q) → GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : Rul Xo c), Submodule.span (𝓞 E) (Set.range xs) = ⊤ → GlobalTheory.ThetaConst.IsTauRule Xo c R (fun _ : Unit => 1) (fun _ => xs) f → ∀ (DF q m : ℕ) (R0 : ℝ), GlobalTheory.EtaAn.RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ z : Σ k, Frame (U.X k).Ψ r, z.2 ∈ (U.X z.1).dom → homN U x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) z ≤ Real.exp ((GlobalTheory.EtaAn.p16 E r q m R 1 - ReciprocityTheory.ChartRestriction.G.I2.phiFD (U.X z.1) (ReciprocityTheory.ChartRestriction.G.I2.th (E := E) q R0) z.2) / (R : ℝ) ^ 4) := by
  first | exact @GlobalTheory.ThetaConst.normSq_thetaConst_le_exp | exact GlobalTheory.ThetaConst.normSq_thetaConst_le_exp | (intros; apply GlobalTheory.ThetaConst.normSq_thetaConst_le_exp <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovHt.KeySection

open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.ThetaConst GlobalTheory.EtaForm

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


variable (Dw) in
theorem wtZ_zero_eq (m : ℕ) : wtZ (0 : (E →+* ℂ) × ℕ → ℕ) (2 * m) = wtOf Dw (weightOf Dw 0 m) m := by
  refine Prod.ext (funext fun x => ?_) (by simp [wtZ, wtOf])
  simp only [wtZ, wtOf, weightOf]
  split_ifs <;> simp <;> omega

theorem nsmul_wtOf (k : ℕ) (la : AllWt.Weight Dw) (m : ℤ) : k • wtOf Dw la m = wtOf Dw (k • la) (k * m) := by
  induction k with
  | zero => simp [wtOf_zero]
  | succ k ih => rw [succ_nsmul, ih, ← wtOf_add, succ_nsmul]; congr 1; push_cast; ring

theorem homN_pow {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) {G : WTZ E} (hG : Even G.2) (f : Rul Xo c)
    (z : Σ k, Frame (U.X k).Ψ r) (hz : z.2 ∈ (U.X z.1).dom) (k : ℕ) :
    homN U x ((k + 1) • G) (f ^ (k + 1)) z = homN U x G f z ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, pow_succ, homN_mul U x (by simpa using hG.mul_left _) hG _ _ z hz, ih, ← pow_succ]

theorem le_val_pow {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] {la : HeightOneSpectrum (𝓞 K)}
    {v : R → EReal} (hv : IsVal la v) {f : R} {a : ℝ} (h : (a : EReal) ≤ v f) (k : ℕ) :
    (((k + 1 : ℕ) * a : ℝ) : EReal) ≤ v (f ^ (k + 1)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, hv.mul]
    refine le_trans (le_of_eq ?_) (add_le_add ih h)
    rw [← EReal.coe_add]
    congr 1
    push_cast
    ring

theorem wtOf_hodge_anti (n : ℕ) (τ : E →+* ℂ) (i j : ℕ) (hij : i ≤ j) :
    (wtOf Dw ((n : ℤ) • hodgeWt Dw) 0).1 (τ, j) ≤ (wtOf Dw ((n : ℤ) • hodgeWt Dw) 0).1 (τ, i) := by
  simp only [wtOf, hodgeWt, barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp_all <;> omega

theorem pow_mul_mem {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {Z : Comp Xo c} {G₀ : WTZ E} (h₀ : Even G₀.2) {θ : Rul Xo c}
    (h : ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * θ ∈ cuspOn U Z (G + G₀)) (k : ℕ) {G : WTZ E} (hG : Even G.2)
    {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : θ ^ k * f ∈ cuspOn U Z (G + k • G₀) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have := h _ (hG.add (by simpa using h₀.mul_left _)) _ ih
    rwa [add_assoc, ← succ_nsmul, mul_right_comm, ← pow_succ] at this

theorem cost_const {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {la : AllWt.Weight Dw}
    (S : ConstSec U x Z la 0) (s : ℝ) : ∃ e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ, (∀ w, e w = -S.rho_vw w / 8) ∧
      cost e (fun σ => s + Real.log (S.cInf σ) / 8) = s - S.deg / 8 := by
  have hfin : (Function.support fun w => -S.rho_vw w / 8).Finite :=
    S.finite_rho.subset fun w hw h0 => hw (by simp [h0])
  refine ⟨Finsupp.ofSupportFinite _ hfin, fun _ => rfl, ?_⟩
  have hn : (Module.finrank ℚ c.F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h1 : ∑ᶠ w, S.rho_vw w * lw c.F w = ∑ w ∈ hfin.toFinset, S.rho_vw w * lw c.F w :=
    finsum_eq_sum_of_support_subset _ fun w hw => by
      simp only [Set.Finite.coe_toFinset, Function.mem_support] at hw ⊢
      intro h0
      exact hw (by rw [show S.rho_vw w = 0 by linarith, zero_mul])
  have h2 : ((Finsupp.ofSupportFinite _ hfin).sum fun w a => a * Real.log (Ideal.absNorm w.asIdeal : ℝ)) =
      -(Module.finrank ℚ c.F : ℝ) / 8 * ∑ w ∈ hfin.toFinset, S.rho_vw w * lw c.F w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    show -S.rho_vw w / 8 * _ = _
    unfold lw
    field_simp
  unfold cost ConstSec.deg lineDeg
  rw [h1, h2, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul]
  field_simp
  ring

theorem exists_twist {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x om : ℝ} (h : FlatDegree U x om) (Z : Comp Xo c)
    (hZ : HasPts U Z) (n : ℤ) : ∃ S : ConstSec U x Z (parWt Dw fun _ => -n) 0,
      S.deg = n * (Fintype.card (Psi H) * (((Dw.p : ℝ) - Dw.q) / 2 * om)) := by
  have s : ∀ τ, FlatSec U x Z τ := fun τ => (h Z τ).1.some
  refine ⟨(ConstSec.prod hZ Finset.univ fun τ => (s τ).toFrame.zpow n).copy
    (by rw [parWt_eq_sum]; simp only [neg_neg]; convert rfl) (by simp), ?_⟩
  refine (ConstSec.prod_spec hZ Finset.univ fun τ => (s τ).toFrame.zpow n).2.2.2.2.trans ?_
  have : ∀ τ, ((s τ).toFrame.zpow n).deg = n * (((Dw.p : ℝ) - Dw.q) / 2 * om) := fun τ => by
    have h1 := (h Z τ).2 (s τ)
    rw [FlatSec.deg_eq_toFrame, neg_neg, flatDegVal] at h1
    rw [(ConstSec.zpow_spec _ _).2.2.2, add_right_cancel h1]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Free


set_option maxHeartbeats 1000000 in
theorem exists_section {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (hL : GlobalTheory.FlatCore.Laws U x) (hM : 5 ^ 4 ∣ l.M) (Z : Comp Xo c)
    (S : ConstSec U x Z (parWt Dw fun _ => -(12 * ((Dw.p + Dw.q : ℕ) : ℤ))) 0) (u : AllWt.Weight Dw) (β A : ℝ)
    (hb : ∀ (xs : Fin (Dw.p + Dw.q) → LatMod Dw (5 ^ 4)) (f : Rul Xo c), Submodule.span (𝓞 D.host.E) (Set.range xs) = ⊤ →
      IsTauRule Xo c 5 (fun _ : Unit => 1) (fun _ => xs) f → ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X,
      (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
        homN (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨y.1, y.2.1⟩ ≤ A ∧
        ENNReal.ofReal (homN (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨y.1, y.2.1⟩) ^ 3 ≤
          ENNReal.ofReal (Real.exp β) * bergOn (U σ) (V σ) (dict σ) Z (wtOf Dw u 0) y) :
    ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ), Carries U Z u (uPrime Dw u) θ ∧
      (∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
        ∀ y : IntFr Xo c T io, y.IsAlg → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ →
          ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧
      InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - uPrime Dw u)) 0) 8 θ t ∧
      cost e t = β / 2 + ((3 * (Dw.p + Dw.q) : ℕ) : ℝ) *
        (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) / 8 - S.deg / 8 := by
  have h5 : Odd 5 := by decide
  obtain ⟨hks, hK⟩ := GlobalTheory.KeyPowTw.exists_twSec_keyPow _ H Dw l Xo c r U x hL.unf hL.xi hL.geo hL.pos hL.good
  obtain ⟨K, hK0, hK1⟩ := hK Z (3 * (Dw.p + Dw.q))
  set κ : ℝ := ((3 * (Dw.p + Dw.q) : ℕ) : ℝ) *
    (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) with hκ
  obtain ⟨x₀, hx₀⟩ := exists_isAdm Dw (R := 5) (by norm_num)
  obtain ⟨w, f, hf, hfZ⟩ := exists_isGenRule_nonzeroOn (Xo := Xo) (c := c) h5 (by norm_num) hM x₀ Z
  have hsp := hx₀.spans (by norm_num) w
  replace hb := hb _ f hsp hf
  obtain ⟨e, he, hc⟩ := cost_const S (β / 2 + κ / 8)
  have hw : (8 : ℤ) • (u - uPrime Dw u) = ((24 * (Dw.p + Dw.q) : ℕ) : ℤ) • hodgeWt Dw := by
    rw [uPrime, sub_sub_cancel, smul_smul]
    congr 1
    push_cast
    ring
  have hG : (11 + 1) • wtZ (0 : (D.host.E →+* ℂ) × ℕ → ℕ) (2 * (Dw.p + Dw.q)) +
      wtOf Dw 0 (-(4 * ((3 * (Dw.p + Dw.q) : ℕ) : ℤ))) + wtOf Dw (parWt Dw fun _ => -(12 * ((Dw.p + Dw.q : ℕ) : ℤ))) 0 =
      wtOf Dw ((8 : ℤ) • (u - uPrime Dw u)) 0 := by
    rw [wtZ_zero_eq Dw, nsmul_wtOf, ← wtOf_add, ← wtOf_add, hw]
    congr 1
    · funext τ j
      simp only [weightOf, hodgeWt, barWt, parWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      split_ifs <;> push_cast <;> ring
    · push_cast
      ring
  have hev : Even (wtZ (0 : (D.host.E →+* ℂ) × ℕ → ℕ) (2 * (Dw.p + Dw.q))).2 := by
    rw [wtZ_zero_eq Dw]; exact even_wtOf _ _
  have hev' : Even ((11 + 1) • wtZ (0 : (D.host.E →+* ℂ) × ℕ → ℕ) (2 * (Dw.p + Dw.q))).2 := by
    rw [wtZ_zero_eq Dw, nsmul_wtOf]; exact even_wtOf _ _
  have hf2 : f ^ 2 ∈ secZ Xo c (exZ Dw (wtZ 0 (2 * (Dw.p + Dw.q)))) := by
    have := IsTauRule.mem_sec h5 hf
    rw [← secZ_nat] at this
    convert pow_mem_secZ this 2 using 2
    funext i
    cases i <;> simp [exZ, wtZ, ex]
  have hmem : (f ^ 2) ^ (11 + 1) * K.sig * S.sig ∈ secZ Xo c (exZ Dw (wtOf Dw ((8 : ℤ) • (u - uPrime Dw u)) 0)) := by
    rw [← hG, exZ_add_eq, exZ_add_eq]
    refine mul_mem_secZ (mul_mem_secZ ?_ K.sig_mem) S.sig_mem
    convert pow_mem_secZ hf2 (11 + 1) using 2
    funext i
    cases i <;> simp [exZ, wtZ]
  have hsupp : (f ^ 2) ^ (11 + 1) * K.sig * S.sig ∈ suppOn Z := mul_mem_suppOn _ S.sig_mem_suppOn
  have hnorm : ∀ σ, GoodEmb c σ → ∀ z ∈ framesOn (U σ) Z,
      homN (U σ) x (wtOf Dw ((8 : ℤ) • (u - uPrime Dw u)) 0) ((f ^ 2) ^ (11 + 1) * K.sig * S.sig) z =
        homN (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) z ^ (11 + 1) * K.cInf σ * S.cInf σ := fun σ hσ => by
    have h1 := fun z hz => S.homN_mul_sig (G := (11 + 1) • wtZ 0 (2 * (Dw.p + Dw.q)) +
      wtOf Dw 0 (-(4 * ((3 * (Dw.p + Dw.q) : ℕ) : ℤ)))) (hev'.add K.even) ((f ^ 2) ^ (11 + 1) * K.sig) (σ := σ) (z := z) hz
    have h2 := fun z hz => K.homN_mul_sig hev' ((f ^ 2) ^ (11 + 1)) (σ := σ) (z := z) hz
    rw [show goodOf c σ = σ from if_pos hσ] at h1 h2
    intro z hz
    rw [← hG, ← homN_pow (U σ) x hev _ z hz.1, ← h2 z hz]
    exact h1 z hz
  refine ⟨(f ^ 2) ^ (11 + 1) * K.sig * S.sig, e, _, ⟨hmem, ?_, fun k g hg => ?_⟩, ?_, ⟨fun σ => ?_, ?_⟩, hc⟩
  · have h1 := congrArg (genVal Z) K.mul_inv
    have h2 := congrArg (genVal Z) S.mul_inv
    rw [map_mul, genVal_idem] at h1 h2
    rw [map_mul, map_mul, map_pow, map_pow]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hfZ)) (left_ne_zero_of_mul_eq_one h1))
      (left_ne_zero_of_mul_eq_one h2)
  · have h1 := GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd _ H Dw l Xo c r U x Z _ _ hks hL.unf hL.pos (even_wtOf _ _)
      (fun τ i j hij _ => by rw [hw]; exact wtOf_hodge_anti _ τ i j hij) hmem hsupp fun σ hσ =>
        ⟨A ^ (11 + 1) * K.cInf σ * S.cInf σ, fun z hz => by
          rw [hnorm σ hσ z hz]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (homN_nonneg _ _ _ _ _) (hb σ hσ ⟨z.1, z.2, hz.1⟩ hz).1 _) (K.cInf_pos σ).le)
            (S.cInf_pos σ).le⟩
    have h2 := pow_mul_mem (even_wtOf _ _) h1 k (by rw [nsmul_wtOf]; exact even_wtOf _ _) hg
    convert h2 using 2
    rw [nsmul_wtOf, nsmul_wtOf, nsmul_wtOf, ← wtOf_add]
    congr 1
    · funext τ j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      push_cast
      ring
  · intro la T io e₀ ho y hy φ hφ
    have hv : (fun g => nval T.V e₀ (evI y g)) ∈ valSet Xo c (algCls Xo c) la := ⟨PtV.mk la ho y hy () trivial, rfl⟩
    rcases mem_valOn_or (Z := Z) hv with hv | hv
    · have h1 : ((φ / 625 / e₀ : ℝ) : EReal) ≤ nval T.V e₀ (evI y f) := by
        by_cases h0 : evI y f = 0
        · rw [h0, nval_zero]; exact le_top
        · rw [nval_of_ne h0, EReal.coe_le_coe_iff]
          have := GlobalTheory.ThetaSteep.tau_bound y hφ h5 (by norm_num) (fun _ => hsp) hf h0
          exact div_le_div_of_nonneg_right (by push_cast at this; linarith) (Nat.cast_nonneg _)
      have h2 := le_val_pow (isVal_valOn hv) (le_val_pow (isVal_valOn hv) h1 1) 11
      have h3 := K.lo_le la _ hv
      have h4 := S.val_mul_sig ((f ^ 2) ^ (11 + 1) * K.sig) hv
      rw [(isVal_valOn hv).mul _ K.sig] at h4
      refine le_trans ?_ (le_of_le_of_eq (add_le_add (add_le_add h2 h3) le_rfl) h4.symm)
      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, he]
      have h6 : 0 ≤ φ / e₀ := div_nonneg hφ.nonneg (Nat.cast_nonneg _)
      have h7 := hK0 la
      simp only [Pi.zero_apply]
      push_cast
      rw [mul_div_assoc, div_right_comm]
      linarith
    · exact (hv _ hsupp).symm ▸ le_top
  · have h1 : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := Formalism.L2.Pj.goodOf_conj c σ
    obtain ⟨z, hz⟩ := (S.hasPts.1 σ).1
    have h2 := fun z hz => S.homN_eq (σ := (starRingEnd ℂ).comp σ) (z := z) hz
    rw [h1] at h2
    beta_reduce
    rw [← h2 z hz, S.homN_eq hz]
  · intro σ hσ y hy
    have h1 := pow_le_pow_left' (hb σ hσ y hy).2 8
    have ha := homN_nonneg (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨y.1, y.2.1⟩
    have hk : K.cInf σ ≤ Real.exp κ := (Real.log_le_iff_le_exp (K.cInf_pos σ)).1 (hK1 σ)
    have hs := S.cInf_pos σ
    have hk0 := K.cInf_pos σ
    rw [hnorm σ hσ _ hy]
    generalize homN (U σ) x (wtZ 0 (2 * (Dw.p + Dw.q))) (f ^ 2) ⟨y.1, y.2.1⟩ = a at h1 ha
    have h2 : Real.exp (2 * (8 : ℕ) * (β / 2 + κ / 8 + Real.log (S.cInf σ) / 8)) =
        (Real.exp κ * S.cInf σ) ^ 2 * Real.exp β ^ 8 := by
      rw [← Real.exp_log hs, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.log_exp]
      congr 1
      push_cast
      ring
    rw [h2, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (Real.exp_pos β).le, mul_assoc (ENNReal.ofReal _),
      ← mul_pow]
    refine le_trans ?_ (mul_le_mul_right h1 _)
    rw [← pow_mul, ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (a ^ (11 + 1) * K.cInf σ * S.cInf σ) ^ 2 ≤ (a ^ (11 + 1) * Real.exp κ * S.cInf σ) ^ 2 := by gcongr
      _ = _ := by ring

theorem twist_cost_le {f r p q L om PP : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = r)
    (ho : |om| ≤ 3 * L) (hP : (f * r * L) ^ 12 ≤ PP) :
    3 * r * (2 * (f * r) * Real.log (2 * Real.pi)) / 8 - 12 * r * (f * ((p - q) / 2 * om)) / 8 ≤ 10 * PP := by
  have h1 : Real.log (2 * Real.pi) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity)
    linarith [Real.pi_le_four]
  have h2 : -((p - q) / 2 * om) ≤ r / 2 * (3 * L) := by
    refine (neg_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) ho (abs_nonneg _) (by linarith)
  have hfr : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf hr
  have hZ : 1 ≤ f * r * L := one_le_mul_of_one_le_of_one_le hfr hL
  have h3 : f * r * L * r ≤ PP := by
    refine le_trans ?_ ((pow_le_pow_right₀ hZ (by norm_num : 2 ≤ 12)).trans hP)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have h4 : f * r * r ≤ f * r * L * r := by
    have : f * r ≤ f * r * L := le_mul_of_one_le_right (by linarith) hL
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have h5 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ f * r * r by positivity)
  have h6 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ f * r by positivity)
  nlinarith


end GlobalTheory.CovHt.KeySection

end

module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombination
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrCombAny

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem real_part {S T : HSp D} (x : WO S T) : (GlobalTheory.FinTranslate.eInf D • x : WO S T).map (finPart D) = 0 := by
  ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul (x i j)

theorem fin_part {S T : HSp D} (x : WO S T) : ((1 - GlobalTheory.FinTranslate.eInf D) • x : WO S T).map (infPart D) = 0 := by
  ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (x i j)

theorem psi_fin_eq {S T : HSp D} {w : WO S T} (hw : w.map (infPart D) = 0) (x : WO S T) :
    ψ (symplOH S T w x) = ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) := by
  have hx : x = GlobalTheory.FinTranslate.eInf D • x + (1 - GlobalTheory.FinTranslate.eInf D) • x := by
    rw [← add_smul, add_sub_cancel, one_smul]
  conv_lhs => rw [hx]
  rw [GlobalTheory.FinTranslate.symplOH_add_right, GlobalTheory.FinTranslate.symplOH_fin_real hw (real_part x), zero_add]

theorem exists_orth_any {S T : HSp D} (hψ : IsStdChar D ψ (-1)) (s : Finset (WO S T)) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ w ∈ U, w.map (infPart D) = 0 → ∀ x ∈ s, ψ (symplOH S T w x) = 1 := by
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∀ x ∈ s, ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1}
      zero_mem' := fun x _ => by rw [GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb x hx => by
        rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
      neg_mem' := fun {a} ha x hx => by
        have := AddChar.map_add_eq_mul ψ (symplOH S T a ((1 - GlobalTheory.FinTranslate.eInf D) • x))
          (symplOH S T (-a) ((1 - GlobalTheory.FinTranslate.eInf D) • x))
        rw [← GlobalTheory.FinTranslate.symplOH_add_left, add_neg_cancel, GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one,
          ha x hx, one_mul] at this
        exact this.symm }
  refine ⟨U, ?_, fun w hw hw' x hx => (psi_fin_eq hw' x).trans (hw x hx)⟩
  have e : (U : Set (WO S T)) = ⋂ x ∈ s, {w | ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1} := by
    ext w
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  exact isOpen_biInter_finset fun x _ => GlobalTheory.FrComb.isOpen_ker hψ (fin_part x)

theorem contDiff_psi {S T : HSp D} (hψ : IsStdChar D ψ (-1)) {n : ℕ} {L : (Fin n → ℝ) →+ WO S T} (hL : Continuous L)
    (hLf : ∀ t, (L t).map (finPart D) = 0) (x : WO S T) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => ψ (symplOH S T (L t) x) := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  let φ : (Fin n → ℝ) →+ ℂ :=
    { toFun := fun t => lam (symplOH S T (L t) x)
      map_zero' := by rw [map_zero L, GlobalTheory.FinTranslate.symplOH_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L, GlobalTheory.FinTranslate.symplOH_add_left, map_add (f := _)] }
  have hφ := GlobalTheory.WeilVacMove.contDiff_additive φ (hl.comp ((GlobalTheory.FinTranslate.continuous_symplOH S T x).comp hL))
  have e : (fun t => ψ (symplOH S T (L t) x)) = fun t => Complex.exp (φ t) :=
    funext fun t => hlam _ (GlobalTheory.WeilVacMove.snd_symplOH S T (L t) x (Or.inl (hLf t)))
  rw [e]
  exact hφ.cexp

theorem biTheta_combL {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) (c : WO A S →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ A S c (fun u' => K u' v) u) := by
  have e : (fun u v => comb ψ A S c (fun u' => K u' v) u) =
      fun u v => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * K (u + x) v) := by
    funext u v; exact GlobalTheory.FrComb.comb_apply c _ u
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply]
    exact continuous_finsetSum _ fun x _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH A S x).comp continuous_fst)).mul
        (hK.cont.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S (u + L t) x) * K (u + L t + x) (v + L' t))) =
        fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * (ψ (symplOH A S (L t) x) * K (u + x + L t) (v + L' t))) := by
      funext t
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_const.mul
      ((contDiff_psi hψ hL hLf x).mul (hK.smooth n L L' hL hL' hLf hL'f (u + x) v)))
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc, hK.quasiL, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH A S (ratW S A γ) x + symplOH A S u x) * ψ (-(symplOH A S (ratW S A γ) u + symplOH A S (ratW S A γ) x)) =
        ψ (-(symplOH A S (ratW S A γ) u)) * ψ (symplOH A S u x) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c x * K (u + x) v) * key
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hK.quasiR]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    obtain ⟨V, hV, hVf⟩ := exists_orth_any hψ c.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' v)
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    refine ⟨U, hU, fun a ha ha' u => ?_⟩
    funext v
    simp only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e3 := congrFun (hUf a ha ha' (u + x)) v
    simp only [heisO] at e3
    rw [← e3]
    ring

theorem biTheta_combR {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) (c : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ S A' c (K u) v) := by
  have e : (fun u v => comb ψ S A' c (K u) v) =
      fun u v => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * K u (v + y)) := by
    funext u v; exact GlobalTheory.FrComb.comb_apply c _ v
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply]
    exact continuous_finsetSum _ fun y _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH S A' y).comp continuous_snd)).mul
        (hK.cont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' (v + L' t) y) * K (u + L t) (v + L' t + y))) =
        fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * (ψ (symplOH S A' (L' t) y) * K (u + L t) (v + y + L' t))) := by
      funext t
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm v, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun y _ => contDiff_const.mul (contDiff_const.mul
      ((contDiff_psi hψ hL' hL'f y).mul (hK.smooth n L L' hL hL' hLf hL'f u (v + y))))
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hK.quasiL]
    ring
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [add_assoc, hK.quasiR, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH S A' (ratW A' S γ) y + symplOH S A' v y) * ψ (-(symplOH S A' (ratW A' S γ) v + symplOH S A' (ratW A' S γ) y)) =
        ψ (-(symplOH S A' (ratW A' S γ) v)) * ψ (symplOH S A' v y) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c y * K u (v + y)) * key
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    refine ⟨U, hU, fun a ha ha' v => ?_⟩
    funext u
    simp only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e3 := congrFun (hUf a ha ha' (v + y)) u
    simp only [heisO] at e3
    rw [← e3]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    obtain ⟨V, hV, hVf⟩ := exists_orth_any hψ c.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' u)

theorem biTheta_biComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (C : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' C → ∀ (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ), IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) := by
  intro D ψ hψ A S A' C hC c c'
  exact biTheta_combL hψ (biTheta_combR hψ hC c') c

end GlobalTheory.FrCombAny

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isJointlySmoothBiTheta_twoVarCombination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (C : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' C → ∀ (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ), IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) := by
  first | exact @GlobalTheory.FrCombAny.biTheta_biComb | exact GlobalTheory.FrCombAny.biTheta_biComb | (intros; apply GlobalTheory.FrCombAny.biTheta_biComb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleTraceZeroNormAdjustRealComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleTraceZeroNormAdjustRealComponents
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

private theorem tmulOne_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (σ : E →ₐ[F] E) (x : R) :
    (Algebra.TensorProduct.map f σ).toRingHom (x ⊗ₜ[F] (1 : E)) = f x ⊗ₜ[F] (1 : E) := by
  change Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem scal_gen (σ : E →ₐ[F] E) (μ : E) (hμ : μ ≠ 0)
    (r : ∀ w : InfinitePlace F, w.Completion) (hr : ∀ w, r w ≠ 0)
    (hN : ∀ w, ((1 : w.Completion) ⊗ₜ[F] (μ * σ μ) : w.Completion ⊗[F] E) = 4 * (r w ⊗ₜ[F] (1 : E)) ^ 4)
    (u₀ : (AF F ⊗[F] E)ˣ) :
    ∃ u ε : (AF F ⊗[F] E)ˣ, (ε : AF F ⊗[F] E) * (u : AF F ⊗[F] E) * sigR (AF F) σ (u : AF F ⊗[F] E) = inclR (AF F) μ ∧
      (∀ v, compFin F E v u = compFin F E v u₀) ∧
      ∀ w, compInf F E w ((ε : AF F ⊗[F] E) * sigR (AF F) σ (ε : AF F ⊗[F] E)) = 4 := by
  set c := sigR (AF F) σ with hc
  set e : AF F ⊗[F] E := pairA F 1 0 ⊗ₜ[F] (1 : E) with he
  have hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0 :=
    Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))
  have hee : e * e = e := by rw [he, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  have hce : c e = e := tmulOne_map F E (AlgHom.id F (AF F)) σ _
  have hfe : ∀ v, compFin F E v e = 0 := by
    intro v
    refine (tmulOne_map F E (evFin F v) (AlgHom.id F E) _).trans ?_
    rw [evFin, AlgHom.comp_apply, show sndA F (pairA F 1 0) = 0 from rfl, map_zero, TensorProduct.zero_tmul]
  have hie : ∀ w, compInf F E w e = 1 := by
    intro w
    refine (tmulOne_map F E (evInf F w) (AlgHom.id F E) _).trans ?_
    rw [evInf, AlgHom.comp_apply, show fstA F (pairA F 1 0) = 1 from rfl, map_one, Algebra.TensorProduct.one_def]
  let R : AF F := pairA F (fun w => r w) 1
  let R' : AF F := pairA F (fun w => (r w)⁻¹) 1
  have hRR : R * R' = 1 := Prod.ext (funext fun w => mul_inv_cancel₀ (hr w)) (mul_one (1 : Af F))
  set a : AF F ⊗[F] E := R ⊗ₜ[F] (1 : E) with ha
  set a' : AF F ⊗[F] E := R' ⊗ₜ[F] (1 : E) with ha'
  have haa : a * a' = 1 := by
    rw [ha, ha', Algebra.TensorProduct.tmul_mul_tmul, mul_one, hRR, Algebra.TensorProduct.one_def]
  have hca : c a = a := tmulOne_map F E (AlgHom.id F (AF F)) σ _
  have hia : ∀ w, compInf F E w a = r w ⊗ₜ[F] (1 : E) := fun w =>
    tmulOne_map F E (evInf F w) (AlgHom.id F E) _
  have hu0 : (u₀ : AF F ⊗[F] E) * ↑u₀⁻¹ = 1 := Units.mul_inv u₀
  set x : AF F ⊗[F] E := e * a + (1 - e) * u₀ with hx
  set x' : AF F ⊗[F] E := e * a' + (1 - e) * ↑u₀⁻¹ with hx'
  have hxx : x * x' = 1 := by
    rw [hx, hx']
    linear_combination (2 - a * ↑u₀⁻¹ - (u₀ : AF F ⊗[F] E) * a') * hee + e * e * haa + (1 - e) * (1 - e) * hu0
  let U : (AF F ⊗[F] E)ˣ := ⟨x, x', hxx, by rw [mul_comm]; exact hxx⟩

  have hshape : ∀ y, c (e * a + (1 - e) * y) = e * a + (1 - e) * c y := by
    intro y; rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, hce, hca]
  have hread : ∀ w y, compInf F E w (e * a + (1 - e) * y) = r w ⊗ₜ[F] (1 : E) := by
    intro w y; rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, hie, hia]; ring
  let M : (AF F ⊗[F] E)ˣ := Units.map (inclR (AF F) : E →+* AF F ⊗[F] E).toMonoidHom (Units.mk0 μ hμ)
  let P : (AF F ⊗[F] E)ˣ := U * Units.map c.toMonoidHom U
  refine ⟨U, M * P⁻¹, ?_, ?_, ?_⟩
  · have h1 : ((P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (U * c U) = 1 := by
      have := Units.inv_mul P
      simpa [P] using this
    calc ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * U * c U
        = (M : AF F ⊗[F] E) * (((P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (U * c U)) := by
          rw [Units.val_mul]; ring
      _ = inclR (AF F) μ := by rw [h1, mul_one]; rfl
  · intro v
    change compFin F E v x = _
    rw [hx, map_add (f := _), map_mul, map_mul, map_sub, map_one, hfe]; ring
  · intro w
    set φ := compInf F E w with hφ
    set ρ : w.Completion ⊗[F] E := r w ⊗ₜ[F] (1 : E) with hρdef
    have hρ : ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) = 1 := by
      rw [hρdef, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ (hr w), Algebra.TensorProduct.one_def]
    have hP : (P : AF F ⊗[F] E) = x * c x := rfl
    have hM : (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] μ := rfl
    have hε : ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (x * c x) = M := by
      rw [← hP, ← Units.val_mul, inv_mul_cancel_right]
    have hε' := congrArg c hε
    rw [map_mul, map_mul] at hε'
    have hall : (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *
        ((x * c x) * (c x * c (c x))) = (M : AF F ⊗[F] E) * c M := by
      rw [← hε', ← hε]; ring
    have hφx : φ x = ρ := hread w _
    have hφcx : φ (c x) = ρ := by rw [hx, hshape, hread]
    have hφccx : φ (c (c x)) = ρ := by rw [hx, hshape, hshape, hread]
    have hcM : c (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] σ μ := by
      rw [hM, hc]
      change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] μ) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hφ1 : ∀ z : E, φ ((1 : AF F) ⊗ₜ[F] z) = (1 : w.Completion) ⊗ₜ[F] z := by
      intro z
      rw [hφ]
      change Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] z) = _
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    have hrhs : φ ((M : AF F ⊗[F] E) * c M) = 4 * ρ ^ 4 := by
      rw [map_mul, hcM, hM, hφ1, hφ1, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hN w]
    have key := congrArg φ hall
    have hB : φ ((x * c x) * (c x * c (c x))) = ρ * ρ * (ρ * ρ) := by
      rw [map_mul, map_mul, map_mul, hφx, hφcx, hφccx]
    rw [map_mul φ _ ((x * c x) * (c x * c (c x))), hB, hrhs] at key
    linear_combination ((r w)⁻¹ ⊗ₜ[F] (1 : E)) ^ 4 * key -
      (φ (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) - 4) *
        (1 + ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 2 + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 3) * hρ
end

private theorem scal_pos (D : D7) (μ : D.host.E) (hμ : μ ≠ 0) (w : InfinitePlace D.host.F) :
    0 < InfinitePlace.Completion.ringEquivRealOfIsReal (NumberField.IsTotallyReal.isReal w)
      (algebraMap D.host.F w.Completion ⟨μ * star μ, (IsCMField.complexConj_eq_self_iff D.host.E _).1 (by
        change star (μ * star μ) = μ * star μ; rw [star_mul, star_star])⟩) := by
  set hw := NumberField.IsTotallyReal.isReal w
  set n : D.host.F := ⟨μ * star μ, (IsCMField.complexConj_eq_self_iff D.host.E _).1 (by
        change star (μ * star μ) = μ * star μ; rw [star_mul, star_star])⟩ with hn
  letI : Algebra D.host.F ℂ := w.embedding.toAlgebra
  let φ : D.host.E →ₐ[D.host.F] ℂ := by
    set_option synthInstance.maxHeartbeats 400000 in exact IsAlgClosed.lift
  have h1 : φ (algebraMap D.host.F D.host.E n) = w.embedding n := φ.commutes n
  have h2 : (algebraMap D.host.F D.host.E n) = μ * star μ := rfl
  have h3 : φ (star μ) = starRingEnd ℂ (φ μ) :=
    IsCMField.complexEmbedding_complexConj D.host.E (φ : D.host.E →+* ℂ) μ
  rw [h2, map_mul, h3, Complex.mul_conj] at h1
  have h4 : ((InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) : ℂ) = w.embedding n := by
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  have h5 : 0 < Complex.normSq (φ μ) := Complex.normSq_pos.2 (by simpa using hμ)
  have h6 := h4.trans h1.symm
  have h7 : (InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) = Complex.normSq (φ μ) := by
    exact_mod_cast h6
  rw [h7]; exact h5

private theorem scal_root (F E : Type) [Field F] [Field E] [Algebra F E] (w : InfinitePlace F) (hw : w.IsReal) (n : F)
    (hn : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion n)) :
    ∃ r : w.Completion, r ≠ 0 ∧
      ((1 : w.Completion) ⊗ₜ[F] (algebraMap F E n) : w.Completion ⊗[F] E) = 4 * (r ⊗ₜ[F] (1 : E)) ^ 4 := by
  set f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set t := f (algebraMap F w.Completion n) with ht
  have h0 : 0 < √(√(t / 4)) := by positivity
  have h4 : 4 * (f.symm √(√(t / 4))) ^ 4 = algebraMap F w.Completion n := by
    apply f.injective
    rw [map_mul, map_pow, map_ofNat, RingEquiv.apply_symm_apply, ← ht, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
    ring
  refine ⟨f.symm √(√(t / 4)), (map_ne_zero f.symm).2 h0.ne', ?_⟩
  have h5 := congrArg (Algebra.TensorProduct.includeLeftRingHom : w.Completion →+* w.Completion ⊗[F] E) h4
  rw [map_mul, map_pow, map_ofNat, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply] at h5
  rw [h5, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_scal_real : ∀ (D : D7) (μ : D.host.E), IsSkew μ → ∀ u₀ : (AE D)ˣ, ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ (∀ v, compFin D.host.F D.host.E v u = compFin D.host.F D.host.E v u₀) ∧ ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4 := by
  intro D μ hμ u₀
  choose r hr hN using fun w : InfinitePlace D.host.F =>
    scal_root D.host.F D.host.E w _ _ (scal_pos D μ hμ.1 w)
  exact scal_gen D.host.F D.host.E D.sp.cm.sig μ hμ.1 r hr hN u₀

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleTraceZeroNormAdjustRealComponentsStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idele_traceZero_norm_adjust_realComponents : ∀ (D : D7) (μ : D.host.E), IsSkew μ → ∀ u₀ : (AE D)ˣ, ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ (∀ v, compFin D.host.F D.host.E v u = compFin D.host.F D.host.E v u₀) ∧ ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4 := by
  first | exact @GlobalTheory.StdUnn.exists_scal_real | exact GlobalTheory.StdUnn.exists_scal_real | (intros; apply GlobalTheory.StdUnn.exists_scal_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSource
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSource
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSuperpos

variable {D : D7}

theorem pair_swap {S A B T : HSp D} (o : OrthDec S A B) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (k : Ω → WO B T) (a : Ω → ℂ) (hk : Measurable k) (ha : Integrable a μ)
    (ν : Measure (WO A T)) [IsFiniteMeasure ν]
    (Φ : WO S T → ℂ) (hΦc : Continuous Φ) (CΦ : ℝ) (hΦ : ∀ x, ‖Φ x‖ ≤ CΦ)
    (g : WO A T → ℂ) (hgc : Continuous g) (Cg : ℝ) (hg : ∀ x, ‖g x‖ ≤ Cg) :
    ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν =
      ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  haveI : BorelSpace (WO B T) := ⟨rfl⟩
  haveI : SFinite ν := @instSFiniteOfSigmaFinite _ _ ν (@IsFiniteMeasure.toSigmaFinite _ _ ν _)
  obtain ⟨-, -, hA2, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨-, -, hB2, -⟩ := lattice_Mx D T.rank B.rank
  have hσ : Measurable fun q : WO A T × Ω => Φ ((o.resS T).symm (q.1, k q.2)) :=
    hΦc.measurable.comp ((o.continuous_resS_symm T).measurable.comp
      (measurable_fst.prodMk (hk.comp measurable_snd)))
  have hgm : Measurable fun q : WO A T × Ω => star (g q.1) :=
    (continuous_star.comp hgc).measurable.comp measurable_fst
  have h1 : Integrable (fun q : WO A T × Ω => a q.2) (ν.prod μ) := ha.comp_snd ν
  have hint : Integrable (Function.uncurry fun u w => a w * Φ ((o.resS T).symm (u, k w)) * star (g u))
      (ν.prod μ) := by
    refine (h1.norm.mul_const (CΦ * Cg)).mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact (h1.aestronglyMeasurable.mul hσ.aestronglyMeasurable).mul hgm.aestronglyMeasurable
    · rcases q with ⟨u, w⟩
      simp only [Function.uncurry_apply_pair, norm_mul, norm_star]
      have hC : 0 ≤ CΦ := (norm_nonneg _).trans (hΦ 0)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hΦ _) (hg _) (norm_nonneg _) hC) (norm_nonneg _)
  calc ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν
      = ∫ u, ∫ w, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂μ ∂ν := by
        congr 1; funext u; rw [integral_mul_const]
    _ = ∫ w, ∫ u, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
        congr 1; funext w; rw [← integral_const_mul]; congr 1; funext u; ring

theorem exists_sfinite {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Ω → ℂ) (ha : Integrable a μ) :
    ∃ s : Set Ω, SigmaFinite (μ.restrict s) ∧ ∀ X : Ω → ℂ, ∫ w, a w * X w ∂μ = ∫ w, a w * X w ∂(μ.restrict s) := by
  have hf := ha.aefinStronglyMeasurable
  refine ⟨hf.sigmaFiniteSet, hf.sigmaFinite_restrict, fun X => ?_⟩
  have hs : MeasurableSet hf.sigmaFiniteSet := hf.measurableSet
  have h0 : ∀ᵐ w ∂μ, w ∉ hf.sigmaFiniteSet → a w = 0 := by
    have := hf.ae_eq_zero_compl
    rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at this
    exact this.mono fun w hw hws => hw hws
  exact (setIntegral_eq_integral_of_ae_compl_eq_zero (h0.mono fun w hw hws => by rw [hw hws, zero_mul])).symm

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem comm_sfinite {S A B T : HSp D} (o : OrthDec S A B) {χ χ' : (AE D)ˣ →* Circle} {om : Om A T}
    (hW : IsWeilDatumO ψ A T χ χ' om) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (k : Ω → WO B T) (a : Ω → ℂ)
    (hk : Measurable k) (ha : Integrable a μ) (p : GA D A × GA D T) (u₀ : WO A T) :
    om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ =
      ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  have hψ := hW.std
  set H : WO S T → ℂ := fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 with hH
  have hHt : IsThetaFunO ψ S T H := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o F hF).1 χ χ' om hW p
  have hHs : ∀ u b, H ((o.resS T).symm (u, b)) = om p (fun u' => F ((o.resS T).symm (u', b))) u := by
    intro u b; simp only [hH, AddEquiv.apply_symm_apply]
  have hsl : ∀ b, IsThetaFunO ψ A T (fun u => F ((o.resS T).symm (u, b))) := by
    intro b
    have := GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o F hF Unit (Measure.dirac ()) (fun _ => b) (fun _ => 1)
      measurable_const (integrable_const _)
    simpa using this
  set G : WO A T → ℂ := fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ with hGdef
  set R : WO A T → ℂ := fun u => ∫ w, a w * om p (fun u' => F ((o.resS T).symm (u', k w))) u ∂μ with hRdef
  have hG : IsThetaFunO ψ A T G := GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o F hF Ω μ k a hk ha
  have hR' : R = fun u => ∫ w, a w * H ((o.resS T).symm (u, k w)) ∂μ := by
    funext u; simp only [hRdef, hHs]
  have hR : IsThetaFunO ψ A T R := by
    rw [hR']; exact GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o H hHt Ω μ k a hk ha
  have hL : IsThetaFunO ψ A T (om p G) := hW.om_pres p G hG
  obtain ⟨v⟩ := GlobalTheory.Unf.Inhab.nonempty_volM D T.rank A.rank
  obtain ⟨hhaar, hfd, hvol⟩ := v.covol
  haveI := hhaar
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have key : ∀ g, IsThetaFunO ψ A T g → thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 R g := by
    intro g hg
    have hg' : IsThetaFunO ψ A T (om p⁻¹ g) := hW.om_pres _ _ hg
    have hinv : om p (om p⁻¹ g) = g := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    obtain ⟨Cg, hCg⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg
    obtain ⟨Cg', hCg'⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg'
    obtain ⟨CF, hCF⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hF
    obtain ⟨CH, hCH⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hHt
    calc thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 (om p G) (om p (om p⁻¹ g)) := by rw [hinv]
      _ = thPair v.μ v.𝓕 G (om p⁻¹ g) := GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ A T χ χ' om hW v p _ _ hG hg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => F ((o.resS T).symm (u, k w))) (om p⁻¹ g) ∂μ := by
          unfold thPair
          exact pair_swap o μ k a hk ha _ F hF.cont CF hCF _ hg'.cont Cg' hCg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (om p (fun u => F ((o.resS T).symm (u, k w)))) g ∂μ := by
          congr 1; funext w; congr 1
          rw [← GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ A T χ χ' om hW v p _ _ (hsl _) hg', hinv]
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => H ((o.resS T).symm (u, k w))) g ∂μ := by
          simp only [hHs]
      _ = thPair v.μ v.𝓕 R g := by
          rw [hR']; unfold thPair
          exact (pair_swap o μ k a hk ha _ H hHt.cont CH hCH g hg.cont Cg hCg).symm
  have hd : IsThetaFunO ψ A T (om p G - R) := GlobalTheory.WeilVacMove.isTheta_sub hL hR
  have hkd := key _ hd
  obtain ⟨CL, hCL⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hL
  obtain ⟨CR, hCR⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hR
  obtain ⟨Cd, hCd⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hd
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  have bint : ∀ f : WO A T → ℂ, Continuous f → ∀ C : ℝ, (∀ x, ‖f x‖ ≤ C) →
      Integrable (fun x => f x * star ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    intro f hf C hC
    refine (integrable_const (C * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hf.mul (continuous_star.comp hd.cont)).aestronglyMeasurable
    · rw [norm_mul, norm_star]
      exact mul_le_mul (hC x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  have h0 : ∫ x in v.𝓕, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) ∂v.μ = 0 := by
    have e : ∀ x, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) =
        om p G x * star ((om p G - R) x) - R x * star ((om p G - R) x) := by
      intro x
      rw [← sub_mul, ← Pi.sub_apply, Complex.star_def, Complex.mul_conj]
    simp only [e]
    rw [integral_sub (bint _ hL.cont CL hCL) (bint _ hR.cont CR hCR)]
    unfold thPair at hkd
    rw [hkd, sub_self]
  rw [integral_complex_ofReal] at h0
  have h1 : ∫ x in v.𝓕, Complex.normSq ((om p G - R) x) ∂v.μ = 0 := by exact_mod_cast h0
  have hnn : 0 ≤ᵐ[v.μ.restrict v.𝓕] fun x => Complex.normSq ((om p G - R) x) :=
    Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _
  have hi : Integrable (fun x => Complex.normSq ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    refine (integrable_const (Cd * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_normSq.comp hd.cont).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hCd x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hCd x))
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 h1
  have hae' : ∀ᵐ x ∂v.μ.restrict v.𝓕, (om p G - R) x = 0 :=
    hae.mono fun x hx => Complex.normSq_eq_zero.1 hx
  obtain ⟨i1, -, i3, -, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i3; haveI := i5
  have hz := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratMx D T.rank A.rank) v.μ v.𝓕 hfd (om p G - R) hd.cont
    (GlobalTheory.WeilVacMove.norm_periodic hψ hd) hae'
  have := congrFun hz u₀
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem weil_comm_superpos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  intro D ψ S A B T o χ χ' om hW F hF Ω _ μ k a hk ha p
  refine ⟨(GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o F hF).1 χ χ' om hW p, fun u₀ => ?_⟩
  obtain ⟨s, hs, hr⟩ := exists_sfinite μ a ha
  have e1 : (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) =
      fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂(μ.restrict s) := funext fun u => hr _
  rw [e1, hr]
  exact comm_sfinite o hW hF (μ.restrict s) k a hk ha.restrict p u₀

end GlobalTheory.WeilSuperpos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSourceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_commutes_superposition_slices_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  first | exact @GlobalTheory.WeilSuperpos.weil_comm_superpos | exact GlobalTheory.WeilSuperpos.weil_comm_superpos | (intros; apply GlobalTheory.WeilSuperpos.weil_comm_superpos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfCommutingProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfCommutingProduct
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CommProd

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def mulEquiv (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) : (B × A) ≃ₜ* G where
  toFun p := (p.1 : G) * p.2
  invFun g := ((e.symm g).2, (e.symm g).1)
  left_inv p := by
    have : e.symm ((p.1 : G) * p.2) = (p.2, p.1) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ p.2.2 _ p.1.2]
    simp [this]
  right_inv g := by
    change ((e.symm g).2 : G) * (e.symm g).1 = g
    rw [← hc _ (e.symm g).1.2 _ (e.symm g).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    change ((p.1 * q.1 : B) : G) * ((p.2 * q.2 : A) : G) = ((p.1 : G) * p.2) * ((q.1 : G) * q.2)
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (p.2 : G), hc _ p.2.2 _ q.1.2]
    simp only [mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (e.symm.continuous.snd).prodMk (e.symm.continuous.fst)

@[simp] theorem mulEquiv_apply (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (p : B × A) : mulEquiv A B hc e he p = (p.1 : G) * p.2 := rfl

def mulEquivSub (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) :
    (R.subgroupOf B × R.subgroupOf A) ≃ₜ* R where
  toFun p := ⟨((p.1 : B) : G) * ((p.2 : A) : G), R.mul_mem (Subgroup.mem_subgroupOf.1 p.1.2) (Subgroup.mem_subgroupOf.1 p.2.2)⟩
  invFun r :=
    have h := hR _ (e.symm r).1.2 _ (e.symm r).2.2 (by rw [← he, e.apply_symm_apply]; exact r.2)
    (⟨(e.symm r).2, Subgroup.mem_subgroupOf.2 h.2⟩, ⟨(e.symm r).1, Subgroup.mem_subgroupOf.2 h.1⟩)
  left_inv p := by
    have : e.symm (((p.1 : B) : G) * ((p.2 : A) : G)) = ((p.2 : A), (p.1 : B)) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ (p.2 : A).2 _ (p.1 : B).2]
    ext <;> simp [this]
  right_inv r := by
    apply Subtype.ext
    change ((e.symm r).2 : G) * (e.symm r).1 = r
    rw [← hc _ (e.symm r).1.2 _ (e.symm r).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    apply Subtype.ext
    change (((p.1 * q.1 : R.subgroupOf B) : B) : G) * (((p.2 * q.2 : R.subgroupOf A) : A) : G) =
      (((p.1 : B) : G) * ((p.2 : A) : G)) * (((q.1 : B) : G) * ((q.2 : A) : G))
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc ((p.2 : A) : G), hc _ (p.2 : A).2 _ (q.1 : B).2]
    simp only [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have hs : Continuous fun r : R => e.symm r := e.symm.continuous.comp continuous_subtype_val
    exact ((hs.snd).subtype_mk _).prodMk ((hs.fst).subtype_mk _)

@[simp] theorem mulEquivSub_apply (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (p : R.subgroupOf B × R.subgroupOf A) :
    (mulEquivSub A B R hc e he hR p : G) = ((p.1 : B) : G) * ((p.2 : A) : G) := rfl

end GlobalTheory.CommProd

namespace GlobalTheory.CommProd

theorem invInv : ∀ {X Y H : Type} [Group X] [Group Y] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace H] [IsTopologicalGroup X] [IsTopologicalGroup Y] [IsTopologicalGroup H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace H] [BorelSpace X] [BorelSpace Y] [BorelSpace H] [LocallyCompactSpace X]
    [LocallyCompactSpace Y] [LocallyCompactSpace H] [SecondCountableTopology X] [SecondCountableTopology Y]
    [SecondCountableTopology H] (e : (Y × X) ≃ₜ* H) (ρ : Measure Y) (ν : Measure X) (μH : Measure H),
    ρ.IsHaarMeasure → ρ.IsInvInvariant → ν.IsHaarMeasure → μH.IsInvInvariant → (ρ.prod ν).map e = μH →
    ν.IsInvInvariant := by
  intro X Y H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e ρ ν μH _ _ _ _ h
  have he : Measurable e := e.continuous.measurable
  have h1 : (ρ.prod ν.inv).map e = μH := by
    have hp : ρ.prod ν.inv = (ρ.prod ν).map (fun p => p⁻¹) := by
      rw [show (fun p : Y × X => p⁻¹) = Prod.map (·⁻¹) (·⁻¹) from rfl,
        ← Measure.map_prod_map _ _ measurable_inv measurable_inv]
      change ρ.prod ν.inv = ρ.inv.prod ν.inv
      rw [Measure.inv_eq_self ρ]
    have hc : (e ∘ fun p : Y × X => p⁻¹) = (fun q : H => q⁻¹) ∘ e := funext fun p => map_inv e p
    rw [hp, Measure.map_map he measurable_inv, hc, ← Measure.map_map measurable_inv he, h]
    exact Measure.inv_eq_self μH
  have h2 : ρ.prod ν.inv = ρ.prod ν := by
    let E := e.toHomeomorph.toMeasurableEquiv
    have hE : (E : Y × X → H) = e := rfl
    rw [← E.map_symm_map (μ := ρ.prod ν.inv), ← E.map_symm_map (μ := ρ.prod ν), hE, h1, h]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : Y)
  have hK0 : ρ K ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := ρ) hK1).ne'
  have hKt : ρ K ≠ ⊤ := hK.measure_lt_top.ne
  refine ⟨Measure.ext fun S hS => ?_⟩
  have := congrArg (fun m : Measure (Y × X) => m (K ×ˢ S)) h2
  simp only [Measure.prod_prod] at this
  exact (ENNReal.mul_right_inj hK0 hKt).1 this

theorem cutProd : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G) (he : ∀ p, e p = p.1 * p.2)
    (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (μR : Measure R) (ρ : Measure (R.subgroupOf B))
    (ν : Measure (R.subgroupOf A)) (βB : B → NNReal) (βA : A → NNReal), SFinite ρ → SFinite ν →
    (ρ.prod ν).map (mulEquivSub A B R hc e he hR) = μR →
    GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf B) ρ βB → GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf A) ν βA →
    GlobalTheory.Tw.IsCosetCutoff R μR (fun g => βB (e.symm g).2 * βA (e.symm g).1) := by
  intro G _ _ _ _ _ _ _ _ A B R hc e he hR μR ρ ν βB βA _ _ hm hB hA
  have hs : Measurable fun g : G => e.symm g := e.symm.continuous.measurable
  have hmeas : Measurable fun g : G => βB (e.symm g).2 * βA (e.symm g).1 :=
    (hB.1.comp (measurable_snd.comp hs)).mul (hA.1.comp (measurable_fst.comp hs))
  refine ⟨hmeas, fun x => ?_⟩
  set ψ := mulEquivSub A B R hc e he hR
  have hψ : Measurable ψ := ψ.continuous.measurable
  have hmx : Measurable fun r : R => ((βB (e.symm ((r : G) * x)).2 * βA (e.symm ((r : G) * x)).1 : NNReal) : ℝ≥0∞) :=
    (hmeas.comp (measurable_subtype_coe.mul_const x)).coe_nnreal_ennreal
  rw [← hm, lintegral_map hmx hψ]
  have key : ∀ p : R.subgroupOf B × R.subgroupOf A, e.symm ((ψ p : G) * x) = ((p.2 : A) * (e.symm x).1, (p.1 : B) * (e.symm x).2) := by
    intro p
    rw [Homeomorph.symm_apply_eq, he, mulEquivSub_apply]
    have hx : x = ((e.symm x).1 : G) * (e.symm x).2 := by rw [← he, e.apply_symm_apply]
    have h1 : ((p.1 : B) : G) * ((p.2 : A) : G) = ((p.2 : A) : G) * ((p.1 : B) : G) :=
      (hc _ (p.2 : A).2 _ (p.1 : B).2).symm
    have h2 : ((p.1 : B) : G) * ((e.symm x).1 : G) = ((e.symm x).1 : G) * ((p.1 : B) : G) :=
      (hc _ (e.symm x).1.2 _ (p.1 : B).2).symm
    calc ((p.1 : B) : G) * ((p.2 : A) : G) * x
        = ((p.2 : A) : G) * (((p.1 : B) : G) * ((e.symm x).1 : G)) * (e.symm x).2 := by
          rw [h1]; conv_lhs => rw [hx]
          simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [Subgroup.coe_mul, mul_assoc]
  simp only [key, ENNReal.coe_mul]
  refine (lintegral_prod _ ((hB.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_fst).mul_const _)).mul
    (hA.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_snd).mul_const _))).aemeasurable).trans ?_
  simp only [Pi.mul_apply, Function.comp_apply, lintegral_const_mul' _ _ ENNReal.coe_ne_top, hA.2, mul_one, hB.2]

end GlobalTheory.CommProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.CommProd in
theorem GlobalTheory.CommProd.quot_vanish_of_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (R : Set G) → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → (∃ e : (A × B) ≃ₜ G, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) → ∀ (μR : Measure R) (μG : Measure G) (ρ : Measure (R.subgroupOf B)) (μ : Measure B), μR.IsHaarMeasure → μR.IsInvInvariant → μG.IsHaarMeasure → ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → ∀ (f : G → ℂ) (z : ℂ), IsQuotIntL1 μR μG f z → (∀ a ∈ A, IsQuotIntL1 ρ μ (fun b => f (a * b.1)) 0) → z = 0 := by
  intro G _ _ _ _ _ _ _ _ A B R hA hB hR hc ⟨e, he⟩ hdec μR μG ρ μ _ _ _ _ _ _ f z hf hz
  have : LocallyCompactSpace A := hA.locallyCompactSpace
  have : LocallyCompactSpace B := hB.locallyCompactSpace
  have hRA : IsClosed ((R.subgroupOf A : Subgroup A) : Set A) := hR.preimage continuous_subtype_val
  have hRB : IsClosed ((R.subgroupOf B : Subgroup B) : Set B) := hR.preimage continuous_subtype_val
  have : LocallyCompactSpace (R.subgroupOf A) := hRA.locallyCompactSpace
  have : LocallyCompactSpace (R.subgroupOf B) := hRB.locallyCompactSpace
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  let φ := mulEquiv A B hc e he
  let ψ := mulEquivSub A B R hc e he hdec
  obtain ⟨μA, hμA, hG⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq φ μ μG
  obtain ⟨ν, hν, hRm⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq ψ ρ μR
  have : ν.IsInvInvariant := invInv ψ ρ ν μR inferInstance inferInstance hν inferInstance hRm
  obtain ⟨βB, -, hβB⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ρ) hRB
  obtain ⟨βA, -, hβA⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ν) hRA
  have hβ := cutProd G A B R hc e he hdec μR ρ ν βB βA inferInstance inferInstance hRm hβB hβA
  obtain ⟨hi, rfl⟩ := hf.cutoff hβ
  have hφs : ∀ p : B × A, e.symm (φ p) = (p.2, p.1) := fun p => by
    rw [Homeomorph.symm_apply_eq, he, mulEquiv_apply, hc _ p.2.2 _ p.1.2]
  have hme : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [← hG] at hi ⊢
  rw [hme.integral_map]
  rw [hme.integrable_map_iff] at hi
  refine (integral_prod_symm _ hi).trans ?_
  have hin : ∀ a : A, ∫ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) ∂μ = 0 := by
    intro a
    obtain ⟨-, h0⟩ := (hz a a.2).cutoff hβB
    have e1 : ∀ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) =
        (βA a : ℝ) • ((βB b : ℝ) • f (a * b)) := fun b => by
      simp only [Function.comp_apply, hφs, mulEquiv_apply, NNReal.coe_mul, smul_smul]
      rw [show φ (b, a) = (b : G) * a from rfl, hc _ a.2 _ b.2, mul_comm (βB b : ℝ)]
    simp only [e1, integral_smul, ← h0, smul_zero]
  exact (integral_congr_ae (Filter.Eventually.of_forall hin)).trans (integral_zero _ _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfCommutingProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientIntegral_vanish_of_commutingProduct : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (R : Set G) → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → (∃ e : (A × B) ≃ₜ G, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) → ∀ (μR : Measure R) (μG : Measure G) (ρ : Measure (R.subgroupOf B)) (μ : Measure B), μR.IsHaarMeasure → μR.IsInvInvariant → μG.IsHaarMeasure → ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → ∀ (f : G → ℂ) (z : ℂ), IsQuotIntL1 μR μG f z → (∀ a ∈ A, IsQuotIntL1 ρ μ (fun b => f (a * b.1)) 0) → z = 0 := by
  first | exact @GlobalTheory.CommProd.quot_vanish_of_prod | exact GlobalTheory.CommProd.quot_vanish_of_prod | (intros; apply GlobalTheory.CommProd.quot_vanish_of_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurProductTypingsAgreeThetaChain
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurProductTypingsAgreeThetaChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.IPDictPf

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem isInnerProduct_of_isMet' (t : T) (k : ℕ) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) (x y : (stY R t k).CC (comR R t)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t k (PiTensorProduct.lift.symm x.1) (PiTensorProduct.lift.symm y.1) (ip y x) := by
  intro v v'
  have h1 := hm.integ y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  have h2 := hm.schur y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  rw [hm.pure v' v] at h2
  have e : (fun g => star ((PiTensorProduct.lift.symm x.1) v g) * (PiTensorProduct.lift.symm y.1) v' g) =
      fun g => PiLocalization₂.val y (PiTensorProduct.tprod ℂ v') g * conj (PiLocalization₂.val x (PiTensorProduct.tprod ℂ v) g) := by
    funext g; rw [mul_comm]; rfl
  refine ⟨?_, ?_⟩
  · exact (congrArg (fun F => IntegrableOn F (stY R t k).fd (stY R t k).ν) e).mpr h1
  · exact (congrArg (fun F : GA D (stY R t k).V → ℂ => ∫ g in (stY R t k).fd, F g ∂(stY R t k).ν) e).trans h2

theorem exists_tprod_ne {k : ℕ} (w : SmT (R.MY k)) (hw : w ≠ 0) : ∃ v : (R.MY k).Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra h
  push_neg at h
  have hid : (LinearMap.id : SmT (R.MY k) →ₗ[ℂ] SmT (R.MY k)) = 0 :=
    PiTensorProduct.ext (MultilinearMap.ext fun v => by simpa using h v)
  exact hw (by simpa using LinearMap.congr_fun hid w)

theorem exists_vec (hC : R.IsChain) (t : T) {k : ℕ} (hk : k < D.R.m) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) :
    ∃ v : (R.MY k).Vec, ∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ ≠ 0 := by
  have hw : ∃ w : SmT (R.MY k), w ≠ 0 := by
    by_cases hkk : k + 1 < D.R.m
    · by_contra h
      push_neg at h
      exact (hC.ItY t k hkk).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItY k φ x))
    · obtain rfl : k = D.R.m - 1 := by omega
      by_contra h
      push_neg at h
      exact (hC.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun x => by simpa using h (R.ItX φ x))
  obtain ⟨w, hw⟩ := hw
  obtain ⟨v, hv⟩ := exists_tprod_ne R w hw
  refine ⟨v, fun h0 => ?_⟩
  have hp := hm.posD (PiTensorProduct.tprod ℂ v) hv
  rw [hm.pure v v] at hp
  change 0 < (∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ).re at hp
  rw [h0] at hp
  simp at hp

theorem ipDict (R : RealDat D A Ks) (F : Face D A) (hG : Given R F) : IPDict R := by
  intro t k hk ipD ip hm x y a
  obtain ⟨v, hv⟩ := exists_vec R hG.core.chain t hk hm
  exact ⟨fun h => hasPeterssonInner_unique _ _ _ _ _ v hv h (isInnerProduct_of_isMet' R t k hm x y), fun h => h ▸ isInnerProduct_of_isMet' R t k hm x y⟩

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → IPDict R := fun R F hG => ipDict R F hG

end GlobalTheory.ChainTw.IPDictPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurProductTypingsAgreeThetaChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurProduct_typings_agree_thetaChain : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → IPDict R := by
  first | exact @GlobalTheory.ChainTw.IPDictPf.main | exact GlobalTheory.ChainTw.IPDictPf.main | (intros; apply GlobalTheory.ChainTw.IPDictPf.main <;> assumption)
end
end

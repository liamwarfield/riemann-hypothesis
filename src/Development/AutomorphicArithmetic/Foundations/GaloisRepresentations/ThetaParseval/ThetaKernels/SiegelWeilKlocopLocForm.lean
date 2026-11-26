module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNM
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbKey
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpExOfTAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.NdZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDegCut

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocForm
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.T_lin (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (a : ℂ) (Φ Φ' : d.Fn) : d.T (a • Φ + Φ') = a • d.T Φ + d.T Φ' := by
  funext X
  have h : ∀ p : (d.κ → AF F) × (d.κ → AF F), schr d.B.ψ p (a • Φ + Φ') = a • schr d.B.ψ p Φ + schr d.B.ψ p Φ' :=
    fun p => by
      funext x
      simp only [schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Darboux.rho, h, map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens_cancel {Ψ : d.MF} (hΨ : d.IsAwayW w Ψ) (h0 : Ψ ≠ 0) {g g' : d.LF}
    (h : R.tens w g Ψ = R.tens w g' Ψ) : g = g' := by
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (funext hc)
  funext u
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
  have := congrFun h (X₀ + Z)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hZ3, hΨ X₀ Z hZ1 hZ2] at this
  exact mul_right_cancel₀ hX₀ this
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.exists_adm (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {Ψ : d.MF} (hΨ : R.GoodAway w Ψ) {f : d.LF} (hf : IsSw f) :
    ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ := (hT.1 F E σ d).2.1 _ (hΨ.2.2 f hf)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_one (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) : ∀ f, IsSw f → L 1 f = f := by
  intro f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e := (hL 1 f hf).2 Ψ hΨ.1 Φ hΦ hT'
  rw [map_one, map_one, Module.End.one_apply, hT'] at e
  exact (R.tens_cancel hΨ.1 hΨ.2.1 e).symm
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_mul (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∀ y y' f, IsSw f → L (y * y') f = L y (L y' f) := by
  intro y y' f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y' f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := (hL y (L y' f) (hL y' f hf).1).2 Ψ hΨ.1 _ (d.om_sch _ Φ hΦ) e1
  have e3 := (hL (y * y') f hf).2 Ψ hΨ.1 Φ hΦ hT'
  rw [map_mul, map_mul, Module.End.mul_apply] at e3
  exact R.tens_cancel hΨ.1 hΨ.2.1 (e3.symm.trans e2)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_lin (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∀ y (a : ℂ) f g, IsSw f → IsSw g → L y (a • f + g) = a • L y f + L y g := by
  intro y a f g hf hg
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φf, hΦf, hTf⟩ := R.exists_adm hT hΨ hf
  obtain ⟨Φg, hΦg, hTg⟩ := R.exists_adm hT hΨ hg
  have hΦ : a • Φf + Φg ∈ d.sch := d.sch.add_mem (d.sch.smul_mem a hΦf) hΦg
  have hTΦ : d.T (a • Φf + Φg) = R.tens w (a • f + g) Ψ := by
    rw [d.T_lin, hTf, hTg]
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e := (hL y (a • f + g) (isSw_lin a hf hg)).2 Ψ hΨ.1 _ hΦ hTΦ
  have ef := (hL y f hf).2 Ψ hΨ.1 Φf hΦf hTf
  have eg := (hL y g hg).2 Ψ hΨ.1 Φg hΦg hTg
  rw [map_add (f := _), map_smul, d.T_lin, ef, eg] at e
  apply R.tens_cancel hΨ.1 hΨ.2.1
  rw [← e]
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_nU (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b → ∀ f, IsSw f →
      L y f = fun u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u := by
  intro y b hb hy f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := ((R.stepN w hT y b hb hy).2 Ψ hΨ.1).2 f hf Φ hΦ hT'
  exact R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_mM (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ c : Matrix (Fin d.n) (Fin d.n) ℂ → ℂ, (∀ a, IsUnit a.det → c a ≠ 0) ∧
      ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a → ∀ f, IsSw f →
        L y f = fun u => c a * f (Matrix.of u * a) := by
  classical
  have hinj : ∀ y y' : GR d.n, mR y = mR y' → y = y' := fun y y' h => Subtype.ext (Units.ext h)
  refine ⟨fun a => if h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a then
    (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose else 1, fun a ha => ?_, fun y a ha hy f hf => ?_⟩
  · by_cases h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a
    · dsimp only
      rw [dif_pos h]
      exact (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose_spec.1
    · dsimp only
      rw [dite_eq_right h]
      exact one_ne_zero
  · have h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a := ⟨ha, y, hy⟩
    have hy0 : h.2.choose = y := hinj _ _ (h.2.choose_spec.trans hy.symm)
    simp only [dif_pos h]
    have hs := (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose_spec.2
    rw [← hy0]
    obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e1 := (hL h.2.choose f hf).2 Ψ hΨ.1 Φ hΦ hT'
    have e2 := (hs.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    exact R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2)
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzEqFlatK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
theorem phz_eq_flat_k {s₁ z : ℂ} {f : d.G → ℂ} : _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z = GlobalTheory.ThK.Dbl.flat d.a f s₁ z := by
  funext x
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k, GlobalTheory.ThK.Dbl.flat, _root_.PositivityTheory.SiegelWeilFormula.kunf.ht_eq_k]
theorem phz_law_k {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    Law d.χ (z - s₁ + (s₁ + (d.n : ℂ) / 2)) (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_eq_flat_k]
  exact Law.flat hf.law d.ok.hgt (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d) z
theorem phz_par_k {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {p : d.G} {t : GL (Fin d.n) (AE F E)}
    (hp : IsPar p t) (ht : Matrix.GeneralLinearGroup.det t = 1) (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (p * g) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z g := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_law_k hf z p t g hp, ht, map_one, map_one]
  simp
theorem phz_rat_k {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {p : d.G} (hp : p ∈ par2 σ d.Y)
    (hr : p ∈ rat2 σ d.Y) (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (p * g) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z g :=
  (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_law_k hf z).rat d.ok.hecke hp hr g
theorem key_id_k {nb : nA σ d.Y d.b → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb : IsNMap d.b nb)
    (hnb' : IsNMap L.b nb') {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (h : G2 σ L.Y) (β : nA σ d.Y d.b) (u : Fin L.n → AE F E)
    (x : d.G) : ∃ p t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
      L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.key_id_pf_k L hnb hnb' hU h β u x
theorem tr_sub_k {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * β.1) = Matrix.trace (T'.1.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β).1) := by
  obtain ⟨h0, h1⟩ := hT
  have hout : ∀ i, i ∉ Set.range L.em → i = L.i₀ := fun i hi => by
    by_contra h
    exact hi ((L.rng i).1 h)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, h1, Matrix.submatrix_apply]
  symm
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun a => ?_)
  · rw [hout i hi]
    simp [(h0 _).1]
  · refine Fintype.sum_of_injective L.em L.inj _ _ (fun k hk => ?_) (fun b => rfl)
    rw [hout k hk]
    simp [(h0 _).2]
theorem cos_bij_k : ∃ e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ q', ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
    _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 = p * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.cos_bij_pf_k L
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopTop
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAssemble
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.ok_of_conj (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {y y' : GR d.n} {x₁ x₂ : d.G} {A₁ A₂ A' : d.LF → d.LF} {B₁ B₂ : d.MF → d.MF}
    (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂) (h' : R.StepOK w (R.ι w y') A' id)
    (hy : R.ι w y = x₁ * R.ι w y' * x₂) (h1 : x₁ * x₂ = 1) : R.OkY w y := by
  have hsch := d.om_sch
  have hc := R.step_comp w hsch (R.step_comp w hsch h₁ h') h₂
  have h0 := R.step_comp w hsch h₁ h₂
  intro f hf
  by_cases hf0 : ∀ u, f u = 0
  · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
    have : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hf0])
    subst this
    rw [map_zero, d.T_zero]
    funext X
    simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
  · push Not at hf0
    obtain ⟨u₀, hu₀⟩ := hf0
    by_cases hex : ∃ κ : ℂ, κ ≠ 0 ∧ A₁ (A₂ f) = κ • f
    · obtain ⟨κ, hκ, hA⟩ := hex
      refine ⟨κ⁻¹ • A₁ (A' (A₂ f)), ?_, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      · obtain ⟨φ, hφ⟩ := hc.1 f hf
        refine ⟨κ⁻¹ • φ, ?_⟩
        funext u
        have := congrFun hφ u
        simp only [Function.comp_apply] at this
        simp [this]
      · have e := (hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
        have hBaway := (h0.2 Ψ hΨ).1
        have hB : ∀ X, B₁ (B₂ Ψ) X = κ⁻¹ * Ψ X := by
          intro X
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
          have h2 := congrFun e0 (X + Z)
          have h3 := hΨ X Z hZ1 hZ2
          have h4 := hBaway X Z hZ1 hZ2
          simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, hZ3, hA, Pi.smul_apply, smul_eq_mul] at h2 h4
          rw [h3, h4] at h2
          rw [eq_inv_mul_iff_mul_eq₀ hκ]
          apply mul_left_cancel₀ hu₀
          linear_combination -h2
        rw [hy, e]
        funext X
        simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hB]
        ring
    · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      have hΨ0 : ∀ X, Ψ X = 0 := by
        by_contra hne
        push Not at hne
        obtain ⟨X₀, hX₀⟩ := hne
        have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
        have hBaway := (h0.2 Ψ hΨ).1
        have key : ∀ u, f u * Ψ X₀ = A₁ (A₂ f) u * B₁ (B₂ Ψ) X₀ := by
          intro u
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
          have h2 := congrFun e0 (X₀ + Z)
          have h3 := hΨ X₀ Z hZ1 hZ2
          have h4 := hBaway X₀ Z hZ1 hZ2
          simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, hZ3] at h2 h4
          rw [h3, h4] at h2
          exact h2
        have hB0 : B₁ (B₂ Ψ) X₀ ≠ 0 := by
          intro h0'
          have := key u₀
          rw [h0', mul_zero] at this
          exact mul_ne_zero hu₀ hX₀ this
        apply hex
        refine ⟨Ψ X₀ / B₁ (B₂ Ψ) X₀, div_ne_zero hX₀ hB0, ?_⟩
        funext u
        have := key u
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, eq_div_iff hB0]
        linear_combination -this
      have : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hΨ0])
      subst this
      rw [map_zero, d.T_zero]
      funext X
      simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hΨ0]
end RD
theorem locOpEx_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k := by
  intro F E _ _ _ _ _ σ d R w
  refine ⟨_, R.isLocOp_of_ok w fun y => ?_⟩
  have hsch := d.om_sch
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  obtain ⟨C, s, B, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  have okN : ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b → R.OkY w y :=
    fun y b hb hy => R.ok_of_step w (R.stepN w hT y b hb hy)
  have okM : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = Glob.mM a → R.OkY w y := by
    intro y a ha hy
    obtain ⟨c, -, hc⟩ := R.stepM w hT y a ha hy
    exact R.ok_of_step w hc
  have okB : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = Glob.nbar c → R.OkY w y := by
    intro y c hc hy
    obtain ⟨y', x, hx, hy', hrel⟩ := R.nbar_conj' w hw₀ y c hc hy
    have hW3 := R.step_comp w hsch (R.step_comp w hsch hW hW) hW
    exact R.ok_of_conj w hT hW3 hW (R.stepN w hT y' x hx hy') hrel (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀)
  obtain ⟨y1, y2, y3, y4, hy, ⟨t, ht⟩, ⟨c, hc, hc2⟩, ⟨a, ha, ha2⟩, ⟨b, hb, hb2⟩⟩ := PositivityTheory.Rg.Sw.Glob.decomp d.n y
  rw [hy]
  exact R.ok_mul w hsch (R.ok_mul w hsch (R.ok_mul w hsch (okN y1 _ (herm_smul_one' t) ht) (okB y2 c hc hc2))
    (okM y3 a ha ha2)) (okN y4 b hb hb2)
end PositivityTheory.SiegelWeilFormula
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.SiegelWeilFormula
theorem locOpEx_of_tAll_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k := _root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds
end PositivityTheory.SiegelWeilFormula
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FirstOrbitParabolicLeft
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C5 PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
set_option linter.unusedSectionVars false
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
variable (L) in
structure Hyp_k (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)
  cf : ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 A'
  δ0 : δ ≠ 0
variable (L) in
abbrev Cr_k : Type := {c : (Fin L.n → AE F E) × AF F // c.1 ∈ L.ratV ∧ c.2 ∈ (algebraMap F (AF F)).range}
variable (L) in
def Fix_k (x : d.G) : Prop :=
  ∀ k, inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)
theorem fix_mul_k {x y : d.G} (hx : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L x) (hy : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L y) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (x * y) := by
  intro k
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)]
  · rw [hy, Matrix.one_apply_eq, mul_one]; exact hx k
  · intro j _ hj; rw [hy j, Matrix.one_apply_ne hj, mul_zero]
  · simp
theorem fix_inv_k {x : d.G} (hx : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L x) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L x⁻¹ := by
  intro k
  have h1 := congrFun (congrFun (GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul d.b x) k) (Sum.inl L.i₀)
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)] at h1
  · rw [hx, Matrix.one_apply_eq, mul_one] at h1; exact h1
  · intro j _ hj; rw [hx j, Matrix.one_apply_ne hj, mul_zero]
  · simp
theorem fix_j_k (g : G2 σ L.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (L.j g) := by
  intro k
  exact (L.j_out g (Sum.inl L.i₀) (by simp) k).2
theorem first_orbit_parabolic_left {p g : d.G} (hp : p ∈ par2 σ d.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (p * g) ↔ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L g := by
  constructor
  · intro h1
    have := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_parabolic_mul L ((par2 σ d.Y).inv_mem hp) h1
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_parabolic_mul L hp
theorem not_first_orbit_weyl (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {g : d.G} (hg : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L g) : ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (w₁ * g) := by
  intro hS
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  have h1 := hS L.i₀
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)] at h1
  · rw [hg, Matrix.one_apply_eq, mul_one, hW] at h1
    simp [Matrix.single_apply, Matrix.one_apply] at h1
    exact hb (kfour.inclR_injective (F := F) (by rw [h1, map_zero]))
  · intro j _ hj; rw [hg j, Matrix.one_apply_ne hj, mul_zero]
  · simp
theorem out_mk_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (γ : rat2 σ d.Y) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ γ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = p * γ.1 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k γ
theorem mk_eq_mk_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {γ γ' : rat2 σ d.Y} :
    (Quotient.mk _ γ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = Quotient.mk _ γ' ↔ γ'.1 * γ.1⁻¹ ∈ par2 σ d.Y := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp
theorem rep_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q ∈ rat2 σ d.Y := (Quotient.out q).2
theorem mk_rep_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) : (Quotient.mk _ ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k d q⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = q := Quotient.out_eq q
theorem weyl_commutes_embedding (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (g : G2 σ L.Y) : w₁ * L.j g = L.j g * w₁ := by
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  apply kunf.inFrame_injective d.b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul]
  set W := inFrame d.b w₁
  set J := inFrame d.b (L.j g)
  have hJ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.pad_j_k L g
  let P : Fin d.n ⊕ Fin d.n → Prop := fun l => l = Sum.inl L.i₀ ∨ l = Sum.inr L.i₀
  have hWo : ∀ r c, ¬ (P r ∧ P c) → (W - 1) r c = 0 := by
    intro r c hrc
    rw [Matrix.sub_apply, hW]
    simp only [P, not_and_or] at hrc
    rcases hrc with hr | hr <;> push_neg at hr <;>
      simp [Matrix.single_apply, Matrix.one_apply, hr.1, hr.2, Ne.symm hr.1, Ne.symm hr.2]
  have hJo : ∀ r c, (P r ∨ P c) → (J - 1) r c = 0 := by
    intro r c hrc
    rw [Matrix.sub_apply, sub_eq_zero]
    rcases hrc with (h | h) | (h | h)
    · exact hJ r c (Or.inl h)
    · exact hJ r c (Or.inr (Or.inl h))
    · exact hJ r c (Or.inr (Or.inr (Or.inl h)))
    · exact hJ r c (Or.inr (Or.inr (Or.inr h)))
  have e1 : (W - 1) * (J - 1) = 0 :=
    mul_eq_zero_of_supp P (fun r l hl => hWo r l fun h => hl h.2) (fun l c hl => hJo l c (Or.inl hl))
  have e2 : (J - 1) * (W - 1) = 0 :=
    mul_eq_zero_of_supp (fun l => ¬ P l) (fun r l hl => hJo r l (Or.inr (not_not.1 hl))) (fun l c hl => hWo l c fun h => hl h.1)
  have eW : W = 1 + (W - 1) := by abel
  have eJ : J = 1 + (J - 1) := by abel
  rw [eW, eJ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e1, e2]
  abel
theorem uA_neg_mul_k (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u = 1 := by
  have := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k L (-u) u
  simp only [neg_add_cancel] at this
  rw [show _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u = _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u from rfl, this]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k]
theorem cM_frame_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ)) := by
  obtain ⟨A', hA'⟩ := h.cf c
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have h2 := kunf.frame_eq hε (cM c)
  rw [hA'] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  have h1 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ * A'.map (cA σ) = 1 := (Matrix.fromBlocks_inj.1 h2).2.1
  have h1' : A'.map (cA σ) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ = 1 := mul_eq_one_comm.1 h1
  have hinv : (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ = 1 := by rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.uA_neg_mul_k, Matrix.transpose_one]
  have e : A'.map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ := by
    calc A'.map (cA σ) = A'.map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ) := by rw [hinv, Matrix.mul_one]
      _ = (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A' = (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ) := by
    rw [← e, Matrix.map_map]
    ext i j
    simp [cA_inv' hσ]
  rw [hA', e2]
theorem fix_cM'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (cM c) := by
  intro k
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  rcases k with k | k
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L]
  · simp
theorem cM_rat'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {c : (Fin L.n → AE F E) × AF F} (hu : c.1 ∈ L.ratV)
    (ha : c.2 ∈ (algebraMap F (AF F)).range) : cM c ∈ rat2 σ d.Y := by
  obtain ⟨u₀, hu₀⟩ := ComplexParameterFamilyContinuity.mem_ratVec.1 hu
  obtain ⟨a₀, ha₀⟩ := ha
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u₀ j))
    (Matrix.single L.i₀ L.i₀ (a₀ • δ)) 0 ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (-u₀ j))ᵀ.map σ)) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h, ← hu₀, ← ha₀, Afc.incM_fromBlocks, kfour.incM_zero]
  congr 1
  · ext i k
    simp [incM, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, GlobalTheory.ThK.incV, Matrix.single_apply, Matrix.one_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · ext i k
    simp only [incM, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.map_apply, Matrix.single_apply]
    split_ifs
    · show (algebraMap F (AF F) a₀) • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (a₀ • δ)
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        ← Algebra.algebraMap_eq_smul_one]
    · simp
  · ext i k
    have cA_inclR (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) =
        (1 : AF F) ⊗ₜ[F] σ x
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    simp [incM, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, GlobalTheory.ThK.incV, Matrix.single_apply, Matrix.one_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [cA_inclR]
theorem emS_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    (inFrame d.b (cM c)).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = 1 := by
  ext r r'
  rcases r with k | k <;> rcases r' with k' | k' <;>
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L, L.inj.eq_iff,
      Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L _)] <;> split_ifs <;> simp
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepTop
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCut
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem nbRat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) :
    ∀ β ∈ nF σ d.Y d.b, nb β ∈ rat2 σ d.Y :=
  fun β hβ => kfour.nb_rat hc.1 β hβ
def Bj_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (j : ℕ) (g : d.G) : ℂ :=
  iteratedDeriv j (Ê · g) (s0 d.m d.n) - iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * (2 * d.I Φ g)
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDeg
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem deg_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0)
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    (x : d.G) : fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  set s := s0 d.m d.n with hsdef
  set A : d.G → ℂ := fun g => iteratedDeriv j (Ê · g) s with hAdef
  have hAc : Continuous A := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  have hB : _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) s * 2)) • d.I Φ + A := by
    funext g; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, hAdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hfcB : ∀ x', fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x' =
      fc d.B.ψ d.b nb lam 𝓖 A T x' - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x') := by
    intro x'
    rw [hB, (_root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d hc T x').1 _ _ _ hIc hAc hIi hAi]; ring
  let w : InfinitePlace F := Classical.arbitrary _
  obtain ⟨y, hy⟩ := dilEx d.n (Pi.single L.i₀ 1) 1
  obtain ⟨pp, qq, e, hpq, hhol⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.holA_k H R hmn hΦ hv hE w j hj hlow
  obtain ⟨hlawA, huA⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.holCoef_k H R L w hc hT A hAc hAi pp qq e hpq hhol
  obtain ⟨uM, ν, 𝓤, hu⟩ := (H.uEx F E σ d R L).1
  obtain ⟨nb', lam', 𝓖', hc'⟩ := H.coefEx F E σ L.sd
  obtain ⟨t', hct⟩ := H.cTSplit F E σ d R L _ _ hsec hEis
  have hspl : ∀ z : ℂ, t' < z.re → ∃ c₂ : d.G → ℂ,
      (∀ x, _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x = _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c₂ x) ∧
      ∀ x, c₂ (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c₂ x := by
    intro z hz
    obtain ⟨c₂, h1, h2⟩ := hct z hz nb lam 𝓖 hc nb' lam' 𝓖' hc' uM ν 𝓤 hu T T' hT
    exact ⟨c₂, h1, fun x => h2 w 1 y x hy⟩
  let c2 : ℂ → d.G → ℂ := fun z => if h : t' < z.re then Classical.choose (hspl z h) else 0
  have hc2 : ∀ z : ℂ, t' < z.re → (∀ x, _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x =
      _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c2 z x) ∧
      ∀ x, c2 z (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c2 z x := by
    intro z hz
    simp only [c2, dif_pos hz]
    exact Classical.choose_spec (hspl z hz)
  have havg_smul : ∀ (c : ℂ) (φ : d.G → ℂ) x', _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (fun g => c * φ g) T x' =
      c * _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 φ T x' := by
    intro c φ x'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc, mul_assoc]
    simp only [integral_const_mul]
  have hhol1 := _root_.PositivityTheory.SiegelWeilFormula.AStep.avgHol_k H L hE hc T hT hu
  have hsep := lawSep U p (max t t') s j (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x)
    (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T (R.ι w y * x))
    (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x) (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x))
    (fun z => c2 z x) (fun z => c2 z (R.ι w y * x)) (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)
    (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x)) (d.n : ℂ) (-2) hUo hR hs hp hj (hhol1 x).1 (hhol1 _).1
    (fun i hi => by
      rw [(hhol1 x).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc])
    (fun i hi => by
      rw [(hhol1 _).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 x])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 _])
    (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT x) (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT _)
    (fun z hz => by
      rw [(hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).2 x]
      congr 1; push_cast; ring_nf)
  have havgA : ∀ x', iteratedDeriv j (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x') s = fc d.B.ψ d.b nb lam 𝓖 A T x' := by
    intro x'
    rw [(hhol1 x').2 j]
    show _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 A T x' = _
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, huA uM ν 𝓤 hu, setIntegral_const]
    simp [Measure.real, hu.2.2.2]
  rw [havgA, havgA] at hsep
  have hth : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x) = Complex.exp (d.m : ℂ) * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x := by
    have := valLaw (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x)
      (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x)) 0 (d.n : ℂ) 2 s _ _
      (fun z _ => by rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneLaw_k H R L hΦ w hc' T' 1 y hy z x]; congr 1; push_cast; ring_nf)
      (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT x) (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT _)
    have e2 : (d.n : ℂ) + 2 * s = d.m := by rw [hsdef, s0]; ring
    rw [e2] at this
    linear_combination this / 2
  have hA1 := hlawA 1 y hy x
  rw [Complex.ofReal_one, one_mul] at hA1
  rw [hfcB x]
  rw [hA1, hth] at hsep
  have e3 : (d.n : ℂ) + -2 * s = ((2 * d.n - d.m : ℕ) : ℂ) := by
    have h2 : ((2 * d.n - d.m : ℕ) : ℂ) = 2 * (d.n : ℂ) - d.m := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [h2, hsdef, s0]; ring
  rw [e3] at hsep
  have hne := exp_ne_of_lt hmn
  have key : (Complex.exp ((2 * d.n - d.m : ℕ) : ℂ) - Complex.exp (d.m : ℂ)) *
      (fc d.B.ψ d.b nb lam 𝓖 A T x - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)) = 0 := by
    linear_combination -hsep
  rcases mul_eq_zero.1 key with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ndZero_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n))
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} (hT : IsND T) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hL : (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ∈ d.lamSet := ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d _ hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  have hLI : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = 0 := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x]; exact (H.orbRes F E σ d).1 hmn T hT _
  have hB : _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) • d.I Φ +
      (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) := by
    funext g; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have h1 := hadd (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) (d.I Φ) (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n))
    hIc hAc hIi hAi
  rw [hB, h1, hLI, mul_zero, zero_add, ← hComm _ hs j]
  obtain ⟨t', ht'⟩ := H.unfold F E σ d _ _ hsec hEis
  obtain ⟨ε, w, hw, -⟩ := (H.auxEx F E σ d).2.1
  have hWL := H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x
  rw [zero_mul] at hWL
  have := ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x)
    (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t')
    (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj
  · rw [this, mul_zero]
  · intro z hz
    have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
    have h2 := (ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT
    rw [← h2]
    simp only [fc, h1, mul_assoc]
    exact integral_const_mul _ _
theorem stepJ_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g = 0 := by
  obtain ⟨nb, lam, 𝓖, hc⟩ := H.coefEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hBc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) :=
    (famCont U Ê hUo hd hcont _ hs j).sub (continuous_const.mul (continuous_const.mul hIc))
  have hBr : ∀ γ ∈ rat2 σ d.Y, ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j (γ * g) = _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g := fun γ hγ g => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j, hIi γ hγ g]
  have hz := H.fourierZero F E σ d nb lam 𝓖 hc (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) hBc (fun β hβ g => hBr _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.nbRat_k d hc β hβ) g) ?_
  · intro g; exact congrFun hz g
  · intro T g
    by_cases hT : IsND T
    · exact _root_.PositivityTheory.SiegelWeilFormula.AStep.ndZero_k H R hmn hΦ hv hE j hj hc hT g
    · obtain ⟨γ, hγ, T₀, T', hsub, hfc⟩ := (H.fcConj F E σ d L nb lam 𝓖 hc).1 T hT
      rw [hfc _ hBc hBr g]
      exact _root_.PositivityTheory.SiegelWeilFormula.AStep.deg_k H R L R' hmn hIH hΦ hv hE j hj hlow hc hsub _
theorem step_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) : _root_.PositivityTheory.SiegelWeilFormula.Step_k := by
  intro F E _ _ _ _ _ σ d R L R' hmn hIH Φ hΦ hv x
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d _ _ hsec (s0 d.m d.n)
  have hall : ∀ j ≤ p.rootMultiplicity (s0 d.m d.n), ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      refine _root_.PositivityTheory.SiegelWeilFormula.AStep.stepJ_k H R L R' hmn hIH hΦ hv hE j hj fun i hi g => ?_
      have := ih i hi (hi.le.trans hj) g
      simpa only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, pderiv_lt p _ i (lt_of_lt_of_le hi hj), zero_mul, sub_zero] using this
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  refine wrap U p (Ê · x) (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) t _ _ hUo hR hs hp (hd x)
    (fun z hz => (hfar z hz).2 x) (fun j hj => ?_) ?_
  · have := hall j hj.le x
    simpa only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, pderiv_lt p _ j hj, zero_mul, sub_zero] using this
  · exact sub_eq_zero.1 (hall _ le_rfl x)
theorem stepOf_k : _root_.PositivityTheory.SiegelWeilFormula.StepOf_k := fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 =>
  _root_.PositivityTheory.SiegelWeilFormula.AStep.step_k ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

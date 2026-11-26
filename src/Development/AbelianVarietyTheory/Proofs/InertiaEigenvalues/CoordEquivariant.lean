module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompletionFrameOfLatticeStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiGradedPieceIsoTwistedOC
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiGradedPieceIsoTwistedOC
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.Graded

variable {l : ℕ} [Fact l.Prime]

theorem mem_OC_iff (y : PadicComplex l) : y ∈ PadicComplexInt l ↔ ‖y‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff]
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff (L := PadicComplex l) (Γ₀ := NNReal)).symm

theorem norm_OC (y : OC l) : ‖(y : PadicComplex l)‖ ≤ 1 := (mem_OC_iff _).1 y.2

theorem norm_alg (x : ℚ_[l]) : ‖algebraMap ℚ_[l] (PadicComplex l) x‖ = ‖x‖ := by
  exact norm_algebraMap' _ x

theorem norm_lpow (m : ℕ) : ‖(l : PadicComplex l) ^ m‖ = (l : ℝ) ^ (-(m : ℤ)) := by
  have h := norm_alg ((l : ℚ_[l]) ^ m)
  rw [map_pow, map_natCast] at h
  rw [h, Padic.norm_p_pow]

theorem eq_zero_of_norm_le (y : PadicComplex l) (h : ∀ m : ℕ, ‖y‖ ≤ 2 * (l : ℝ) ^ (-(m : ℤ))) :
    y = 0 := by
  by_contra hy
  have hpos : 0 < ‖y‖ / 2 := by positivity
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
  have := h m
  rw [zpow_neg, zpow_natCast, ← inv_pow] at this
  linarith

theorem theta_alg (θ : Ainf l →+* OC l) (z : ℤ_[l]) :
    ((θ (algebraMap ℤ_[l] (Ainf l) z) : OC l) : PadicComplex l) = zC z := by
  rw [← sub_eq_zero]
  apply eq_zero_of_norm_le
  intro m
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m z)
  have hz : z = (z.appr m : ℤ_[l]) + w * (l : ℤ_[l]) ^ m := by rw [hw]; ring
  have h1 : ((θ (algebraMap ℤ_[l] (Ainf l) z) : OC l) : PadicComplex l) - zC z =
      ((θ (algebraMap ℤ_[l] (Ainf l) w) : OC l) : PadicComplex l) * (l : PadicComplex l) ^ m -
        zC w * (l : PadicComplex l) ^ m := by
    generalize z.appr m = n at hz
    subst hz
    simp [zC]
  have h2 : ‖zC w‖ ≤ 1 := by rw [zC, norm_alg]; exact w.2
  have h3 := norm_OC (θ (algebraMap ℤ_[l] (Ainf l) w))
  have h4 : 0 ≤ (l : ℝ) ^ (-(m : ℤ)) := by positivity
  rw [h1]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_lpow]
  nlinarith

theorem inclW_inj : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

variable {P : LocPrime l} (AI : LocAinf l P)

theorem xi_cancel {a b : Ainf l} (h : AI.ξ * a = AI.ξ * b) : a = b := by
  apply inclW_inj
  have := congrArg (inclW l) h
  rw [map_mul, map_mul] at this
  exact AI.isUnit_inclW_ξ.mul_left_cancel this

theorem εroot_pow (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ k ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem ζQ_pow (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem theta_lambda (θ : Ainf l →+* OC l) (hθ : IsTheta AI θ) (g : GQ l)
    (hg : g (P.ζQ 1) = P.ζQ 1) (lam : Ainf l) (hlam : AI.actW g AI.ξ = lam * AI.ξ) :
    ((θ lam : OC l) : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (P.χQ g : ℚ_[l]) := by
  obtain ⟨-, -, hact, hker, hζ⟩ := hθ
  have hπ : θ AI.π₁ = AI.ζ 1 - 1 := by
    rw [LocAinf.π₁, map_sub, map_one, ← hζ 1]; rfl
  have hne : ((AI.ζ 1 - 1 : OC l) : PadicComplex l) ≠ 0 := by
    intro h
    exact AI.ζ_one (sub_eq_zero.1 (Subtype.ext h))
  have hgπ : θ (AI.actW g AI.π₁) = AI.ζ 1 - 1 := by
    apply Subtype.ext
    have := hact g AI.π₁
    rw [hπ] at this
    rw [this]
    push_cast
    rw [map_sub, map_one, AI.ζ_eq, AI.actC_ext, hg]
  rw [← sub_eq_zero]
  apply mul_left_cancel₀ hne
  rw [mul_zero]
  apply eq_zero_of_norm_le
  intro m
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m (P.ζQ m) (ζQ_pow m)
  set z : Ainf l := WittVector.teichmuller l (AI.εroot m) with hz
  have hzl : z ^ (l ^ m) = 1 + AI.μ := by
    rw [hz, ← map_pow, εroot_pow, LocAinf.μ]; ring
  have h0 : θ (AI.actW g z - z ^ a) = 0 := by
    apply Subtype.ext
    rw [map_sub, map_pow]
    push_cast
    rw [hact, hζ m, AI.ζ_eq, AI.actC_ext, hga, sub_eq_zero]
    exact map_pow (algebraMap (Om l) (PadicComplex l)) _ _
  obtain ⟨b, hb⟩ := (hker _).1 h0
  have hb' : AI.actW g z = z ^ a + AI.ξ * b := by rw [← hb]; ring
  obtain ⟨k, hk⟩ := Polynomial.powAddExpansion (z ^ a) (AI.ξ * b) (l ^ m)
  obtain ⟨k', hk'⟩ := Polynomial.powAddExpansion (1 : Ainf l) AI.μ a
  have h1 : 1 + AI.actW g AI.μ = (z ^ a + AI.ξ * b) ^ (l ^ m) := by
    rw [← hb', ← map_pow, hzl, map_add (f := _), map_one]
  rw [hk, ← pow_mul, mul_comm a, pow_mul, hzl, hk', AI.μ_eq, map_mul, hlam] at h1
  have h2 : AI.actW g AI.π₁ * lam = (a : Ainf l) * AI.π₁ +
      (l : Ainf l) ^ m * ((z ^ a) ^ (l ^ m - 1) * b) + AI.ξ * (k' * AI.π₁ ^ 2 + k * b ^ 2) := by
    apply xi_cancel AI
    rw [Nat.cast_pow, one_pow, one_pow] at h1
    linear_combination h1
  have hξ : θ AI.ξ = 0 := (hker _).2 dvd_rfl
  have h3 := congrArg (fun t => ((θ t : OC l) : PadicComplex l)) h2
  simp only [map_add (f := _), map_mul, hξ, hgπ, hπ, map_pow, map_natCast, zero_mul, add_zero] at h3
  set u : OC l := (θ z ^ a) ^ (l ^ m - 1) * θ b with hu
  have h4 : ((AI.ζ 1 - 1 : OC l) : PadicComplex l) * (((θ lam : OC l) : PadicComplex l) -
      algebraMap ℚ_[l] (PadicComplex l) (P.χQ g : ℚ_[l])) = (l : PadicComplex l) ^ m * (u : PadicComplex l) -
      ((AI.ζ 1 - 1 : OC l) : PadicComplex l) *
        algebraMap ℚ_[l] (PadicComplex l) ((P.χQ g : ℚ_[l]) - a) := by
    rw [map_sub, map_natCast]
    generalize (AI.ζ 1 - 1 : OC l) = t at h3 ⊢
    push_cast at h3
    linear_combination h3
  rw [h4]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_lpow, norm_alg]
  have h5 := norm_OC u
  have h6 := norm_OC (AI.ζ 1 - 1)
  have h7 : 0 ≤ (l : ℝ) ^ (-(m : ℤ)) := by positivity
  have h8 := norm_nonneg ((P.χQ g : ℚ_[l]) - a)
  nlinarith

def toM (i : ℤ) : Ainf l →+ Mxi (AinfSub l) (xiU AI) i where
  toFun a := ⟨((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a, inclW l a, ⟨a, rfl⟩, rfl⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp [mul_add])

theorem toM_val (i : ℤ) (a : Ainf l) :
    (toM AI i a : WCb l) = ((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a := rfl

theorem toM_bij (i : ℤ) : Function.Bijective (toM AI i) := by
  constructor
  · intro a b h
    have := congrArg Subtype.val h
    rw [toM_val, toM_val] at this
    exact inclW_inj ((Units.mul_right_inj _).1 this)
  · rintro ⟨x, y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

theorem toM_mem (i : ℤ) (a : Ainf l) :
    toM AI i a ∈ (Mxi (AinfSub l) (xiU AI) (i + 1)).comap (Mxi (AinfSub l) (xiU AI) i).subtype ↔
      AI.ξ ∣ a := by
  have key : ∀ b : Ainf l, ((xiU AI ^ (i + 1) : (WCb l)ˣ) : WCb l) * inclW l b =
      ((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l (AI.ξ * b) := by
    intro b
    rw [zpow_add_one, Units.val_mul, map_mul, mul_assoc]; rfl
  constructor
  · rintro ⟨y, ⟨b, rfl⟩, h⟩
    refine ⟨b, ?_⟩
    have h' : ((xiU AI ^ (i + 1) : (WCb l)ˣ) : WCb l) * inclW l b =
      ((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a := h
    rw [key] at h'
    exact (inclW_inj ((Units.mul_right_inj _).1 h')).symm
  · rintro ⟨b, rfl⟩
    exact ⟨inclW l b, ⟨b, rfl⟩, key b⟩

theorem toM_smul (i : ℤ) (z : ℤ_[l]) (a : Ainf l) :
    z • toM AI i a = toM AI i (algebraMap ℤ_[l] (Ainf l) z * a) := by
  apply Subtype.ext
  rw [Submodule.coe_smul, toM_val, toM_val, map_mul, Algebra.smul_def]
  have : inclW l (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (WCb l) z := (inclWA l).commutes z
  rw [this]; ring

theorem toM_act (i : ℤ) (g : GQ l) : ∃ lam : (Ainf l)ˣ, AI.actW g AI.ξ = lam * AI.ξ ∧
    ∀ a : Ainf l, actM (xiOK AI) i g (toM AI i a) =
      toM AI i (((lam ^ i : (Ainf l)ˣ) : Ainf l) * AI.actW g a) := by
  obtain ⟨u, ⟨b, hb⟩, ⟨b', hb'⟩, hu⟩ := (xiOK AI).2.2 g
  have hb1 : inclW l b = u := hb
  have hb2 : inclW l b' = ((u⁻¹ : (WCb l)ˣ) : WCb l) := hb'
  have hbb : b * b' = 1 := by
    apply inclW_inj
    rw [map_mul, hb1, hb2, map_one, Units.mul_inv]
  let lam : (Ainf l)ˣ := ⟨b, b', hbb, by rw [mul_comm, hbb]⟩
  have hmap : Units.map (inclW l).toMonoidHom lam = u := Units.ext hb1
  refine ⟨lam, ?_, fun a => ?_⟩
  · apply inclW_inj
    have h1 := inclW_act AI g AI.ξ
    have h2 : AI.actWCbHom g (inclW l AI.ξ) = u * inclW l AI.ξ := hu
    rw [map_mul]
    change inclW l (AI.actWHom g AI.ξ) = inclW l b * _
    rw [← h1, h2, hb1]
  · apply Subtype.ext
    change AI.actWCbHom g (((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a) = _
    rw [toM_val, map_mul, act_zpow (act := AI.actWCbHom) g i u hu, inclW_act, map_mul, mul_zpow, Units.val_mul]
    have h3 : inclW l ((lam ^ i : (Ainf l)ˣ) : Ainf l) = ((u ^ i : (WCb l)ˣ) : WCb l) := by
      rw [← hmap, ← map_zpow]; rfl
    rw [h3]
    change _ = _ * (_ * inclW l (AI.actWHom g a))
    ring

theorem graded_of_theta (θ : Ainf l →+* OC l) (hθ : IsTheta AI θ) (i : ℤ) :
    ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧
      Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧
      ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x,
        Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  let θ' : Ainf l →+* PadicComplex l := (PadicComplexInt l).subtype.comp θ
  have hθ' : ∀ a, θ' a = ((θ a : OC l) : PadicComplex l) := fun _ => rfl
  have hker : ∀ a, θ' a = 0 ↔ AI.ξ ∣ a := by
    intro a
    rw [← hθ.2.2.2.1 a, hθ']
    exact ZeroMemClass.coe_eq_zero
  let e := AddEquiv.ofBijective (toM AI i) (toM_bij AI i)
  let f : Mxi (AinfSub l) (xiU AI) i →+ PadicComplex l :=
    θ'.toAddMonoidHom.comp e.symm.toAddMonoidHom
  have hf : ∀ a, f (toM AI i a) = θ' a := fun a => congrArg θ' (e.symm_apply_apply a)
  let Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l :=
    QuotientAddGroup.lift
      ((Mxi (AinfSub l) (xiU AI) (i + 1)).comap (Mxi (AinfSub l) (xiU AI) i).subtype).toAddSubgroup f
      (by
        intro x hx
        obtain ⟨a, rfl⟩ := (toM_bij AI i).2 x
        rw [AddMonoidHom.mem_ker, hf, hker]
        exact (toM_mem AI i a).1 hx)
  have hΦ : ∀ a, Φ (Submodule.Quotient.mk (toM AI i a)) = θ' a := fun a => hf a
  have hsurj : ∀ x : Qab (AinfSub l) (xiU AI) i (i + 1), ∃ a, x = Submodule.Quotient.mk (toM AI i a) := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, rfl⟩ := (toM_bij AI i).2 y
    exact ⟨a, rfl⟩
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := hsurj x
    rw [hΦ, hker] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((toM_mem AI i a).2 hx)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj x
      rw [Set.mem_setOf_eq, hΦ]
      exact norm_OC _
    · intro hy
      obtain ⟨a, ha⟩ := hθ.2.1 ⟨y, (mem_OC_iff y).2 hy⟩
      exact ⟨_, by rw [hΦ a, hθ', ha]⟩
  · intro z x
    obtain ⟨a, rfl⟩ := hsurj x
    rw [← Submodule.Quotient.mk_smul, toM_smul, hΦ, hΦ, map_mul, hθ', theta_alg]
  · intro g hg x
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨lam, h1, h2⟩ := toM_act AI i g
    have h3 := theta_lambda AI θ hθ g hg lam h1
    have h4 : actQab (xiOK AI) i (i + 1) g (Submodule.Quotient.mk (toM AI i a)) =
        Submodule.Quotient.mk (actM (xiOK AI) i g (toM AI i a)) := rfl
    rw [h4, h2, hΦ, hΦ, map_mul, hθ' (AI.actW g a), hθ.2.2.1, hθ' a]
    congr 1
    have h5 : Units.map θ'.toMonoidHom lam =
        Units.map (algebraMap ℚ_[l] (PadicComplex l)).toMonoidHom (P.χQ g) := Units.ext h3
    have h6 := congrArg (fun u : (PadicComplex l)ˣ => ((u ^ i : (PadicComplex l)ˣ) : PadicComplex l)) h5
    beta_reduce at h6
    rw [← map_zpow, ← map_zpow] at h6
    exact h6

theorem graded_iso : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (i : ℤ),
    ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧
      Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧
      ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x,
        Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  intro l _ P AI i
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_fontaineTheta_on_Ainf l P AI
  exact graded_of_theta AI θ hθ i

end GlobalTheory.Cyc.Graded
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiGradedPieceIsoTwistedOCStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xiGradedPiece_iso_twistedOC : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (i : ℤ), ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧ Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧ ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x, Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  first | exact @GlobalTheory.Cyc.Graded.graded_iso | exact GlobalTheory.Cyc.Graded.graded_iso | (intros; apply GlobalTheory.Cyc.Graded.graded_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateBasisOfIsDecompletionAtLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateBasisOfIsDecompletionAtLevel
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem htBasis_of_isDec : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  intro l _ act χ _ _ K m d M U Dm g J hD hH
  obtain ⟨hdet, -, -, -, hrel⟩ := hD
  obtain ⟨e, u, hli, hu, hfix⟩ := hH
  have hDe : ∀ v : Fin d → PadicComplex l, Dm.mulVec (Dm⁻¹.mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hinj : ∀ v w : Fin d → PadicComplex l, Dm.mulVec v = Dm.mulVec w → v = w := by
    intro v w h
    have h2 := congrArg (fun x => Dm⁻¹.mulVec x) h
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] using h2
  refine ⟨fun k => Dm⁻¹.mulVec (e k), u, ?_, hu, ?_⟩
  · refine LinearIndependent.of_comp Dm.mulVecLin ?_
    have : (Dm.mulVecLin ∘ fun k => Dm⁻¹.mulVec (e k)) = e := by
      funext k
      exact hDe (e k)
    rw [this]
    exact hli
  · intro σ hσ k
    apply hinj
    have hmap : (Dm.map (act σ)).mulVec (fun a => act σ (Dm⁻¹.mulVec (e k) a)) =
        fun a => act σ (e k a) := by
      funext a
      conv_rhs => rw [← hDe (e k)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    have h1 := hfix σ hσ k
    unfold twAct at h1 ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hrel σ hσ, ← Matrix.mulVec_mulVec, hmap, h1, hDe]

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateBasisOfIsDecompletionAtLevelStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateBasis_of_isDecompletionAtLevel : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  first | exact @GlobalTheory.Cyc.htBasis_of_isDec | exact GlobalTheory.Cyc.htBasis_of_isDec | (intros; apply GlobalTheory.Cyc.htBasis_of_isDec <;> assumption)
end
end

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Topology Filter TensorProduct Matrix

namespace GlobalTheory.Cyc.GradedTorsion

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_eq (q : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) q = ((algebraMap ℚ_[l] (Om l) q : Om l) : PadicComplex l) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) q

theorem act_zC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (z : ℤ_[l]) : act g (zC z) = zC z := by
  rw [zC, algebraMap_eq, ha.1, AlgEquiv.commutes]

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  have h : (l : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h, algebraMap_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem zC_add (x y : ℤ_[l]) : zC (x + y) = zC x + zC y := by simp [zC]

theorem zC_mul (x y : ℤ_[l]) : zC (x * y) = zC x * zC y := by simp [zC]

theorem zC_sum {ι : Type} (s : Finset ι) (f : ι → ℤ_[l]) : zC (∑ j ∈ s, f j) = ∑ j ∈ s, zC (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, zC_add, ih]

theorem zC_pow_l (k : ℕ) : zC ((l : ℤ_[l]) ^ k) = (l : PadicComplex l) ^ k := by simp [zC]

theorem mulVec_mem_ball {d : ℕ} {A : Matrix (Fin d) (Fin d) (PadicComplex l)}
    (hA : ∀ a b, ‖A a b‖ ≤ 1) {y : Fin d → PadicComplex l} (hy : y ∈ ball l d) :
    A *ᵥ y ∈ ball l d := by
  intro a
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun b _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA a b) (norm_nonneg _) (hy b)

theorem twAct_smul_nat (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (i : ℤ) {d : ℕ} (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (σ : GQ l) (n : ℕ)
    (y : Fin d → PadicComplex l) :
    twAct act χ i U σ ((n : PadicComplex l) • y) = (n : PadicComplex l) • twAct act χ i U σ y := by
  have : (fun a => act σ (((n : PadicComplex l) • y) a)) =
      (n : PadicComplex l) • fun a => act σ (y a) := by
    funext a; simp
  simp only [twAct]
  rw [this, Matrix.mulVec_smul, smul_comm]

theorem twAct_mulVec (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (i : ℤ) {d : ℕ} (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (σ : GQ l) (h : D * U σ = M σ * D.map (act σ))
    (y : Fin d → PadicComplex l) :
    twAct act χ i M σ (D *ᵥ y) = D *ᵥ twAct act χ i U σ y := by
  have : (fun a => act σ ((D *ᵥ y) a)) = D.map (act σ) *ᵥ fun a => act σ (y a) := by
    funext a; simp [Matrix.mulVec, dotProduct]
  simp only [twAct]
  rw [this, Matrix.mulVec_mulVec, ← h, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

theorem sandwich {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    {K : FinExt l} {m d : ℕ} {M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)}
    {D : Matrix (Fin d) (Fin d) (PadicComplex l)} {g : GQ l} (hD : IsDec act χ K m M D U g)
    (i : ℤ) (n : ℕ)
    (hU : ∀ (c : GQ l → Fin d → PadicComplex l) (k : ℕ),
      CocOn (Gj K m) (twAct act χ i U) (ball l d) c →
      CobOn (Gj K m) (twAct act χ i U) (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ) →
      CobOn (Gj K m) (twAct act χ i U) (ball l d) (fun σ => (l : PadicComplex l) ^ n • c σ))
    (c : GQ l → Fin d → PadicComplex l) (k : ℕ)
    (hc : CocOn (Gj K m) (twAct act χ i M) (ball l d) c)
    (hk : CobOn (Gj K m) (twAct act χ i M) (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ)) :
    CobOn (Gj K m) (twAct act χ i M) (ball l d) (fun σ => (l : PadicComplex l) ^ (n + 1) • c σ) := by
  obtain ⟨hdet, hint, hinv, -, hcomm⟩ := hD
  set E : Matrix (Fin d) (Fin d) (PadicComplex l) := (l : PadicComplex l) • D⁻¹ with hE
  have hEint : ∀ a b, ‖E a b‖ ≤ 1 := fun a b => by simpa [hE] using hinv a b
  have hDE : ∀ y, D *ᵥ (E *ᵥ y) = (l : PadicComplex l) • y := fun y => by
    rw [Matrix.mulVec_mulVec, hE, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hinj : Function.Injective D.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det D).2 hdet)
  have hEt : ∀ σ ∈ Gj K m, ∀ y, twAct act χ i U σ (E *ᵥ y) = E *ᵥ twAct act χ i M σ y := by
    intro σ hσ y
    apply hinj
    show D *ᵥ _ = D *ᵥ _
    rw [← twAct_mulVec act χ i M U D σ (hcomm σ hσ), hDE, hDE, twAct_smul_nat]
  obtain ⟨x, hx, hxe⟩ := hU (fun σ => E *ᵥ c σ) k
    ⟨(continuous_const.matrix_mulVec continuous_id).comp_continuousOn hc.1,
      fun σ hσ => mulVec_mem_ball hEint (hc.2.1 σ hσ), fun σ hσ τ hτ => by
        simp only [hc.2.2 σ hσ τ hτ, Matrix.mulVec_add, hEt σ hσ]⟩
    (by
      obtain ⟨x, hx, hxe⟩ := hk
      refine ⟨E *ᵥ x, mulVec_mem_ball hEint hx, fun σ hσ => ?_⟩
      have := hxe σ hσ
      simp only at this ⊢
      rw [hEt σ hσ, ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul])
  refine ⟨D *ᵥ x, mulVec_mem_ball hint hx, fun σ hσ => ?_⟩
  have := hxe σ hσ
  simp only at this ⊢
  rw [twAct_mulVec act χ i M U D σ (hcomm σ hσ), ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul,
    hDE, smul_smul, pow_succ]

theorem transfer {G : Subgroup (GQ l)} {X : Type} [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] ↥G X) {d : ℕ}
    (A : GQ l → (Fin d → PadicComplex l) → (Fin d → PadicComplex l))
    (Ψ : X →+ (Fin d → PadicComplex l)) (hinj : Function.Injective Ψ)
    (hr : Set.range Ψ = ball l d)
    (hl : ∀ (k : ℕ) x, Ψ ((l : ℤ_[l]) ^ k • x) = (l : PadicComplex l) ^ k • Ψ x)
    (hA : ∀ (g : ↥G) x, Ψ (ρ g x) = A g (Ψ x)) (n : ℕ)
    (H : ∀ (c : GQ l → Fin d → PadicComplex l) (k : ℕ), CocOn G A (ball l d) c →
      CobOn G A (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ) →
      CobOn G A (ball l d) (fun σ => (l : PadicComplex l) ^ n • c σ)) :
    @TorsKilledBy ℤ_[l] ↥G X _ _ _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology X) ρ
      (l : ℤ_[l]) ((l : ℤ_[l]) ^ n) := by
  classical
  rintro f ⟨hfc, hfm⟩ ⟨k, x, hx⟩
  rw [continuous_adicModule_iff] at hfc
  have hb : ∀ y, Ψ y ∈ ball l d := fun y => hr ▸ ⟨y, rfl⟩
  let c : GQ l → Fin d → PadicComplex l := fun σ => if h : σ ∈ G then Ψ (f ⟨σ, h⟩) else 0
  have hc : ∀ σ (h : σ ∈ G), c σ = Ψ (f ⟨σ, h⟩) := fun σ h => dif_pos h
  have hcont : Continuous fun g : ↥G => Ψ (f g) := by
    rw [continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt (l := l))
    filter_upwards [hfc g N] with h hh
    obtain ⟨y, e⟩ := hh
    rw [dist_eq_norm, ← map_sub, e, hl, norm_smul, norm_pow]
    refine lt_of_le_of_lt ?_ hN
    exact mul_le_of_le_one_right (by positivity) ((pi_norm_le_iff_of_nonneg zero_le_one).2 (hb y))
  obtain ⟨y, hy, hye⟩ := H c k
    ⟨by
      rw [continuousOn_iff_continuous_domRestrict]
      convert hcont using 1
      funext g
      exact hc g g.2,
    fun σ hσ => by rw [hc σ hσ]; exact hb _,
    fun σ hσ τ hτ => by
      rw [hc σ hσ, hc τ hτ, hc _ (G.mul_mem hσ hτ)]
      have := hfm ⟨σ, hσ⟩ ⟨τ, hτ⟩
      rw [← hA ⟨σ, hσ⟩, ← map_add (f := _), ← this]
      rfl⟩
    ⟨Ψ x, hb x, fun σ hσ => by
      have := hx ⟨σ, hσ⟩
      simp only [Pi.smul_apply] at this
      simp only
      rw [hc σ hσ, ← hl, this, map_sub, hA]⟩
  rw [← hr] at hy
  obtain ⟨z, rfl⟩ := hy
  refine ⟨z, fun g => hinj ?_⟩
  have := hye g g.2
  simp only at this
  rw [Pi.smul_apply, hl, map_sub, hA, ← this, hc g g.2]

theorem exists_coord {T Q : Type} [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup Q]
    [Module ℤ_[l] Q] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] T) (Φ : Q →+ PadicComplex l)
    (hinj : Function.Injective Φ) (hr : Set.range Φ = {y | ‖y‖ ≤ 1})
    (hz : ∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) :
    ∃ Ψ : T ⊗[ℤ_[l]] Q →+ (Fin d → PadicComplex l), Function.Injective Ψ ∧
      Set.range Ψ = ball l d ∧ (∀ (z : ℤ_[l]) x, Ψ (z • x) = zC z • Ψ x) ∧
      ∀ t q a, Ψ (t ⊗ₜ q) a = zC (b.repr t a) * Φ q := by
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := Q) b
  refine ⟨⟨⟨fun x a => Φ (e x a), ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · funext a; simp
  · intro x y; funext a; simp
  · intro x y hxy
    apply e.injective
    ext a
    exact hinj (congrFun hxy a)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩ a
      exact (hr ▸ ⟨_, rfl⟩ : Φ (e x a) ∈ {y : PadicComplex l | ‖y‖ ≤ 1})
    · intro hy
      have : ∀ a, ∃ q, Φ q = y a := fun a =>
        (hr.symm ▸ hy a : y a ∈ Set.range Φ)
      choose q hq using this
      refine ⟨e.symm (Finsupp.equivFunOnFinite.symm q), ?_⟩
      funext a
      simp [hq]
  · intro z x
    funext a
    simp [hz]
  · intro t q a
    simp [e, hz]

theorem coord_equivariant {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {T Q : Type} [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup Q]
    [Module ℤ_[l] Q] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] T) (Φ : Q →+ PadicComplex l)
    (Ψ : T ⊗[ℤ_[l]] Q →+ (Fin d → PadicComplex l))
    (hΨ : ∀ t q a, Ψ (t ⊗ₜ q) a = zC (b.repr t a) * Φ q)
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (r : T →ₗ[ℤ_[l]] T)
    (s : Q →ₗ[ℤ_[l]] Q) (hM : ∀ a j, M g a j = zC (b.repr (r (b j)) a))
    (hs : ∀ x, Φ (s x) = chiC χ i g * act g (Φ x)) (x : T ⊗[ℤ_[l]] Q) :
    Ψ (TensorProduct.map r s x) = twAct act χ i M g (Ψ x) := by
  induction x using TensorProduct.induction_on with
  | zero => funext a; simp [twAct, Matrix.mulVec, dotProduct]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
    funext a
    simp [twAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  | tmul t q =>
    funext a
    have h1 : b.repr (r t) a = ∑ j, b.repr (r (b j)) a * b.repr t j := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← b.sum_repr t, map_sum, map_sum, Finsupp.finsetSum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    simp only [TensorProduct.map_tmul, hΨ, twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, map_mul, act_zC ha, hM, hs, h1, zC_sum, zC_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

theorem rI_eq (l m : ℕ) (J : Finset ℤ) (i : ℤ) :
    rI l m (J : Set ℤ) i = ∑ u ∈ J.erase i, (m + padicValInt l (u - i)) := by
  rw [rI, ← finsum_mem_finset_eq_sum]
  refine finsum_congr fun u => ?_
  by_cases h1 : u ∈ J <;> by_cases h2 : u = i <;> simp [h1, h2, vZ]

theorem of_basis (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l)
    {T : Type} [AddCommGroup T] [Module ℤ_[l] T] (m : ℕ) (hlev : Lev l m)
    (ρ : ↥(Gj K m) →* (T →ₗ[ℤ_[l]] T)) (i : ℤ)
    (J : Set ℤ) (hfin : J.Finite) {d : ℕ} {M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)}
    (b : Module.Basis (Fin d) ℤ_[l] T)
    (hb : ∀ (σ : ↥(Gj K m)) a j, M σ a j = zC (b.repr (ρ σ (b j)) a))
    {Dm : Matrix (Fin d) (Fin d) (PadicComplex l)} {g : GQ l}
    (hD : IsDec AI.actC P.χQ K m M Dm U g) (hHT : HTBasis AI.actC P.χQ (Gj K m) M J) :
    @TorsKilledBy ℤ_[l] _ _ _ _ _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology _)
      (repQ AI (Gj K m) ρ i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (2 + max 1 (rI l m J i))) := by
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hHT' := GlobalTheory.T.hodgeTateBasis_of_isDecompletionAtLevel l _ _ ha hχ K _ d M U Dm g _ hD hHT
  have hJ : J = (hfin.toFinset : Set ℤ) := hfin.coe_toFinset.symm
  have hc6 := GlobalTheory.T.cocycle_twist_coboundary_on_ball l _ _ ha hχ K _ d hlev U g hD.2.2.2.1 hfin.toFinset (hJ ▸ hHT') i
  rw [← rI_eq, ← hJ] at hc6
  have hs := sandwich hD i _ hc6
  obtain ⟨Φ, hinj, hr, hz, hact⟩ := GlobalTheory.T.xiGradedPiece_iso_twistedOC l P AI i
  obtain ⟨Ψ, hΨi, hΨr, hΨz, hΨ⟩ := exists_coord b Φ hinj hr hz
  have hn : 2 + max 1 (rI l m J i) = 1 + max 1 (rI l m J i) + 1 := by omega
  rw [hn]
  refine transfer _ (twAct AI.actC P.χQ i M) Ψ hΨi hΨr
    (fun k x => by rw [hΨz, zC_pow_l]) (fun σ x => ?_) _ hs
  have hζ : (σ : GQ l) (P.ζQ 1) = P.ζQ 1 := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ ?_
    refine (le_sup_right : _ ≤ Ks K _) (IntermediateField.subset_adjoin _ _ ?_)
    show P.ζQ 1 ^ (l ^ m) = 1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlev.1
    have h1 : P.ζQ 1 ^ l = 1 := (P.ζQ_succ 0).trans P.ζQ_zero
    rw [pow_add, pow_one, pow_mul, h1, one_pow]
  exact coord_equivariant ha _ i b Φ Ψ hΨ M σ (ρ σ)
    (actQab (xiOK AI) i (i + 1) σ) (hb σ) (hact σ hζ) x

theorem torsion_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (i : ℤ) (hle : Gj K (mN l s (M0 + h0)) ≤ GK K), HypW S E T M0 h0 → letI := zlMod LL T; letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) i (i + 1))) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; TorsKilledBy (repQ (D.locA l) (Gj K (mN l s (M0 + h0))) ((actTZ LL T).comp (Subgroup.inclusion hle)) i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (2 + max 1 (rI l (mN l s (M0 + h0)) (Jset S T) i))) := by
  intro D HW F h7 l _ K s LL h S E T M0 h0 i hle hW
  have hsm : s ≤ mN l s (M0 + h0) := by unfold mN; omega
  have hlev : Lev l (mN l s (M0 + h0)) :=
    ⟨le_trans h.1 hsm, fun h2 => le_trans (h.2.1 h2) hsm⟩
  have h1 := (GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).1
  refine h1.elim fun d h1 => h1.elim fun M h1 => h1.elim fun A hM => ?_
  have h2 := GlobalTheory.T.exists_decompletion_frame_of_lattice D HW F l K s LL h T M0 h0 hW d M A hM
  refine h2.elim fun Dm h2 => h2.elim fun U h2 => h2.elim fun g hD => ?_
  have h3 := GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks D HW F h7 l K s LL h T hW.1 d M A hM _ hsm
  refine Exists.elim hM fun b hb => ?_
  exact @of_basis l _ (D.loc l) (D.locA l) K _ _ (zlMod LL T) _ hlev
    ((actTZ LL T).comp (Subgroup.inclusion hle)) i _ h3.1 d M U b
    (fun σ => hb.1 (Subgroup.inclusion hle σ)) Dm g hD.1 h3.2

end GlobalTheory.Cyc.GradedTorsion

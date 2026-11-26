module

public import Development.WeilBound.ThetaLifts.SmallCones.ConeLaw
public import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.ConeLawAB
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cA_cA (hσ : IsCMExt F E σ) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [cA, cm_conj_conj hσ]
  | add a b ha hb => simp [ha, hb]

theorem chi_conj (hσ : IsCMExt F E σ) {χ : Chr F E} {k : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ k) (t : (AE F E)ˣ) :
    χ (GlobalTheory.Doubling.conjUnit σ t) = (χ t)⁻¹ := by
  have h1 := h (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t)
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨t, rfl⟩)), Circle.coe_eq_one,
    show Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) =
      t * GlobalTheory.Doubling.conjUnit σ t from Units.ext (GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := AF F) t.1), map_mul] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem conjUnit_val (t : (AE F E)ˣ) : (GlobalTheory.Doubling.conjUnit σ t : (AE F E)ˣ).1 = cA σ t.1 := rfl

section

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
  {om : Rep σ X W} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {χX χW : Chr F E}
  {r s r' s' : ℕ} {rX rW : ℝ}

theorem isLevi_inv' {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.x = (t⁻¹ : (AE F E)ˣ).1 • incV F H'.x :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.1, smul_smul, Units.inv_mul, one_smul])

theorem levi_inv_y {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.y = cA σ t.1 • incV F H'.y :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.2.1, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul])

theorem Mix2.levi (h : Mix2 H H' χX χW rX rW om om₀ e) {t g₁ p t' h₁ p'} (h1 : IsLevi H t g₁ p) (h2 : IsLevi H' t' h₁ p') {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : e (om (p, p') Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) *
      ((χX t' : ℂ) * (((absE F E t' : ℝ) ^ rW : ℝ) : ℂ))) • om₀ (g₁, h₁) (e Φ) := by
  simpa using h t g₁ p h1 1 (one_mem _) t' h₁ p' h2 1 (one_mem _) Φ hΦ

theorem Mix2.uni (h : Mix2 H H' χX χW rX rW om om₀ e) {m} (hm : m ∈ unip σ X H) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    e (om (m, 1) Φ) = e Φ := by
  simpa [← Prod.one_eq_mk] using h 1 1 1 (levi_one H) m hm 1 1 1 (levi_one H') 1 (one_mem _) Φ hΦ

theorem rpow_c {a : ℝ} (ha : 0 < a) (x y : ℝ) : ((a ^ x : ℝ) : ℂ) * ((a ^ y : ℝ) : ℂ) = ((a ^ (x + y) : ℝ) : ℂ) := by
  rw [Real.rpow_add ha, Complex.ofReal_mul]

theorem lawsTA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e)
    (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    LawsT B M om om₀ H H' e (shiftA H H') (fun l => (χW⁻¹ l : ℂ) * (((absE F E l : ℝ) ^ ((n : ℝ) - 1 - d₁ / 2) : ℝ) : ℂ))
      fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  refine ⟨inv_one, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), mat_inv_mulVec m (hx m hm), inv_one, mat_one', Matrix.one_mulVec]
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), isLevi_inv' h1, levi_inv_y h2, smul_smul]
    simp only [inv_inv, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one, map_inv, MonoidHom.inv_apply]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, NNReal.coe_inv, rpow_c (inv_pos.2 ha), Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    congr 3
    ring

theorem lawsA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : 2 * n = d + 2 * z) (hd : d = d₁ + 2) (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    Laws B M om om₀ H H' e (shiftA H H') χW⁻¹ (χX / χW) z fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hd' : (d : ℝ) = d₁ + 2 := by exact_mod_cast hd
  have hz' : (2 * n : ℝ) = d + 2 * z := by exact_mod_cast hz
  refine ⟨?_, fun t h₁ p' h2 => ⟨GlobalTheory.Doubling.conjUnit σ t, fun l Ψ hΨ => ?_⟩⟩
  · convert lawsTA hp hM hx using 3 with l
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 2
    linarith
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), levi_inv_y h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, Units.val_mul, conjUnit_val]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, MonoidHom.inv_apply,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, show (n : ℝ) / 2 = (d - n) / 2 + z by linarith, ← rpow_c ha]
    field_simp

theorem sy_iso (hx : form σ W.J H'.x H'.x = 0) (a b : Fin n → AE F E) :
    sy σ X W (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
  have h0 : ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) = 0 := by
    have := congrArg (inclR (F := F) (AF F)) hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, map_zero] at this
    simpa [incV, incM, cA, inclR, mul_assoc] using this
  have : hTens (cA σ) (incM F X.J) (incM F W.J) (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
    calc _ = ∑ i, ∑ k, a i * incM F X.J i k * cA σ (b k) * ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) := by
          simp only [hTens, Matrix.vecMulVec_apply, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      _ = 0 := by simp [h0]
  simp only [sy, symp, this, mul_zero, map_zero]

theorem lawsB {M₀ : Model σ X₁ W₁} (hp : IsPair B M χX χW om r s r' s') (he : IsEv B M M₀ H.ι H'.ι (isoB H H') e)
    (hM : Mix2 H H' χX χW ((d : ℝ) / 2) ((n₁ : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : d + 2 = 2 * n + 2 * z) (hn : n = n₁ + 2) (hxx : form σ W.J H'.x H'.x = 0)
    (hy : ∀ m ∈ unip σ X H, ∃ (y : Fin n₁ → AE F E) (c : AE F E),
      mat m *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ y + c • incV F H.x) :
    Laws B M om om₀ H H' e (shiftB σ H H') χW (χX / χW) z id := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hz' : (d : ℝ) + 2 = 2 * n + 2 * z := by exact_mod_cast hz
  have hn' : (n : ℝ) = n₁ + 2 := by exact_mod_cast hn
  refine ⟨⟨rfl, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩,
    fun t h₁ p' h2 => ⟨(GlobalTheory.Doubling.conjUnit σ t)⁻¹, fun l Ψ hΨ => ?_⟩⟩
  · unfold shiftB
    obtain ⟨y, c, hy'⟩ := hy m⁻¹ (inv_mem hm)
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), hy', inv_one, mat_one', Matrix.one_mulVec, Units.val_one, map_one, one_smul,
      one_smul, Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_comm, ← rho_rho_of M.co B.ψ _ _ (by
        rw [← Matrix.add_vecMulVec]; exact sy_iso hxx _ _), he.inv _ (Or.inl ⟨c • incV F H'.x, by
        rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩) _ (hs _ _ hΨ), add_comm, ← rho_rho_of M.co B.ψ _ _ (sy_iso hxx _ _),
      he.inv _ (Or.inr ⟨y, rfl⟩) _ (hs _ _ hΨ)]
  · unfold shiftB
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), levi_inv_y h1, isLevi_inv' h2, smul_smul]
    simp only [id, inv_one, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, rpow_c ha, ← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 3
    linarith
  · unfold shiftB
    have hc : cA σ (l * (GlobalTheory.Doubling.conjUnit σ t)⁻¹ : (AE F E)ˣ).1 = cA σ l.1 * (t⁻¹ : (AE F E)ˣ).1 := by
      rw [Units.val_mul, map_mul, ← map_inv, conjUnit_val, cA_cA hp.base.cm]
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), isLevi_inv' h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, hc]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, map_inv,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div, NNReal.coe_inv]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
      show (n₁ : ℝ) / 2 = (d - n) / 2 + -z by linarith, ← rpow_c ha]
    field_simp

end

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.ConeAB
section -- merged from Development.WeilBound.ThetaLifts.SmallCones.ConeCore
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sfin_of {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (s : Set α) : SFinite μ ∧ SFinite (μ.restrict s) :=
  ⟨inferInstance, inferInstance⟩

theorem sfin_haar {G : Type} [Group G] [TopologicalSpace G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (s : Set G) : SFinite μ ∧ SFinite (μ.restrict s) := ⟨inferInstance, inferInstance⟩

theorem cone_core (hUn : Unfold) (hU : UnipEx) (hD : StabDec) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hA : EvAdm)
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
    {M₀ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {j₀ j₁ i₀ i₁ r s r' s' r₀ s₀ r₀' s₀' : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) {I e} (he : IsEv B M M₀ H.ι H'.ι I e)
    {K : Subgroup (UA σ X.J)} {μK : Measure K} {μ : Measure (AE F E)ˣ} (hI : Iwa H K) (hμK : μK.IsHaarMeasure) (hμ : μ.IsHaarMeasure)
    (u : (AE F E)ˣ → Ten F E n d) (z : ℕ) (ι : (AE F E)ˣ → (AE F E)ˣ) (hι : ι = id ∨ ι = fun l => l⁻¹) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om r s r' s' → IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀' →
      ∀ (ν χ : Chr F E) (S : Submodule ℂ (Fn F n d)), Continuous ν → Laws B M om om₀ H H' e u ν χ z ι →
      (∀ Ψ ∈ S, Ψ ∈ schA F (Fin n × Fin d)) → (∀ x, ∀ Ψ ∈ S, om x Ψ ∈ S) →
      (∀ Ψ ∈ S, ∀ h₁, ∫⁻ l, (∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) Ψ)) g h₁‖ₑ ∂M₀.μ) *
        ENNReal.ofReal ((absE F E l : ℝ) ^ z) ∂μ < ⊤) →
      (∀ Ψ ∈ schA F (Fin n × Fin d), ∃ Ψ₁ ∈ schA F (Fin n₁ × Fin d₁), ∀ l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
        Integrable (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) μ ∧
        l₁ Ψ₁ = ∫ l, l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ) →
      ∀ Φ ∈ S, KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (u 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (u 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (u 1) Φ h (γ x * g) ∂M.μ = κ * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ u ν z (om (1, p * h) Φ) 1 =
        (χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ u ν z (om (1, h) Φ) h₁ = M₀.I om₀ (cone B M om e K μK μ u ν z (om (1, h) Φ)) h₁ := by
  by_cases hex : ∃ χX χW om om₀, IsPair B M χX χW om r s r' s' ∧ IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀'
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om om₀ hp hp₀ => absurd ⟨χX, χW, om, om₀, hp, hp₀⟩ hex⟩
  obtain ⟨χ0, χ0', o, o₀, hq, hq₀⟩ := hex
  obtain ⟨-, -, -, -, ⟨lev, hlc, hlev, -⟩, -⟩ := hU F E σ B n n₁ X X₁ H j₀ j₁ r s hq.base (Or.inl hq.herm) hH
  obtain ⟨-, -, -, -, ⟨lev', -, hlev', -⟩, -⟩ := hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hq.base (Or.inr hq.skew) hH'
  obtain ⟨κ, hκ, hUnf⟩ := hUn F E σ B n n₁ X X₁ H j₀ j₁ r s hq.base hq.herm hH K μK μ M.μ M.dom M₀.μ M₀.dom lev hI hμK hμ
    hq.good.haar hq.good.dom hq₀.good.haar hq₀.good.dom hlev
  refine ⟨κ, by exact_mod_cast hκ.ne', fun χX χW om om₀ hp hp₀ ν χ S hν hL hle hst hfin hlam Φ hΦ hK => ?_⟩
  obtain ⟨-, -, i1, -, i2, i3, i4⟩ := ideleTop F E
  obtain ⟨j1, j2, j3, -⟩ := i4 μ hμ
  obtain ⟨k1, k2, -⟩ := hG F E σ hp.base.cm n₁ X₁.J (hE F E σ B hp.base n₁ X₁ r₀ s₀ (Or.inl hp₀.herm)).1
  obtain ⟨-, k3, -⟩ := hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1
  have k4 : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  have k5 : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have k6 := hp₀.good.haar
  obtain ⟨k10, k11⟩ := sfin_haar M₀.μ M₀.dom
  have k12 : SFinite μ := (sfin_of μ ∅).1
  have k7 : CompactSpace K := isCompact_iff_compactSpace.1 hI.1
  obtain ⟨⟨l₀, hl₀, hl₀'⟩, hrho, hev⟩ := hA F E σ B n d n₁ d₁ X W X₁ W₁ M M₀ hp.base hp.good hp₀.good
  obtain ⟨l₁, hl₁, hl₁'⟩ := hev _ _ _ e he (u 1) l₀ hl₀
  have hsch : ∀ v, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ v Ψ) ∈ schA F (Fin n₁ × Fin d₁) :=
    fun v Ψ h => he.maps _ (hrho v Ψ h)
  have hcv : ∀ Ψ ∈ schA F (Fin n × Fin d), Continuous fun x => thetaSum F (e (M.co.rho B.ψ (u 1) (om x Ψ))) := fun Ψ h =>
    (pair_cont hp hl₁ h).congr fun x => by rw [hl₁' _ (pair_pres hp x h), hl₀' _ (hsch _ _ (pair_pres hp x h))]
  have hιc : Continuous ι := by rcases hι with rfl | rfl; exacts [continuous_id, continuous_inv]
  have habs : Continuous fun l : (AE F E)ˣ => (absE F E l : ℝ) := NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE
  have hw : Continuous fun l : (AE F E)ˣ => (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z :=
    (continuous_subtype_val.comp hν).mul ((Complex.continuous_ofReal.comp habs).pow z)
  have hw0 : ∀ l : (AE F E)ˣ, (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ≠ 0 := fun l =>
    mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ (by exact_mod_cast absE_ne l))
  have hOK : LineOK B M om M₀ om₀ e μ u ν z S := by
    refine ⟨hle, hst, fun l => hsch _, fun g h => ⟨_, pair_adm hp₀ (g, h) hl₀, fun Φ hΦ => hl₀' _ (pair_pres hp₀ _ hΦ)⟩,
      fun Ψ hΨ h₁ => ?_, hlam⟩
    refine int_prod μ _ (θ := fun x => theta om₀ (e (M.co.rho B.ψ (u x.1) Ψ)) x.2 h₁) ?_ hw (fun l => ?_) (hfin Ψ hΨ h₁)
    · have c1 : Continuous fun x : (AE F E)ˣ × UA σ X₁.J =>
          thetaSum F (e (M.co.rho B.ψ (u 1) (om (lev (ι x.1, x.2), lev' (1, h₁)) Ψ))) *
            (((absE F E (ι x.1) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) / ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z) :=
        (((hcv Ψ (hle Ψ hΨ)).comp ((hlc.comp ((hιc.comp continuous_fst).prodMk continuous_snd)).prodMk continuous_const)).mul
          (Complex.continuous_ofReal.comp ((habs.comp (hιc.comp continuous_fst)).rpow_const fun x => Or.inl (absE_ne _)))).div
          (hw.comp continuous_fst) fun x => hw0 _
      exact c1.congr fun x => by rw [hL.toLawsT.theta (hlev _ _) (hlev' _ _) (hle Ψ hΨ), mul_div_cancel_right₀ _ (hw0 _)]
    · rw [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  obtain ⟨m, Ψ, c, hΨ, hc, hd⟩ := kfin_dec hp (hle Φ hΦ) hK S fun k => hst _ _ hΦ
  have hci : ∀ i, Integrable (c i) μK := fun i => (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd' : ∀ h (k : K), om (k.1, 1) (om (1, h) Φ) = ∑ i, c i k • om (1, h) (Ψ i) := fun h k => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show om (k.1, 1) (om (1, h) Φ) = om (1, h) (om (k.1, 1) Φ) by simp [om_mul], hd, map_sum]
    simp only [map_smul]
  refine ⟨fun γ hγ h => ?_, fun t h₁ p hl h => hL.coneI_law hp μK (hle Φ hΦ) hl h,
    fun h h₁ => hOK.coneI_eq μK (fun i => hst _ _ (hΨ i)) hci (hd' h) h₁⟩
  obtain ⟨f1, f2⟩ := hOK.unf μK (fun i => hst _ _ (hΨ i)) hci (hd' h) ι
    (fun G => by rcases hι with rfl | rfl; exacts [rfl, lintegral_inv_eq_self G])
    (fun G => by rcases hι with rfl | rfl; exacts [rfl, integral_inv_eq_self G μ]) lev (thv B M om e (u 1) Φ h) (fun l g k => by
      rw [← hL.toLawsT.theta (hlev _ _) (levi_one (W₁ := W₁) H') (pair_pres hp _ (pair_pres hp _ (hle Φ hΦ)))]
      simp [thv, om_mul])
  rw [← f2]
  refine hUnf γ hγ _ ((hcv Φ (hle Φ hΦ)).comp (continuous_id.prodMk continuous_const)) (fun v hv g => ?_)
    (fun δ hδ hx g => hL.toLawsT.rat hD hTB hp hp₀ hH (hsch _) (hle Φ hΦ) h hδ hx g) f1
  unfold thv
  rw [show om (v * g, h) Φ = om (v, 1) (om (g, h) Φ) by simp [om_mul], hL.uni v hv _ (pair_pres hp _ (hle Φ hΦ))]

end PositivityTheory.ThKCT

end
end

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem domSo (hS : SoSemi) (hV : FinVolU) (hE : EpsOf) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    {χX χW om r s r' s'} (hp : IsPair B M χX χW om r s r' s') : Dom M om (soFin B M) := by
  intro φ hφ
  obtain ⟨p, k, hc, h⟩ := hS F E σ B n d X W M χX χW om r s r' s' hp φ hφ 0
  refine ⟨p, k, fun _ => 1, hc, measurable_const, ?_, fun f g y => ?_⟩
  · rw [setLIntegral_one]
    exact hV F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1 M.μ M.dom hp.good.haar hp.good.dom
  · rw [mul_one, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (by simpa using h f g y)

theorem incM_vecMulVec {n d : ℕ} (x : Fin n → E) (y : Fin d → E) :
    incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (incV F x) (incV F y) := by
  ext i j
  simp [incM, incV, Matrix.vecMulVec_apply]

theorem hTens_vec {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x x' : Fin n → E) (y y' : Fin d → E) :
    hTens (cA σ) (incM F J) (incM F J') (incM F (Matrix.vecMulVec x y)) (incM F (Matrix.vecMulVec x' y')) =
      inclR (F := F) (AF F) (form σ J x x' * form σ J' y y') := by
  have hc : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun a => by simp [cA, inclR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hTens, incM, Matrix.map_apply, Matrix.vecMulVec_apply, hc, ← map_mul, ← map_sum, form, dotProduct, Matrix.mulVec]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum _ _ (x i), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul]; ring

theorem form_swap (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} (h : ∀ i j, σ (J j i) = ε * J i j)
    (x y : Fin n → E) : σ (form σ J x y) = ε * form σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_conj_conj hσ, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem coneA_of (hUn : Unfold) (hU : UnipEx) (hD : StabDec) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hA : EvAdm)
    (hM : MixAB) (hL : LineInt) (hW : DomWeil) : ConeA := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨κ, hκ, h⟩ := cone_core hUn hU hD hTB hG hE hA (r := r + 1) (s := s + 1) (r' := r' + 1) (s' := s' + 1) (r₀ := r) (s₀ := s)
    (r₀' := r') (s₀' := s') hH hH' he hI hμK hμ (shiftA H H') z _ (Or.inr rfl)
  refine ⟨κ, hκ, fun χX χW om om₀ hp hp₀ Φ hΦ hK => ?_⟩
  have hν : Continuous (χW⁻¹ : Chr F E) := hp.hW.1.inv
  have hyx : form σ X.J H.y H.x = 1 := by
    have := form_swap hp.base.cm (J := X.J) (ε := 1) (fun i j => by rw [one_mul, hp.herm.herm]) H.x H.y
    rw [hH.xy, map_one, one_mul] at this
    exact this.symm
  have key := fun Ψ hΨ => hL F E σ B n d n₁ d₁ X W X₁ W₁ M M₀ hp.base hp.good hp₀.good _ _ _ e he
    (Matrix.vecMulVec H.x H'.y) (Matrix.vecMulVec H.y H'.x)
    (fun a => Or.inl ⟨a • incV F H.y, by rw [incM_vecMulVec, Matrix.smul_vecMulVec]⟩)
    (by rw [hTens_vec, hyx, hH'.xy, mul_one, map_one]; exact isUnit_one) (AlgHom.id _ _) (Or.inl rfl) μ hμ z χW⁻¹ (by omega) hν Ψ hΨ
  simp only [incM_vecMulVec, AlgHom.id_apply] at key
  have h1 := hH.rank
  have h2 := hH'.rank
  exact h χX χW om om₀ hp hp₀ χW⁻¹ (χX / χW) (schA F _) hν
    (lawsA hp ((hM F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀).1 e he) hz.1 h2
      fun m hm => ((hU F E σ B n n₁ X X₁ H j₀ j₁ _ _ hp.base (Or.inl hp.herm) hH).2.2.2.2.2.1 m hm).1)
    (fun _ h => h) (fun x Ψ h => pair_pres hp x h)
    (fun Ψ hΨ h₁ => (key Ψ hΨ).1 om₀ (fun x Φ h => pair_pres hp₀ x h)
      (Or.inl (hW F E σ B _ _ X₁ W₁ M₀ χX χW om₀ r s r' s' hp₀ (Or.inl (by omega)))) h₁)
    (fun Ψ hΨ => (key Ψ hΨ).2) Φ hΦ hK

theorem coneB_of (hUn : Unfold) (hU : UnipEx) (hD : StabDec) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hA : EvAdm)
    (hM : MixAB) (hL : LineInt) (hS : SoSemi) (hV : FinVolU) (hSF : SoFin) (hSt : SoStab) (hSe : SoEv) : ConeB := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨κ, hκ, h⟩ := cone_core hUn hU hD hTB hG hE hA (r := r + 1) (s := s + 1) (r' := r' + 1) (s' := s' + 1) (r₀ := r) (s₀ := s)
    (r₀' := r') (s₀' := s') hH hH' he hI hμK hμ (shiftB σ H H') z _ (Or.inl rfl)
  refine ⟨κ, hκ, fun χX χW om om₀ hp hp₀ Φ hΦ hK => ?_⟩
  have hyx : form σ W.J H'.y H'.x = -1 := by
    have := form_swap hp.base.cm (J := W.J) (ε := -1) (fun i j => by rw [neg_one_mul, hp.skew.skew]) H'.x H'.y
    rw [hH'.xy, map_one, neg_one_mul] at this
    rw [this, neg_neg]
  have key := fun Ψ hΨ => hL F E σ B n d n₁ d₁ X W X₁ W₁ M M₀ hp.base hp.good hp₀.good _ _ _ e he
    (Matrix.vecMulVec H.y H'.x) (Matrix.vecMulVec H.x H'.y)
    (fun a => Or.inl ⟨a • incV F H'.y, by rw [incM_vecMulVec, Matrix.vecMulVec_smul]⟩)
    (by rw [hTens_vec, hyx, hH.xy, one_mul, map_neg, map_one]; exact isUnit_one.neg) (cA σ) (Or.inr rfl) μ hμ z χW hz.2 hp.hW.1 Ψ hΨ
  have hle := (hSF F E σ B n d X W M χX χW om _ _ _ _ hp).2.2.1
  have hso := fun Ψ hΨ => (hSe F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hp.base hp.herm hp.skew hp.good
    hp₀.good e he Ψ hΨ).2
  simp only [incM_vecMulVec] at key hso
  exact h χX χW om om₀ hp hp₀ χW (χX / χW) (M.So B.ψ B.τ₁) hp.hW.1
    (lawsB hp he ((hM F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀).2 e he) hz.1 hH.rank
      hH'.xx fun m hm => ((hU F E σ B n n₁ X X₁ H j₀ j₁ _ _ hp.base (Or.inl hp.herm) hH).2.2.2.2.2.1 m hm).2)
    hle (hSt F E σ B n d X W M χX χW om _ _ _ _ hp)
    (fun Ψ hΨ h₁ => (key Ψ (hle Ψ hΨ)).1 om₀ (fun x Φ h => pair_pres hp₀ x h) (Or.inr ⟨domSo hS hV hE hp₀, hso Ψ hΨ⟩) h₁)
    (fun Ψ hΨ => (key Ψ hΨ).2) Φ hΦ hK

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.IsoActFree
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem units_sum {K : Type} [Field K] {a : K → ℂ} (ha : Summable a) : ∑' ξ : Kˣ, a ξ = ∑' x, a x - a 0 := by
  have h1 := ha.tsum_subtype_add_tsum_subtype_compl {0}
  rw [tsum_singleton] at h1
  rw [← h1, add_sub_cancel_left]
  exact (unitsEquivNeZero (G₀ := K)).tsum_eq fun x => a x.1

theorem orbit_sum {Γ I : Type} [Group Γ] [MulAction Γ I] (hfree : ∀ (ξ η : Γ) (x : I), ξ • x = η • x → ξ = η) {f : I → ℂ}
    (hf : Summable f) : ∑' x, f x = ∑' q : MulAction.orbitRel.Quotient Γ I, ∑' ξ : Γ, f (ξ • q.out) := by
  have hb : Function.Bijective fun y : MulAction.orbitRel.Quotient Γ I × Γ => y.2 • y.1.out := by
    constructor
    · rintro ⟨q, ξ⟩ ⟨q', η⟩ h
      dsimp only at h
      have : q = q' := by
        rw [← q.out_eq, ← q'.out_eq]
        exact Quotient.sound ⟨ξ⁻¹ * η, by dsimp only; rw [mul_smul, ← h, inv_smul_smul]⟩
      subst this
      rw [hfree _ _ _ h]
    · intro x
      obtain ⟨ξ, hξ⟩ : (Quotient.mk (MulAction.orbitRel Γ I) x).out ∈ MulAction.orbit Γ x := Quotient.mk_out (s := MulAction.orbitRel Γ I) x
      exact ⟨(Quotient.mk _ x, ξ⁻¹), by dsimp only at hξ ⊢; rw [← hξ, inv_smul_smul]⟩
  rw [← (Equiv.ofBijective _ hb).tsum_eq]
  exact ((Equiv.ofBijective _ hb).summable_iff.2 hf).tsum_prod

section

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem form_smul (J : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin n → E) : form σ J (c • x) (c • x) = c * σ c * form σ J x x := by
  simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

instance isoAct : MulAction Eˣ (IsoV σ X) where
  smul ξ x := ⟨(ξ : E) • x.1, smul_ne_zero ξ.ne_zero x.2.1, by rw [form_smul, x.2.2, mul_zero]⟩
  one_smul x := Subtype.ext (one_smul E x.1)
  mul_smul a b x := Subtype.ext (mul_smul (a : E) (b : E) x.1)

theorem isoAct_val (ξ : Eˣ) (x : IsoV σ X) : (ξ • x).1 = (ξ : E) • x.1 := rfl

theorem isoAct_free (ξ η : Eˣ) (x : IsoV σ X) (h : ξ • x = η • x) : ξ = η :=
  Units.ext (smul_left_injective E x.2.1 (congrArg Subtype.val h))

def conjE (hσ : IsCMExt F E σ) : Eˣ ≃ Eˣ where
  toFun := Units.map (σ : E →* E)
  invFun := Units.map (σ : E →* E)
  left_inv x := Units.ext (cm_conj_conj hσ x.1)
  right_inv x := Units.ext (cm_conj_conj hσ x.1)

abbrev idl (ξ : Eˣ) : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom ξ

theorem incV_smul (c : E) (x : Fin n → E) : incV F (c • x) = inclR (F := F) (AF F) c • incV F x := by
  funext i
  simp [incV]

theorem incM_smul (c : E) (x : Matrix (Fin n) (Fin d) E) : incM F (c • x) = inclR (F := F) (AF F) c • incM F x := by
  ext i j
  simp [incM]

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁}
  {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u : (AE F E)ˣ → Ten F E n d} {ν χ : Chr F E} {z : ℕ}
  {ι : (AE F E)ˣ → (AE F E)ˣ} {w : (AE F E)ˣ → ℂ} {χX χW : Chr F E} {r s r' s' r₀ s₀ r₀' s₀' : ℕ}

theorem LawsT.mult (h : LawsT B M om om₀ H H' e u w ι) (hD : StabDec) (hU : UnipEx) (hTB : ThetaBasic)
    (hp : IsPair B M χX χW om r s r' s') (hp₀ : IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀') {j₀ j₁} (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) Ψ) ∈ schA F (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    {γ} (hγ : Moves (σ := σ) (X := X) H γ) (y g) (x : IsoV σ X) (ξ η : Eˣ) (hη : ι (idl η) = idl ξ⁻¹) (hν : w (idl η) = 1) :
    thv B M om e (u 1) Φ y (γ (ξ • x) * g) = thetaSum F (e (M.co.rho B.ψ (u (idl η)) (om (γ x * g, y) Φ))) := by
  obtain ⟨-, -, -, -, ⟨lev, -, hlev, -⟩, -⟩ := hU F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH
  have hl := hlev (idl ξ⁻¹) 1
  have hr := (hD F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH).2.1 ξ⁻¹ 1 (one_mem _) _ hl
  set p := lev (idl ξ⁻¹, 1)
  have h1 : mat (p * γ x) *ᵥ incV F (ξ • x).1 = incV F H.x := by
    rw [mat_mul', ← Matrix.mulVec_mulVec, isoAct_val, incV_smul, Matrix.mulVec_smul, (hγ x).2, Matrix.mulVec_smul, hl.1, smul_smul]
    simp [← map_mul]
  have h2 := h.rat hD hTB hp hp₀ hH hs hΦ y (δ := γ (ξ • x) * (p * γ x)⁻¹)
    (mul_mem (hγ _).1 (inv_mem (mul_mem hr (hγ x).1)))
    (by rw [mat_mul', ← Matrix.mulVec_mulVec, mat_inv_mulVec _ h1, (hγ _).2]) (p * γ x * g)
  rw [show γ (ξ • x) * (p * γ x)⁻¹ * (p * γ x * g) = γ (ξ • x) * g by group] at h2
  have h3 := h.theta (l := idl η) (by rwa [hη]) (levi_one (W₁ := W₁) H') (pair_pres hp (γ x * g, y) hΦ)
  rw [hη, hν, GlobalTheory.Doubling.absE_inclR] at h3
  rw [h2]
  simpa [thv, om_mul, mul_assoc, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Prod.one_eq_mk] using h3

end

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.GenAnisoOf
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}

theorem dom_change (hG : GrpTop) (hE : EpsOf) (hB : B.IsGood σ) {r s : ℕ} (hX : X.IsHerm σ B r s)
    {m m' : Measure (UA σ X.J)} {D D' : Set (UA σ X.J)} (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure)
    (hd : IsFundamentalDomain (ratU σ X.J) D m) (hd' : IsFundamentalDomain (ratU σ X.J) D' m') :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : UA σ X.J → ℂ, (∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g) →
      ∫ g in D, φ g ∂m = c * ∫ g in D', φ g ∂m' := by
  obtain ⟨b1, b2, b3, b4, -⟩ := hG F E σ hB.cm n X.J (hE F E σ B hB n X r s (Or.inl hX)).1
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hc : m = Measure.haarScalarFactor m m' • m' := Measure.isMulLeftInvariant_eq_smul m m'
  have hpos : 0 < Measure.haarScalarFactor m m' := Measure.haarScalarFactor_pos_of_isHaarMeasure m m'
  have hac : m ≪ m' := by
    rw [hc]; exact Measure.smul_absolutelyContinuous
  have hd'' : IsFundamentalDomain (ratU σ X.J) D' m := hd'.mono hac
  refine ⟨((Measure.haarScalarFactor m m' : NNReal) : ℂ), ?_, fun φ hφ => ?_⟩
  · exact_mod_cast hpos.ne'
  · set_option synthInstance.maxHeartbeats 100000 in
    have h1 : ∫ g in D, φ g ∂m = ∫ g in D', φ g ∂m := hd.setIntegral_eq hd'' fun γ g => hφ γ γ.2 g
    rw [h1]
    conv_lhs => rw [hc]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]

theorem isLevi_one : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 1 :=
  ⟨by rw [mat_one', Matrix.one_mulVec, Units.val_one, one_smul],
    by rw [mat_one', Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul],
    by rw [mat_one', mat_one', Matrix.one_mul, Matrix.mul_one]⟩

theorem weil_bound (hW : WeilConv) {M : Model σ X W} {χX χW om r s r' s'} (hp : IsPair B M χX χW om r s r' s')
    (hr : d + 2 * min r s < 2 * n ∨ min r s = 0) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ (C : ℝ) (k : ℕ), ∀ h, ∫⁻ g in M.dom, ‖theta om Φ g h‖ₑ ∂M.μ ≤ ENNReal.ofReal (C * (ht h : ℝ) ^ k) := by
  obtain ⟨h1, C, k, h2⟩ := (hW F E σ B n d X W M χX χW om r s r' s' hp hr).1 Φ hΦ
  refine ⟨C, k, fun h => ?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm (h1 h)]
  exact ENNReal.ofReal_le_ofReal (h2 h)

theorem zero_term (hM : MixW) (hT : ThetaBasic) {M : Model σ X W} {M₁ : Model σ X W₁} {χX χW om om₁ r s r' s' r₁ s₁ i₀ i₁}
    (hp : IsPair B M χX χW om r s r' s') (hp₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    {e} (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) {c : ℂ} (hc : ∀ φ : UA σ X.J → ℂ, (∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g) →
      ∫ g in M.dom, φ g ∂M.μ = c * ∫ g in M₁.dom, φ g ∂M₁.μ) (C₀ : ℂ) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    HasLaw W₁ H' χX ((n : ℝ) / 2) (fun h => ∫ g in M.dom, C₀ * thetaSum F (e (om (g, h) Φ)) ∂M.μ) ∧
      ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h, ∫ g in M.dom, C₀ * thetaSum F (e (om (g, p * h) Φ)) ∂M.μ =
        C₀ * c * M₁.I om₁ (e (om (1, h) Φ)) h₁ := by
  have key : ∀ g t h₁ p, IsLevi H' t h₁ p → ∀ h, thetaSum F (e (om (g, p * h) Φ)) =
      (χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * theta om₁ (e (om (1, h) Φ)) g h₁ := fun g t h₁ p hl h => by
    have := hM F E σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hp₁ e he g t h₁ p hl 1 (one_mem _) _
      (pair_pres hp (1, h) hΦ)
    rw [om_mul, Prod.mk_mul_mk, mul_one, one_mul] at this
    rw [this, thetaSum_smul', theta]
  have key1 : ∀ g h₁ p, IsLevi H' 1 h₁ p → ∀ h, thetaSum F (e (om (g, p * h) Φ)) = theta om₁ (e (om (1, h) Φ)) g h₁ :=
    fun g h₁ p hl h => by rw [key g 1 h₁ p hl h]; simp
  refine ⟨fun t m hl h => ?_, fun h₁ p hl h => ?_⟩
  · simp only [key _ t 1 m hl h, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have := key1 g 1 1 isLevi_one h
    rw [one_mul] at this
    simp only [this]
    ring
  · obtain ⟨-, t2, -⟩ := (hT F E σ B n d₁ X W₁ M₁ χX χW om₁ r s r₁ s₁ hp₁).1 _ (he.maps _ (pair_pres hp (1, h) hΦ))
    simp only [key1 _ h₁ p hl h]
    rw [integral_const_mul, hc _ fun γ hγ g => by simpa using t2 γ hγ 1 (one_mem _) g h₁, mul_assoc, Model.I]

theorem genAniso_of (hK : CTKernel) (hF : CTFub) (hM : MixW) (hW : WeilConv) (hT : ThetaBasic) (hWi : Witt) (hG : GrpTop)
    (hE : EpsOf) : GenAniso := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ H' i₀ i₁ r s r' s' r₁ s₁ X' M M₁ hX hrs hH e he
  subst hX
  by_cases h0 : ∃ χX χW om om₁, IsPair B M χX χW om r s r' s' ∧ IsPair B M₁ χX χW om₁ r s r₁ s₁
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om om₁ h1 h2 => absurd ⟨χX, χW, om, om₁, h1, h2⟩ h0⟩
  obtain ⟨_, _, _, _, q, q₁⟩ := h0
  obtain ⟨C₀, hC₀, h1, -⟩ := hK F E σ B n d d₁ X' W W₁ M M₁ H' i₀ i₁ hH q₁.good e he
  obtain ⟨c, hc0, hc⟩ := dom_change hG hE q.base q.herm q.good.haar q₁.good.haar q.good.dom q₁.good.dom
  refine ⟨C₀ * c, mul_ne_zero hC₀ hc0, fun χX χW om om₁ hp hp₁ Φ hΦ => ?_⟩
  obtain ⟨z1, z2⟩ := zero_term hM hT hp hp₁ hH he hc C₀ hΦ
  exact ⟨_, (hF F E σ B n d X' W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ (weil_bound hW hp (Or.inr hrs) hΦ) _
    (h1 ((hWi F E σ B n X' r s hp.base hp.herm).1 hrs) χX χW om r s r' s' hp Φ hΦ)).2, z1, z2⟩

theorem genBig_of (hK : CTKernel) (hF : CTFub) (hA : ConeA) (hM : MixW) (hW : WeilConv) (hT : ThetaBasic) (hWi : Witt)
    (hG : GrpTop) (hE : EpsOf) : GenBig := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ e g₁ g₀ he₀ he z hz K μK μ hI hμK hμ
  by_cases h0 : ∃ χX χW om, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1)
  swap
  · exact ⟨1, 1, one_ne_zero, one_ne_zero, fun χX χW om _ _ h1 => absurd ⟨χX, χW, om, h1⟩ h0⟩
  obtain ⟨_, _, _, q⟩ := h0
  obtain ⟨C₀, hC₀, -, h1⟩ := hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' g₁ e₀ he₀
  obtain ⟨C₁, hC₁, h2⟩ := h1 n₁ X₁ H j₀ j₁ M₀ hH g₀ e he
  obtain ⟨κ, hκ, h3⟩ := hA F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨c, hc0, hc⟩ := dom_change hG hE q.base q.herm q.good.haar g₁.haar q.good.dom g₁.dom
  obtain ⟨γ, hγ⟩ := (hWi F E σ B n X _ _ q.base q.herm).2 n₁ H (adapted_x_ne hH) hH.xx
  refine ⟨C₀ * c, C₁ * κ, mul_ne_zero hC₀ hc0, mul_ne_zero hC₁ hκ, fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ hfin => ?_⟩
  obtain ⟨z1, z2⟩ := zero_term hM hT hp hp₁ hH' he₀ hc C₀ hΦ
  obtain ⟨a1, a2, a3⟩ := h3 χX χW om om₀ hp hp₀ Φ hΦ hfin
  obtain ⟨f1, f2⟩ := hF F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ hH' Φ hΦ
    (weil_bound hW hp (Or.inl (by omega)) hΦ) _ fun g => (h2 γ hγ χX χW om _ _ _ _ hp Φ hΦ g).2
  refine ⟨_, fun h => C₁ * κ * coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) 1, ?_, z1,
    fun t m hl h => ?_, fun h₁ p hl h => ⟨?_, z2 h₁ p hl h⟩⟩
  · convert f2 using 1
    funext h
    obtain ⟨-, b2, b3⟩ := a1 γ hγ h
    have b4 := b2.const_mul C₁
    have b5 := (f1 h).sub b4
    rw [Pi.add_apply, mul_assoc, ← b3, ← integral_const_mul, ← integral_add _ b4]
    · rfl
    · refine b5.congr (Eventually.of_forall fun g => ?_)
      exact add_sub_cancel_right _ _
  · simp only [a2 t 1 m hl h]
    ring
  · simp only [a2 1 h₁ p hl h, a3]
    simp

end PositivityTheory.ThKCT
end
end

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem genSmall_of (hK : CTKernel) (hF : CTFub) (hCB : ConeB) (h2 : TwoExp) (hM : MixAB) (hMW : MixW) (hC : EvCone) (hWi : Witt)
    (hD : StabDec) (hU : UnipEx) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hSD : SoDecay) (hV : FinVolU) (hSF : SoFin)
    (hSt : SoStab) (hZ : SoZeroA') (hSe : SoEv) : GenSmall := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eB hM₁ hM₀ he₀ heB z hz K μK μ hI hμK hμ
  by_cases hex : ∃ χX χW om, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1)
  swap
  · exact ⟨1, 1, one_ne_zero, one_ne_zero, fun χX χW om _ _ hp => absurd ⟨χX, χW, om, hp⟩ hex⟩
  obtain ⟨χ0, χ0', o, hq⟩ := hex
  obtain ⟨⟨eA, heA⟩, -⟩ := hC F E σ B n d X W M χ0 χ0' o _ _ _ _ hq _ _ X₁ W₁ H H' i₀ i₁ j₀ j₁ M₀ hH hH' hM₀
  obtain ⟨C₀, hC₀, -, hK1⟩ := hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀
  obtain ⟨C₁, hC₁, hK2⟩ := hK1 n₁ X₁ H j₀ j₁ M₀ hH hM₀ eA heA
  obtain ⟨c, hc, h2'⟩ := h2 F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hq.base hq.herm hq.skew hq.good hM₀
    eA eB heA heB
  obtain ⟨κ, hκ, hB⟩ := hCB F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' eB heB z hz K μK μ hI hμK hμ
  obtain ⟨γ, hγ⟩ := (hWi F E σ B n X _ _ hq.base hq.herm).2 n₁ H (adapted_x_ne hH) hH.xx
  obtain ⟨κ₁, hκ₁, hch⟩ := dom_change hG hE hq.base hq.herm hq.good.haar hM₁.haar hq.good.dom hM₁.dom
  refine ⟨C₀ * κ₁, C₁ * c * κ, mul_ne_zero hC₀ hκ₁, mul_ne_zero (mul_ne_zero hC₁ hc) hκ,
    fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ hfin => ?_⟩
  have hle := (hSF F E σ B n d X W M χX χW om _ _ _ _ hp).2.2.1
  have hs := hle Φ hΦ
  have hst := hSt F E σ B n d X W M χX χW om _ _ _ _ hp
  obtain ⟨hmA, hmB⟩ := hM F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀
  replace hmA := hmA eA heA
  have hu := (hU F E σ B n n₁ X X₁ H j₀ j₁ _ _ hp.base (Or.inl hp.herm) hH).2.2.2.2.2.1
  have lB := lawsB hp heB (hmB eB heB) hz.1 hH.rank hH'.xx fun m hm => (hu m hm).2
  obtain ⟨b1, b2, b3⟩ := hB χX χW om om₀ hp hp₀ Φ hΦ hfin
  replace b1 := b1 γ hγ
  have k1 := hK2 γ hγ χX χW om _ _ _ _ hp Φ hs
  have hsch : ∀ {I e}, IsEv B M M₀ H.ι H'.ι I e → ∀ w, ∀ Ψ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ w Ψ) ∈ schA F (Fin n₁ × Fin d₁) := fun he w Ψ h => he.maps _ (rho_mem M hp.base.std w h)
  set L : UA σ X.J → UA σ W.J → ℂ := fun g h =>
    ∑' q : MulAction.orbitRel.Quotient Eˣ (IsoV σ X), -thetaSum F (eA (om (γ q.out * g, h) Φ)) with hL
  have hlines : ∀ g h, (Summable fun x => thv B M om eB (shiftB σ H H' 1) Φ h (γ x * g)) →
      ∑' x, thv B M om eA (shiftA H H' 1) Φ h (γ x * g) - c * ∑' x, thv B M om eB (shiftB σ H H' 1) Φ h (γ x * g) = L g h := by
    intro g h hsB
    have hsA : Summable fun x => thv B M om eA (shiftA H H' 1) Φ h (γ x * g) := (k1 g).1 h
    rw [← tsum_mul_left, ← hsA.tsum_sub (hsB.mul_left c), orbit_sum isoAct_free (hsA.sub (hsB.mul_left c))]
    refine tsum_congr fun q => ?_
    have hΨ := pair_pres hp (γ q.out * g, h) hs
    obtain ⟨sA, sB, e2⟩ := h2' _ hΨ
    have vA : ∀ ξ : Eˣ, thv B M om eA (shiftA H H' 1) Φ h (γ (ξ • q.out) * g) =
        thetaSum F (eA (M.co.rho B.ψ (incM F ((ξ : E) • Matrix.vecMulVec H.x H'.y)) (om (γ q.out * g, h) Φ))) := fun ξ => by
      rw [(lawsTA hp hmA fun m hm => (hu m hm).1).mult hD hU hTB hp hp₀ hH (hsch heA _) hs hγ h g q.out ξ ξ (map_inv _ _).symm
        (by simp only [MonoidHom.inv_apply, hp.hW.2 ξ, GlobalTheory.Doubling.absE_inclR]; simp), incM_smul, incM_vecMulVec]
      rfl
    let φ : Eˣ ≃ Eˣ := (Equiv.inv Eˣ).trans (conjE hp.base.cm)
    have vB : ∀ ξ : Eˣ, thv B M om eB (shiftB σ H H' 1) Φ h (γ (ξ • q.out) * g) =
        thetaSum F (eB (M.co.rho B.ψ (incM F ((φ ξ : E) • Matrix.vecMulVec H.y H'.x)) (om (γ q.out * g, h) Φ))) := fun ξ => by
      rw [lB.toLawsT.mult hD hU hTB hp hp₀ hH (hsch heB _) hs hγ h g q.out ξ ξ⁻¹ rfl
        (by simp only [hp.hW.2 ξ⁻¹, GlobalTheory.Doubling.absE_inclR]; simp), incM_smul, incM_vecMulVec, shiftB]
      congr 4
    simp only [vA, vB]
    have sA' : Summable fun ξ : Eˣ => thetaSum F (eA (M.co.rho B.ψ (incM F ((ξ : E) • Matrix.vecMulVec H.x H'.y))
        (om (γ q.out * g, h) Φ))) := sA.comp_injective Units.val_injective
    have sB' : Summable fun ξ : Eˣ => thetaSum F (eB (M.co.rho B.ψ (incM F ((φ ξ : E) • Matrix.vecMulVec H.y H'.x))
        (om (γ q.out * g, h) Φ))) := (sB.comp_injective Units.val_injective).comp_injective φ.injective
    rw [sA'.tsum_sub (sB'.mul_left c), tsum_mul_left,
      φ.tsum_eq fun ξ : Eˣ => thetaSum F (eB (M.co.rho B.ψ (incM F ((ξ : E) • Matrix.vecMulVec H.y H'.x)) (om (γ q.out * g, h) Φ))),
      units_sum sA, units_sum sB, e2]
    have z0 : ∀ v : Matrix (Fin n) (Fin d) E, incM F ((0 : E) • v) = 0 := fun v => by rw [incM_smul, map_zero, zero_smul]
    have zB := (hSe F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hp.base hp.herm hp.skew hp.good hM₀ eB heB _
      (hst (γ q.out * g, h) Φ hΦ)).1
    simp only [z0, rho_zero, zB]
    simp [thetaSum]
  obtain ⟨Cd, kd, hdec⟩ := hSD F E σ B n d X W M χX χW om _ _ _ _ hp Φ hΦ 0
  have hvol := hV F E σ hp.base.cm n X.J (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1 M.μ M.dom hp.good.haar hp.good.dom
  obtain ⟨f1, f2⟩ := hF F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ hH' Φ hs
    ⟨Cd * (M.μ M.dom).toReal, kd, fun h => by
      calc _ ≤ ∫⁻ _ in M.dom, ENNReal.ofReal (Cd * (ht h : ℝ) ^ kd) ∂M.μ := lintegral_mono fun g => by
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (by simpa using hdec g h)
        _ = _ := by
            rw [setLIntegral_const, mul_right_comm, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvol.ne]⟩
    _ fun g => (k1 g).2
  refine ⟨fun h => ∫ g in M.dom, (C₀ * thetaSum F (e₀ (om (g, h) Φ)) + C₁ * L g h) ∂M.μ,
    fun h => C₁ * c * κ * coneI B M om M₀ om₀ eB K μK μ (shiftB σ H H') χW z (om (1, h) Φ) 1, ?_, fun t m hm h => ?_,
    fun t m hm h => by dsimp only; rw [b2 t 1 m hm h]; ring, fun h₁ p hl h => ⟨?_, fun hso => ?_⟩⟩
  · convert f2 using 1
    funext h
    obtain ⟨a1, a2, a3⟩ := b1 h
    rw [Pi.add_apply, mul_assoc (C₁ * c), ← a3, ← integral_const_mul, ← eq_sub_iff_add_eq, ← integral_sub (f1 h) (a2.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [a1] with g hg
    rw [← hlines g h hg]
    simp only [thv]
    ring
  · dsimp only
    rw [← integral_const_mul]
    congr 1
    funext g
    have m1 : ∀ g', om (g', m * h) Φ = om (1, m) (om (g', h) Φ) := fun g' => by simp [om_mul]
    have m2 := hMW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ 1 t 1 m hm 1 (one_mem _) _
      (pair_pres hp (g, h) hs)
    rw [one_mul] at m2
    simp only [hL, m1, m2, hmA.levi (levi_one H) hm (pair_pres hp _ hs), thetaSum_smul', ← Prod.one_eq_mk, map_one,
      Module.End.one_apply, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, one_mul, ← mul_neg, tsum_mul_left]
    ring
  · dsimp only
    rw [b2 1 h₁ p hl h, b3]
    simp
  · have hz0 : ∀ g, L g (p * h) = 0 := fun g => by
      have : ∀ g', eA (om (g', p * h) Φ) = 0 := fun g' => by
        refine hZ F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ _ _ _ _ M M₀ hH hH' hp.base hp.herm hp.skew hp.good hM₀ M₁ hM₁
          ⟨χX, χW, om₁, om₀, _, _, _, _, _, _, hp₁, hp₀⟩ e₀ eA he₀ heA _ (pair_pres hp _ hs) ?_
        have m2 := hMW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ g' 1 h₁ p hl 1 (one_mem _) _
          (pair_pres hp (1, h) hs)
        rw [one_mul, om_mul, Prod.mk_mul_mk, mul_one] at m2
        rw [m2]
        exact Submodule.smul_mem _ _ (hSt F E σ B n d₁ X W₁ M₁ χX χW om₁ _ _ _ _ hp₁ _ _ hso)
      simp [hL, this, thetaSum]
    simp only [hz0, mul_zero, add_zero]
    exact (zero_term hMW hTB hp hp₁ hH' he₀ hch C₀ hs).2 h₁ p hl h

end PositivityTheory.ThKCT

end

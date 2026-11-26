module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIffMulNormInvAlg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIffMulNormInvAlg
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLatInj

open GlobalTheory.TwOrbLat GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem invT_invT (h : GLw m w) : invT m _ (invT m _ h) = h :=
  Units.ext (by change (h.val)ᵀᵀ = h.val; exact transpose_transpose _)

theorem invT_injective : Function.Injective (invT m (w.adicCompletion E)) := fun x y hxy => by
  rw [← invT_invT x, hxy, invT_invT]

theorem dlt_eq_iff (hw : ¬ IsSplitAt w) (β β' : B.A) (hβ : IsUnit (GlobalTheory.TwLat.gram e b β)) (hβ' : IsUnit (GlobalTheory.TwLat.gram e b β'))
    (g : GLw m w) :
    GlobalTheory.TwLat.dlt e b β' = g⁻¹ * GlobalTheory.TwLat.dlt e b β * thL m w g ↔ g.valᵀ * GlobalTheory.TwLat.gram e b β * g.val.map (cj w) = GlobalTheory.TwLat.gram e b β' := by
  unfold GlobalTheory.TwLat.dlt
  rw [dite_eq_left hβ, dite_eq_left hβ']
  have hth : thL m w g = PhiU m _ * invT m _ (GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ := by
    simp only [thL, if_neg hw]; rfl
  have hinv : g⁻¹ = invT m _ (invT m _ g⁻¹) := (invT_invT _).symm
  have key : g⁻¹ * (invT m _ hβ.unit * (PhiU m _)⁻¹) * thL m w g =
      invT m _ (invT m _ g⁻¹ * hβ.unit * GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ := by
    rw [hth, map_mul, map_mul, ← hinv]; group
  rw [key, mul_left_inj, invT_injective.eq_iff, Units.ext_iff, eq_comm]
  rfl

theorem herm_sum_left (β z : B.A) (f : Fin m → B.A) : B.herm β (∑ i, f i) z = ∑ i, B.herm β (f i) z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (β y : B.A) (f : Fin m → B.A) : B.herm β y (∑ i, f i) = ∑ i, B.herm β y (f i) := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_sub_left (β y y' z : B.A) : B.herm β (y - y') z = B.herm β y z - B.herm β y' z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  rw [mul_sub, sub_mul, map_sub]

theorem herm_crd (he : ∀ x, e (K.c x) = cj w (e x)) (β y z : B.A) :
    e (B.herm β y z) = crd e b y ⬝ᵥ (GlobalTheory.TwLat.gram e b β *ᵥ fun l => cj w (crd e b z l)) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, map_sum,
    map_mul, he]
  simp only [dotProduct, mulVec, crd, GlobalTheory.TwLat.gram, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cj_cj (he : ∀ x, e (K.c x) = cj w (e x)) (z : w.adicCompletion E) : cj w (cj w z) = z := by
  obtain ⟨k, rfl⟩ := e.surjective z
  rw [← he, ← he, K.c_c]

theorem eq_zero_of_herm (he : ∀ x, e (K.c x) = cj w (e x)) (β : B.A) (hβ : IsUnit (GlobalTheory.TwLat.gram e b β)) (d : B.A)
    (hd : ∀ t, B.herm β d t = 0) : d = 0 := by
  have h1 : ∀ v, (crd e b d ᵥ* GlobalTheory.TwLat.gram e b β) ⬝ᵥ v = 0 := by
    intro v
    have h := congrArg e (hd (ofCrd e b fun l => cj w (v l)))
    rw [herm_crd e b he, map_zero, dotProduct_mulVec] at h
    have hv : (fun l => cj w (crd e b (ofCrd e b fun l => cj w (v l)) l)) = v := by
      funext l; rw [crd_ofCrd, cj_cj e he]
    rwa [hv] at h
  have h2 : crd e b d ᵥ* GlobalTheory.TwLat.gram e b β = 0 := by
    funext j
    have := h1 (Pi.single j 1)
    simpa [dotProduct_single] using this
  have h3 : crd e b d = 0 := by
    have : crd e b d = (crd e b d ᵥ* (hβ.unit : Matrix (Fin m) (Fin m) (w.adicCompletion E))) ᵥ*
        ((hβ.unit⁻¹ : (Matrix (Fin m) (Fin m) (w.adicCompletion E))ˣ) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
      rw [vecMul_vecMul, Units.mul_inv, vecMul_one]
    rw [this, IsUnit.unit_spec, h2, zero_vecMul]
  apply crd_injective e b
  rw [h3]; funext i; simp [crd]

end GlobalTheory.TwLatInj

namespace GlobalTheory.TwLatInj

open GlobalTheory.TwOrbLat GlobalTheory.TwLat

theorem dlt_twConj_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) →
    (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) →
    ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u : B.A,
    Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) →
    (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ x x' : B.Aˣ, B.σ (x : B.A) = x →
    B.σ (x' : B.A) = x' →
    ((∃ g : GLw m w, GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x') = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g) ↔
      ∃ a : B.Aˣ, (x' : B.A) = x * (a * B.σ a)) := by
  intro E _ _ _ _ w hw K e he _ _ B m b u hu β₀ hβ₀ hG x x' hx hx'
  obtain ⟨ε, hε⟩ : ∃ ε : B.A, ε = (-1) ^ (m - 1) := ⟨_, rfl⟩
  rw [← hε] at hβ₀
  have hε2 : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hεa : ε = algebraMap K.E B.A ((-1) ^ (m - 1)) := by rw [hε]; simp

  have hasym : ∀ t : B.A, B.σ t = t → ∀ y z, K.c (B.herm ((β₀ : B.A) * t) y z) =
      B.herm ((β₀ : B.A) * t) (ε * u * z) y := by
    intro t ht y z
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    rw [← GlobalTheory.UnitLemma.Basic.trace_sigma, map_mul B.σ, map_mul B.σ, map_mul B.σ, hβ₀, ht, B.σ_σ]
    congr 1; ring
  constructor
  · rintro ⟨g, hg⟩
    rw [dlt_eq_iff e b hw _ _ (hG x) (hG x') g] at hg
    let φ : B.A → B.A := fun a => ofCrd e b (g.val *ᵥ crd e b a)
    have hcφ : ∀ a, crd e b (φ a) = g.val *ᵥ crd e b a := fun a => crd_ofCrd e b _
    have hφs : ∀ (k : K.E) (a : B.A), φ (k • a) = k • φ a := by
      intro k a; apply crd_injective e b; rw [hcφ, crd_smul, crd_smul, hcφ, mulVec_smul]
    have hφadd : ∀ a a', φ (a + a') = φ a + φ a' := by
      intro a a'; apply crd_injective e b; rw [hcφ, crd_add, crd_add, hcφ, hcφ, mulVec_add]
    have hφsurj : ∀ t, φ (ofCrd e b ((g⁻¹ : GLw m w).val *ᵥ crd e b t)) = t := by
      intro t; apply crd_injective e b
      rw [hcφ, crd_ofCrd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

    have hiso : ∀ y z, B.herm ((β₀ : B.A) * x) (φ y) (φ z) = B.herm ((β₀ : B.A) * x') y z := by
      intro y z; apply e.injective
      rw [herm_crd e b he, herm_crd e b he, hcφ, hcφ, ← hg]
      have hc : (fun l => cj w ((g.val *ᵥ crd e b z) l)) = g.val.map (cj w) *ᵥ fun l => cj w (crd e b z l) := by
        funext l; exact RingHom.map_mulVec (cj w) g.val (crd e b z) l
      have ht : g.val *ᵥ crd e b y = crd e b y ᵥ* g.valᵀ := (vecMul_transpose _ _).symm
      rw [hc, ht]
      simp only [dotProduct_mulVec, vecMul_vecMul]

    have hv : ∀ z, φ (ε * u * z) = ε * u * φ z := by
      intro z
      have key : ∀ y, B.herm ((β₀ : B.A) * x) (φ (ε * u * z) - ε * u * φ z) (φ y) = 0 := by
        intro y
        rw [herm_sub_left, hiso, ← hasym x' hx', ← hiso, hasym x hx, sub_self]
      exact sub_eq_zero.1 (eq_zero_of_herm e b he _ (hG x) _ fun t => by rw [← hφsurj t]; exact key _)
    have hφu : ∀ z, φ (u * z) = u * φ z := by
      intro z
      have h1 : φ (ε * u * z) = ε * φ (u * z) := by
        rw [mul_assoc, hεa, ← Algebra.smul_def, ← Algebra.smul_def, hφs]
      have h2 := (hv z).symm.trans h1
      linear_combination (-ε) * h2 - (φ (u * z) - u * φ z) * hε2
    have hφmul : ∀ a c, φ (a * c) = a * φ c := by
      intro a
      have ha : a ∈ Algebra.adjoin K.E {u} := by rw [hu]; trivial
      induction ha using Algebra.adjoin_induction with
      | mem z hz =>
        rw [Set.mem_singleton_iff] at hz; subst hz; exact hφu
      | algebraMap r =>
        intro c; rw [← Algebra.smul_def, ← Algebra.smul_def, hφs]
      | add a₁ a₂ _ _ h₁ h₂ =>
        intro c; rw [add_mul, hφadd, h₁, h₂, add_mul]
      | mul a₁ a₂ _ _ h₁ h₂ =>
        intro c; rw [mul_assoc, h₁, h₂, mul_assoc]
    have hφ : ∀ a, φ a = a * φ 1 := fun a => by rw [← hφmul, mul_one]
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, φ a₀ = 1 := ⟨_, hφsurj 1⟩
    let c : B.Aˣ := ⟨φ 1, a₀, by rw [mul_comm, ← hφ, ha₀], by rw [← hφ, ha₀]⟩
    refine ⟨c, ?_⟩
    have hc : (c : B.A) = φ 1 := rfl
    have hxx : (x : B.A) * ((x⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv x
    have hd : ∀ t, B.herm ((β₀ : B.A) * x) (((x⁻¹ : B.Aˣ) : B.A) * (x' - x * (c * B.σ c))) t = 0 := by
      intro t
      have h1 := hiso 1 t
      rw [hφ t, ← hc] at h1
      unfold GlobalTheory.UnitLemma.InvAlg.herm at h1 ⊢
      have h3 : (β₀ : B.A) * x * (((x⁻¹ : B.Aˣ) : B.A) * (x' - x * (c * B.σ c))) * B.σ t =
          (β₀ : B.A) * x' * 1 * B.σ t - (β₀ : B.A) * x * c * B.σ (t * c) := by
        rw [map_mul B.σ]
        linear_combination ((β₀ : B.A) * (x' - x * (c * B.σ c)) * B.σ t) * hxx
      rw [h3, map_sub, h1, sub_self]
    have h0 := eq_zero_of_herm e b he _ (hG x) _ hd
    have : (x' : B.A) - x * (c * B.σ c) = 0 := by
      rw [← one_mul ((x' : B.A) - _), ← hxx, mul_assoc, h0, mul_zero]
    exact sub_eq_zero.1 this
  · rintro ⟨a, ha⟩
    refine ⟨mulGL e b a, ?_⟩
    rw [dlt_eq_iff e b hw _ _ (hG x) (hG x')]
    ext i j
    have h1 : GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x') i j = e (B.herm ((β₀ : B.A) * x) (a * b i) (a * b j)) := by
      simp only [GlobalTheory.TwLat.gram, Matrix.of_apply]
      rw [ha, ← mul_assoc, GlobalTheory.UnitLemma.Basic.herm_norm]
    rw [h1, herm_crd e b he]
    have hcol : ∀ i, crd e b ((a : B.A) * b i) = fun k => (mulGL e b a).val k i := by
      intro i; funext k; rw [mulGL_val, ← mulHom_eq, mulHom_apply]; rfl
    rw [hcol, hcol]
    congr 1
    simp only [dotProduct, mulVec, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]

end GlobalTheory.TwLatInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIffMulNormInvAlgStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedConj_iff_mul_norm_invAlg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u : B.A, Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) → (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ x x' : B.Aˣ, B.σ (x : B.A) = x → B.σ (x' : B.A) = x' → ((∃ g : GLw m w, GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x') = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g) ↔ ∃ a : B.Aˣ, (x' : B.A) = x * (a * B.σ a)) := by
  first | exact @GlobalTheory.TwLatInj.dlt_twConj_iff | exact GlobalTheory.TwLatInj.dlt_twConj_iff | (intros; apply GlobalTheory.TwLatInj.dlt_twConj_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDet
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat

open GlobalTheory.UnitLemma

theorem model_aeval_mulVec {K : UQ} {L : Type} [Field L] (e : K.E ≃+* L) {B : InvAlg K} {n : ℕ}
    (ψ : B.A ≃+ (Fin n → L)) (hs : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (u : B.A)
    (g : Matrix (Fin n) (Fin n) L) (hu : ∀ y, ψ (u * y) = g *ᵥ ψ y) (p : K.E[X]) (y : B.A) :
    ψ (aeval u p * y) = aeval g (p.map (e : K.E →+* L)) *ᵥ ψ y := by
  induction p using Polynomial.induction_on generalizing y with
  | C a =>
    rw [aeval_C, ← Algebra.smul_def, hs, Polynomial.map_C, aeval_C, Algebra.algebraMap_eq_smul_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  | add p q hp hq =>
    rw [map_add (f := _), add_mul, map_add (f := _), hp, hq, Polynomial.map_add (f := _), map_add (f := _), Matrix.add_mulVec]
  | monomial k a h =>
    have h1 : aeval u (C a * X ^ (k + 1)) = aeval u (C a * X ^ k) * u := by
      rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, aeval_X]
    have h2 : aeval g ((C a * X ^ (k + 1)).map (e : K.E →+* L)) = aeval g ((C a * X ^ k).map (e : K.E →+* L)) * g := by
      rw [pow_succ, ← mul_assoc, Polynomial.map_mul, Polynomial.map_X, Polynomial.aeval_mul, aeval_X]
    rw [h1, h2, mul_assoc, h, hu, Matrix.mulVec_mulVec]

theorem prod_herm_fst {K : UQ} (B₁ B₂ : InvAlg K) (x : (B₁.prod B₂).A) (y z : B₁.A) :
    (B₁.prod B₂).herm x ((y, 0) : B₁.A × B₂.A) ((z, 0) : B₁.A × B₂.A) = B₁.herm x.1 y z := by
  unfold InvAlg.herm
  have hel : x * (show (B₁.prod B₂).A from (y, 0)) * (B₁.prod B₂).σ (show (B₁.prod B₂).A from (z, 0)) =
      (show (B₁.prod B₂).A from (x.1 * y * B₁.σ z, 0)) := by
    refine Prod.ext rfl ?_
    show x.2 * 0 * B₂.σ 0 = 0
    simp
  rw [hel]
  exact (Algebra.trace_prod_apply (R := K.E) ((x.1 * y * B₁.σ z, 0) : B₁.A × B₂.A)).trans (by simp)

theorem neg_one_zpow_val_norm_mul (K : UQ) (d g : K.E) (hd : d ≠ 0) :
    (-1 : ℂ) ^ val K.O (d * g * K.c d) = ((K.eta g : ℚ) : ℂ) := by
  unfold UQ.eta
  by_cases hg : g = 0
  · subst hg; simp
  have hval : ∀ a b : K.E, a ≠ 0 → b ≠ 0 → val K.O (a * b) = val K.O a + val K.O b := by
    intro a b ha hb
    unfold val
    rw [Valuation.map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
    ring
  have hcd : K.c d ≠ 0 := by simpa using hd
  rw [hval _ _ (mul_ne_zero hd hg) hcd, hval _ _ hd hg, UnramNorm.val_c]
  have h2 : (-1 : ℂ) ^ (val K.O d + val K.O g + val K.O d) = (-1 : ℂ) ^ val K.O g := by
    rw [show val K.O d + val K.O g + val K.O d = 2 * val K.O d + val K.O g by ring,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
    norm_num
  rw [h2]
  push_cast
  rfl

end GlobalTheory.KapLat

namespace GlobalTheory.KapLat

open GlobalTheory.UnitLemma

theorem kapSign_eq_eta_gramDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → ∀ (x : (B₁.prod B₂).A) (γ : GLw n w), IsModel w e (B₁.prod B₂) ((u₁, u₂) : B₁.A × B₂.A) x γ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet x.1) : ℚ) : ℂ) := by
  intro E _ _ _ w hns K e hB n Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂ x γ hM
  obtain ⟨ψ, hs, hu, hh⟩ := hM
  obtain ⟨-, -, hval, -⟩ := hB
  set P₁ : K.E[X] := Q₁.map e.symm.toRingHom with hP₁
  have hQ₁ : Q₁ = P₁.map (e : K.E →+* w.adicCompletion E) := by
    rw [hP₁, Polynomial.map_map]
    ext i
    simp
  have hunit : IsUnit (aeval u₂ P₁) := by
    obtain ⟨a, b, hab⟩ := hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
    have h := congrArg (aeval u₂) hab
    simp only [Polynomial.coe_mapRingHom, map_add (f := _), map_mul, map_one] at h
    rw [hF₂.2.1, mul_zero, add_zero] at h
    exact ⟨⟨aeval u₂ P₁, aeval u₂ a, by rw [mul_comm]; exact h, h⟩, rfl⟩
  have hker : ∀ y : (B₁.prod B₂).A, aeval γ.val Q₁ *ᵥ ψ y = 0 ↔ y.2 = 0 := by
    intro y
    rw [hQ₁, ← model_aeval_mulVec e ψ hs _ γ.val hu P₁ y, AddEquiv.map_eq_zero_iff]
    have hp1 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).1 = aeval u₁ P₁ :=
      (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) P₁).symm
    have hp2 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).2 = aeval u₂ P₁ :=
      (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) P₁).symm
    have h1 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁ * y).2 = aeval u₂ P₁ * y.2 := by
      rw [← hp2]; rfl
    have h0 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁ * y).1 = 0 := by
      show (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).1 * y.1 = 0
      rw [hp1, hF₁.2.1, zero_mul]
    constructor
    · intro h
      have h2 := congrArg Prod.snd h
      rw [h1] at h2
      exact hunit.mul_right_eq_zero.mp h2
    · intro h
      exact Prod.ext h0 (by rw [h1, h, mul_zero]; rfl)
  unfold kapSign
  rw [if_neg hns]
  dsimp only
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val Q₁)) with hV₁
  set m := Module.finrank (w.adicCompletion E) V₁ with hm
  set v := Module.finBasis (w.adicCompletion E) V₁ with hv
  have hmem : ∀ y : (B₁.prod B₂).A, ψ y ∈ V₁ ↔ y.2 = 0 := fun y => by
    rw [hV₁, LinearMap.mem_ker, Matrix.toLin'_apply, hker]
  let ψ₁ : B₁.A →+ (Fin n → w.adicCompletion E) :=
    AddMonoidHom.mk' (fun z => ψ (show (B₁.prod B₂).A from (z, 0))) (fun z z' => by
      rw [← map_add (f := _)]
      congr 1
      exact Prod.ext rfl (show (0 : B₂.A) = 0 + 0 by simp))
  have hψ₁ : ∀ z, ψ₁ z = ψ (show (B₁.prod B₂).A from (z, 0)) := fun z => rfl
  have hψ₁s : ∀ (c : K.E) z, ψ₁ (c • z) = e c • ψ₁ z := by
    intro c z
    rw [hψ₁, hψ₁, ← hs]
    congr 1
    exact Prod.ext rfl (show (0 : B₂.A) = c • 0 by simp)
  have hψ₁i : Function.Injective ψ₁ := by
    intro z z' hzz
    rw [hψ₁, hψ₁] at hzz
    exact congrArg Prod.fst (ψ.injective hzz)
  let a' : Fin m → B₁.A := fun i => (ψ.symm (v i : Fin n → w.adicCompletion E)).1
  have hva : ∀ i, ψ₁ (a' i) = v i := by
    intro i
    have h2 : (ψ.symm (v i : Fin n → w.adicCompletion E)).2 = 0 :=
      (hmem _).1 (by rw [ψ.apply_symm_apply]; exact (v i).2)
    have h3 : (show (B₁.prod B₂).A from (a' i, 0)) = ψ.symm (v i) := Prod.ext rfl h2.symm
    rw [hψ₁, h3, ψ.apply_symm_apply]
  have hsum : ∀ g : Fin m → K.E, ψ₁ (∑ i, g i • a' i) = ∑ i, e (g i) • (v i : Fin n → w.adicCompletion E) := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hψ₁s, hva]
  have hli : LinearIndependent K.E a' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : ∑ j, e (g j) • v j = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← hsum g, hg, map_zero]
      rfl
    have := Fintype.linearIndependent_iff.mp v.linearIndependent _ h0 i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range a') := by
    intro z _
    have hz : ψ₁ z ∈ V₁ := (hmem _).2 rfl
    have hrep := congrArg Subtype.val (v.sum_repr ⟨ψ₁ z, hz⟩)
    rw [Submodule.coe_sum] at hrep
    simp only [Submodule.coe_smul] at hrep
    have hz' : z = ∑ i, e.symm (v.repr ⟨ψ₁ z, hz⟩ i) • a' i := by
      apply hψ₁i
      rw [hsum]
      simp only [RingEquiv.apply_symm_apply]
      exact hrep.symm
    rw [hz']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let hb : Module.Basis (Fin m) K.E B₁.A := Module.Basis.mk hli hsp
  have hbapp : ⇑hb = a' := funext fun i => Module.Basis.mk_apply hli hsp i
  have hdm : Module.finrank K.E B₁.A = m := by
    rw [Module.finrank_eq_card_basis hb, Fintype.card_fin]
  let bm := (Module.finBasis K.E B₁.A).reindex (finCongr hdm)
  have hgram : B₁.gramDet x.1 = (Matrix.of fun i j => B₁.herm x.1 (bm i) (bm j)).det := by
    unfold InvAlg.gramDet
    rw [← Matrix.det_reindex_self (finCongr hdm)]
    congr 1
    ext i j
    simp [bm, Module.Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hdetM : IsUnit (bm.toMatrix a').det := by
    have h := bm.isUnit_det hb
    rwa [Module.Basis.det_apply, hbapp] at h
  have hGa := GlobalTheory.GramChange.gram_of_sum K B₁ K.E (RingEquiv.refl K.E) (K.c : K.E →+* K.E) (fun _ => rfl) x.1 bm a'
    (bm.toMatrix a') (fun j => (bm.sum_toMatrix_smul_self a' j).symm)
  have e1 : (bm.toMatrix a').map (RingEquiv.refl K.E) = bm.toMatrix a' := Matrix.ext fun _ _ => rfl
  rw [e1] at hGa
  have e2 : ((bm.toMatrix a').map (K.c : K.E →+* K.E)).det = K.c (bm.toMatrix a').det :=
    (RingHom.map_det (K.c : K.E →+* K.E) (bm.toMatrix a')).symm
  have hdetG : (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det =
      (bm.toMatrix a').det * B₁.gramDet x.1 * K.c (bm.toMatrix a').det := by
    calc (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det
        = (Matrix.of fun i j => (RingEquiv.refl K.E) (B₁.herm x.1 (a' i) (a' j))).det := rfl
      _ = ((bm.toMatrix a')ᵀ * (Matrix.of fun i j => (RingEquiv.refl K.E) (B₁.herm x.1 (bm i) (bm j))) *
            (bm.toMatrix a').map (K.c : K.E →+* K.E)).det := by rw [hGa]
      _ = _ := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e2, hgram]
        rfl
  have hK : (Matrix.of fun i j => ∑ k, cj w ((v i : Fin n → w.adicCompletion E) k) * (v j : Fin n → w.adicCompletion E) k) =
      (Matrix.of fun i j => e (B₁.herm x.1 (a' i) (a' j)))ᵀ := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    calc _ = stdH w (ψ₁ (a' j)) (ψ₁ (a' i)) := by
          rw [hva, hva]
          unfold stdH
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = e ((B₁.prod B₂).herm x (show (B₁.prod B₂).A from (a' j, 0)) (show (B₁.prod B₂).A from (a' i, 0))) :=
          hh _ _
      _ = e (B₁.herm x.1 (a' j) (a' i)) := congrArg e (prod_herm_fst B₁ B₂ x _ _)
  have hdetE : (Matrix.of fun i j => e (B₁.herm x.1 (a' i) (a' j))).det =
      e (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det := by
    exact (RingHom.map_det (e : K.E →+* w.adicCompletion E) _).symm
  rw [hK, Matrix.det_transpose, hdetE, ← hval, hdetG]
  exact neg_one_zpow_val_norm_mul K _ _ hdetM.ne_zero

end GlobalTheory.KapLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDetStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_kernelSign_eq_eta_gramDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → ∀ (x : (B₁.prod B₂).A) (γ : GLw n w), IsModel w e (B₁.prod B₂) ((u₁, u₂) : B₁.A × B₂.A) x γ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet x.1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapLat.kapSign_eq_eta_gramDet | exact GlobalTheory.KapLat.kapSign_eq_eta_gramDet | (intros; apply GlobalTheory.KapLat.kapSign_eq_eta_gramDet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormCutoffLogWeightLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormCutoffLogWeightLowerBound
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeightLevi

open Complex ComplexConjugate Filter

theorem deriv_zero_of_eqOn {χ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {c : ℝ}
    (h : ∀ s ∈ U, χ s = c) : ∀ s ∈ U, deriv χ s = 0 ∧ deriv (deriv χ) s = 0 := by
  have h1 : ∀ s ∈ U, deriv χ s = 0 := fun s hs => by
    have e : χ =ᶠ[𝓝 s] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hs) h
    rw [e.deriv_eq]; simp
  intro s hs
  refine ⟨h1 s hs, ?_⟩
  have e : deriv χ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := Filter.eventually_of_mem (hU.mem_nhds hs) h1
  rw [e.deriv_eq]; simp

theorem hasDerivAt_logShift {δ s : ℝ} (hs : 0 < s + δ) :
    HasDerivAt (fun s => Real.log ((s + δ) / 2)) (s + δ)⁻¹ s := by
  have h1 : HasDerivAt (fun s : ℝ => (s + δ) / 2) (1 / 2) s :=
    ((hasDerivAt_id' s).add_const δ).div_const 2
  convert h1.log (by positivity) using 1
  field_simp

theorem hasDerivAt_cutLog {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {δ s : ℝ} (hs : 0 < s + δ) :
    HasDerivAt (fun s => χ s * Real.log ((s + δ) / 2))
      (deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹) s := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  exact (hd s).hasDerivAt.mul (hasDerivAt_logShift hs)

theorem derivs_cutLog {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {δ t : ℝ} (ht : 0 < t + δ) :
    deriv (fun s => χ s * Real.log ((s + δ) / 2)) t =
        deriv χ t * Real.log ((t + δ) / 2) + χ t * (t + δ)⁻¹ ∧
      deriv (deriv (fun s => χ s * Real.log ((s + δ) / 2))) t =
        deriv (deriv χ) t * Real.log ((t + δ) / 2) + 2 * deriv χ t * (t + δ)⁻¹ -
          χ t * ((t + δ)⁻¹) ^ 2 := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hd2 : Differentiable ℝ (deriv χ) :=
    (contDiff_infty_iff_deriv.1 hχ).2.differentiable (by simp)
  have hU : Set.Ioi (-δ) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have e : deriv (fun s => χ s * Real.log ((s + δ) / 2)) =ᶠ[𝓝 t]
      fun s => deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹ :=
    Filter.eventually_of_mem hU fun s hs =>
      (hasDerivAt_cutLog hχ (by simp only [Set.mem_Ioi] at hs; linarith)).deriv
  refine ⟨(hasDerivAt_cutLog hχ ht).deriv, ?_⟩
  rw [e.deriv_eq]
  have hinv : HasDerivAt (fun s => (s + δ)⁻¹) (-1 / (t + δ) ^ 2) t :=
    ((hasDerivAt_id' t).add_const δ).inv ht.ne'
  have h : HasDerivAt (fun s => deriv χ s * Real.log ((s + δ) / 2) + χ s * (s + δ)⁻¹) _ t :=
    ((hd2 t).hasDerivAt.mul (hasDerivAt_logShift ht)).add ((hd t).hasDerivAt.mul hinv)
  rw [h.deriv]
  field_simp
  ring

theorem cutLog_bounds (χ : ℝ → ℝ) (A : ℝ) (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (h1 : ∀ t, t ≤ 1 / 4 → χ t = 1) (h0 : ∀ t, 1 ≤ t → χ t = 0) (hA1 : ∀ t, |deriv χ t| ≤ A)
    (hA2 : ∀ t, |deriv (deriv χ) t| ≤ A) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    -(13 * A + 20) ≤ deriv (fun s => χ s * Real.log ((s + δ) / 2)) t ∧
      -(13 * A + 20) ≤ deriv (fun s => χ s * Real.log ((s + δ) / 2)) t +
        t * deriv (deriv (fun s => χ s * Real.log ((s + δ) / 2))) t := by
  have htd : 0 < t + δ := by linarith
  obtain ⟨e1, e2⟩ := derivs_cutLog hχ htd
  rw [e1, e2]
  have hA : 0 ≤ A := (abs_nonneg _).trans (hA1 0)
  set L := Real.log ((t + δ) / 2)
  set u := (t + δ)⁻¹ with hu_def
  have hu : 0 < u := inv_pos.2 htd
  have htu : t * u ≤ 1 := by
    rw [hu_def, ← div_eq_mul_inv, div_le_one htd]; linarith
  have htu0 : 0 ≤ t * u := mul_nonneg ht hu.le
  have hc0 := h01 t
  have hpos : 0 ≤ χ t * u * (1 - t * u) :=
    mul_nonneg (mul_nonneg hc0.1 hu.le) (by linarith)
  have hexp : deriv χ t * L + χ t * u + t * (deriv (deriv χ) t * L + 2 * deriv χ t * u - χ t * u ^ 2) =
      deriv χ t * L + t * (deriv (deriv χ) t * L) + 2 * (deriv χ t * (t * u)) +
        χ t * u * (1 - t * u) := by ring
  rw [hexp]
  by_cases hc : t < 1 / 4 ∨ 1 < t
  · have hz : deriv χ t = 0 ∧ deriv (deriv χ) t = 0 := by
      rcases hc with hc | hc
      · exact deriv_zero_of_eqOn isOpen_Iio (fun s hs => h1 s (le_of_lt hs)) t hc
      · exact deriv_zero_of_eqOn isOpen_Ioi (fun s hs => h0 s (le_of_lt hs)) t hc
    rw [hz.1, hz.2]
    have : 0 ≤ χ t * u := mul_nonneg hc0.1 hu.le
    constructor <;> nlinarith
  · push_neg at hc
    have hx1 : (t + δ) / 2 ≤ 1 := by linarith
    have hx0 : 1 / 8 ≤ (t + δ) / 2 := by linarith
    have hL0 : L ≤ 0 := Real.log_nonpos (by linarith) hx1
    have hl8 : Real.log (1 / 8) = -(3 * Real.log 2) := by
      rw [show (1 : ℝ) / 8 = ((2 : ℝ) ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
    have hL1 : -3 ≤ L := by
      have := Real.log_le_log (by norm_num) hx0
      have := Real.log_two_lt_d9
      linarith
    have hLabs : |L| ≤ 3 := abs_le.2 ⟨hL1, by linarith⟩
    have b1 : -(3 * A) ≤ deriv χ t * L := by
      have : |deriv χ t * L| ≤ A * 3 := by
        rw [abs_mul]; exact mul_le_mul (hA1 t) hLabs (abs_nonneg _) hA
      linarith [neg_abs_le (deriv χ t * L)]
    have b2 : -(3 * A) ≤ t * (deriv (deriv χ) t * L) := by
      have : |t * (deriv (deriv χ) t * L)| ≤ 1 * (A * 3) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht]
        exact mul_le_mul (by linarith) (mul_le_mul (hA2 t) hLabs (abs_nonneg _) hA)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
      linarith [neg_abs_le (t * (deriv (deriv χ) t * L))]
    have b3 : -A ≤ deriv χ t * (t * u) := by
      have : |deriv χ t * (t * u)| ≤ A * 1 := by
        rw [abs_mul, abs_of_nonneg htu0]
        exact mul_le_mul (hA1 t) htu htu0 hA
      linarith [neg_abs_le (deriv χ t * (t * u))]
    have : 0 ≤ χ t * u := mul_nonneg hc0.1 hu.le
    constructor <;> nlinarith

theorem normSq_sum_conj_mul_le {n : ℕ} (a b : Fin n → ℂ) :
    Complex.normSq (∑ m, conj (a m) * b m) ≤
      (∑ m, Complex.normSq (a m)) * ∑ m, Complex.normSq (b m) := by
  have h1 : ‖∑ m, conj (a m) * b m‖ ≤ ∑ m, ‖a m‖ * ‖b m‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ => by
      rw [norm_mul, Complex.norm_conj]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun m => ‖a m‖) (fun m => ‖b m‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ m, conj (a m) * b m‖ ^ 2 ≤ (∑ m, ‖a m‖ * ‖b m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem levi_cutLog_lower : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) →
    (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) →
    (∀ t, |deriv (deriv χ) t| ≤ A) → ∀ (n : ℕ) (ρ δ : ℝ), 0 < ρ → 0 < δ → δ ≤ 1 →
    ∀ (z : V n) (ξ : Fin n → ℂ), -((13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) ≤
      (leviV n (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ))
        z ξ).re := by
  intro χ A hχ h01 h1 h0 hA1 hA2 n ρ δ hρ hδ hδ1 z ξ
  set k : ℝ → ℝ := fun s => χ s * Real.log ((s + δ) / 2) with hk
  let L : Fin n → V n →L[ℂ] ℂ := fun j => ((ρ : ℂ)⁻¹) • EuclideanSpace.proj j
  have hLapp : ∀ j y, L j y = (ρ : ℂ)⁻¹ * y j := fun j y => by simp [L]
  set v : V n → ℝ := fun y => ∑ j, Complex.normSq (L j y) with hvdef
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hv : ∀ y : V n, ‖y‖ ^ 2 / ρ ^ 2 = v y := by
    intro y
    simp only [hvdef, hLapp, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal,
      EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    field_simp
  have hfun : (fun w : V n => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ))
      = fun w => ((k (v w) : ℝ) : ℂ) := by
    funext w; rw [hv w]
  rw [hfun]
  have hLc : ∀ j, ContDiffAt ℂ 2 (fun y => L j y) z := fun j => (L j).contDiff.contDiffAt
  have hu : ∀ j, ContDiffAt ℝ 2 (fun y => Complex.normSq (L j y)) z := fun j =>
    H.contDiffAt_normSq_comp (hLc j)
  have hvC : ContDiffAt ℝ 2 v z := ContDiffAt.sum fun j _ => hu j
  have ht0 : 0 ≤ v z := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hkC : ContDiffAt ℝ 2 k (v z) := by
    have hχ2 : ContDiffAt ℝ 2 χ (v z) := hχ.contDiffAt.of_le (by norm_cast)
    exact hχ2.mul (((contDiffAt_id.add contDiffAt_const).div_const (2 : ℝ)).log
      (by simp only [id]; positivity))
  rw [H.leviChain n k v z ξ hvC hkC]
  have hwdL : ∀ j m, wd n m (fun y => L j y) z = (ρ : ℂ)⁻¹ * (if j = m then 1 else 0) := by
    intro j m
    rw [wd_of_differentiableAt (L j).differentiableAt, (L j).fderiv, hLapp]
    simp [bas, PiLp.single_apply]
  have hLevi : leviV n (fun y => ((v y : ℝ) : ℂ)) z ξ =
      ((∑ j, Complex.normSq ((ρ : ℂ)⁻¹ * ξ j) : ℝ) : ℂ) := by
    rw [show (fun y => ((v y : ℝ) : ℂ)) = fun y => ((∑ j, Complex.normSq (L j y) : ℝ) : ℂ) from rfl,
      H.leviV_ofReal_sum hu, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.leviV_normSq_comp (hLc j)]
    simp [hwdL]
  have hwd : ∀ m, wd n m (fun y => ((v y : ℝ) : ℂ)) z = (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) := by
    intro m
    rw [show (fun y => ((v y : ℝ) : ℂ)) = fun y => ((∑ j, Complex.normSq (L j y) : ℝ) : ℂ) from rfl,
      H.wd_ofReal_sum (fun j => (hu j).differentiableAt (by simp))]
    refine (Finset.sum_congr rfl fun j _ => by rw [H.wd_normSq_comp (hLc j), hwdL]).trans ?_
    simp [hLapp]
  rw [hLevi]
  simp only [hwd]
  set P := ∑ j, Complex.normSq ((ρ : ℂ)⁻¹ * ξ j) with hP
  set N := Complex.normSq (∑ m, (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) * ξ m) with hN
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hNt : N ≤ v z * P := by
    have e : ∑ m, (ρ : ℂ)⁻¹ * conj ((ρ : ℂ)⁻¹ * z m) * ξ m =
        ∑ m, conj ((ρ : ℂ)⁻¹ * z m) * ((ρ : ℂ)⁻¹ * ξ m) :=
      Finset.sum_congr rfl fun m _ => by ring
    have ev : v z = ∑ m, Complex.normSq ((ρ : ℂ)⁻¹ * z m) :=
      Finset.sum_congr rfl fun m _ => by rw [hLapp]
    rw [hN, e, ev, hP]
    exact normSq_sum_conj_mul_le _ _
  have hPe : (13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 = (13 * A + 20) * P := by
    rw [hP, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    field_simp
  rw [hPe]
  obtain ⟨b1, b2⟩ := cutLog_bounds χ A hχ h01 h1 h0 hA1 hA2 hδ hδ1 ht0
  by_cases hs : 0 ≤ deriv (deriv k) (v z)
  · have := mul_le_mul_of_nonneg_right b1 hP0
    have := mul_nonneg hs hN0
    nlinarith
  · push_neg at hs
    have h3 : deriv (deriv k) (v z) * (v z * P) ≤ deriv (deriv k) (v z) * N :=
      mul_le_mul_of_nonpos_left hNt hs.le
    have := mul_le_mul_of_nonneg_right b2 hP0
    nlinarith

end GlobalTheory.PeakWeightLevi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormCutoffLogWeightLowerBoundStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviForm_cutoffLogWeight_lower_bound : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → (∀ t, |deriv (deriv χ) t| ≤ A) → ∀ (n : ℕ) (ρ δ : ℝ), 0 < ρ → 0 < δ → δ ≤ 1 → ∀ (z : V n) (ξ : Fin n → ℂ), -((13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) ≤ (leviV n (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ)) z ξ).re := by
  first | exact @GlobalTheory.PeakWeightLevi.levi_cutLog_lower | exact GlobalTheory.PeakWeightLevi.levi_cutLog_lower | (intros; apply GlobalTheory.PeakWeightLevi.levi_cutLog_lower <;> assumption)
end
end

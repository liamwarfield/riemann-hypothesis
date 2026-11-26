module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory
namespace DSInequiv

open PI.DSInfCharCap

lemma eq_of_capP {n : ℕ} (mu mu' : Fin n → ℝ) (h : StrictAnti mu) (h' : StrictAnti mu')
    (e : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (mu s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (mu' s : ℂ)) Y) :
    mu = mu' := by
  have key : ∀ (a b : Fin n → ℝ),
      (∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (b s : ℂ)) Y) →
      Set.range a ⊆ Set.range b := by
    rintro a b e _ ⟨s, rfl⟩
    have h0 : Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) (-(a s : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [e] at h0
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h0
    refine ⟨t, ?_⟩
    have : (b t : ℂ) = (a s : ℂ) := by linear_combination ht
    exact_mod_cast this
  have hr : Set.range mu = Set.range mu' :=
    Set.Subset.antisymm (key _ _ e) (key _ _ fun Y => (e Y).symm)
  have h1 : StrictMono (fun s => -mu s) := fun a b hab => neg_lt_neg (h hab)
  have h2 : StrictMono (fun s => -mu' s) := fun a b hab => neg_lt_neg (h' hab)
  have hr' : Set.range (fun s => -mu s) = Set.range (fun s => -mu' s) := by
    have := congrArg (fun S => Neg.neg '' S) hr
    simp only [← Set.range_comp] at this
    exact this
  have := (h1.range_inj h2).mp hr'
  funext s
  exact neg_injective (congrFun this s)

section
variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def toReal (V : H ≃L[ℂ] H') : H ≃L[ℝ] H' :=
  { V.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := V.continuous
    continuous_invFun := V.symm.continuous }

lemma dsig_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.inG ε X) (v : H) :
    V (PI.PhMeasCore.dsig τ X v) = PI.PhMeasCore.dsig τ' X (V v) := by
  unfold PI.PhMeasCore.dsig
  have e : (fun t : ℝ => τ' (NormedSpace.exp ((t : ℂ) • X)) (V v)) =
      (toReal V) ∘ (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    exact (hV _ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t) v).symm
  rw [e]
  unfold deriv
  rw [ContinuousLinearEquiv.comp_fderiv]
  rfl

lemma dsigC_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) : V (dsigC ε τ Y v) = dsigC ε τ' Y (V v) := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hH := Formalism.REAL.Jm_conjTranspose ε
  have hJ' := Formalism.REAL.f1alg_JJ_left ε
  unfold dsigC
  rw [map_add (f := _), map_smul, dsig_equiv V hV, dsig_equiv V hV]
  · rw [Formalism.REAL.f1alg_inG_iff]
    have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp [Complex.conj_I]
    simp only [thetaJ, conjTranspose_smul, hs, conjTranspose_sub, conjTranspose_neg, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    module
  · rw [Formalism.REAL.f1alg_inG_iff]
    have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
    simp only [thetaJ, conjTranspose_smul, hs, conjTranspose_add, conjTranspose_neg, conjTranspose_mul, hH,
      conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, hJ', Matrix.mul_one]
    module

lemma dsigCW_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (w : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) : V (dsigCW ε τ w v) = dsigCW ε τ' w (V v) := by
  induction w with
  | nil => rfl
  | cons Y w ih => simp only [dsigCW]; rw [dsigC_equiv V hV, ih]

lemma actU_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : H) : V (actU ε τ p v) = actU ε τ' p (V v) := by
  unfold actU Finsupp.sum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, dsigCW_equiv V hV]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma smooth_equiv (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) :
    V v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, hE⟩ := hv g₀ hg₀
  refine ⟨U, fun g => V (F g), hU, hm, ?_, fun g hg hg' => ?_⟩
  · exact ((toReal V).contDiff).comp_contDiffOn hF
  · exact (hV g hg' v).symm.trans (congrArg V (hE g hg hg'))

lemma smooth_conj {A B P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hA : Pᴴ * A * P = B) {v : H}
    (hv : PI.UpqRep.SmoothOnH B (fun g => τ g v)) :
    v ∈ PI.PhMeasCore.smoothVecs A (fun g => τ (P⁻¹ * g * P)) := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hmem : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * A * g = A → PI.UpqRep.inUH B (P⁻¹ * g * P) := by
    intro g hg
    unfold PI.UpqRep.inUH
    have h1 : P * (P⁻¹ * g * P) = g * P := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    calc (P⁻¹ * g * P)ᴴ * B * (P⁻¹ * g * P)
        = (P * (P⁻¹ * g * P))ᴴ * A * (P * (P⁻¹ * g * P)) := by
          rw [← hA, conjTranspose_mul P]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * (gᴴ * A * g) * P := by rw [h1, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = B := by rw [hg, hA]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => P⁻¹ * g * P
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by simp }
  let L' := LinearMap.toContinuousLinearMap L
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, hE⟩ := hv _ (hmem g₀ hg₀)
  refine ⟨L' ⁻¹' U, F ∘ L', hU.preimage L'.continuous, hm, hF.comp_continuousLinearMap L', fun g hg hg' => ?_⟩
  exact hE _ hg (hmem g hg')

lemma eq_of_equiv (hc : DSInfCharCap) {mu mu' : Fin n → ℝ} (hm : Formalism.QuantumDeterminants.IsHCParam mu)
    (hm' : Formalism.QuantumDeterminants.IsHCParam mu') (h : PI.UpqRep.IsDS ε mu τ) (h' : PI.UpqRep.IsDS ε mu' τ')
    (V : H ≃L[ℂ] H') (hV : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, V (τ g x) = τ' g (V x))
    {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) τ) (h0 : v ≠ 0) : mu = mu' := by
  refine eq_of_capP mu mu' hm.1 hm'.1 fun Y => ?_
  have e1 := hc n ε mu H τ hm h v hv Y
  have e2 := hc n ε mu' H' τ' hm' h' (V v) (smooth_equiv V hV hv) Y
  rw [← actU_equiv V hV, e1, map_smul] at e2
  exact smul_left_injective ℂ (by simpa using h0) e2

lemma inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ PI.UpqRep.UJset ε) (hb : b ∈ PI.UpqRep.UJset ε) :
    a * b ∈ PI.UpqRep.UJset ε := by
  show (a * b)ᴴ * PI.UpqRep.Jm ε * (a * b) = PI.UpqRep.Jm ε
  have ha' : aᴴ * PI.UpqRep.Jm ε * a = PI.UpqRep.Jm ε := ha
  have hb' : bᴴ * PI.UpqRep.Jm ε * b = PI.UpqRep.Jm ε := hb
  calc _ = bᴴ * (aᴴ * PI.UpqRep.Jm ε * a) * b := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

lemma cayley_quot {B P Q : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (hP : Pᴴ * PI.UpqRep.Jm ε * P = B)
    (hQ' : Qᴴ * PI.UpqRep.Jm ε * Q = B) : P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  show (P * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  calc _ = (Q⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * Q⁻¹ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Q * Q⁻¹)ᴴ * PI.UpqRep.Jm ε * (Q * Q⁻¹) := by
      rw [hP, ← hQ', conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

end

lemma exists_kfin {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (R : Rep k r)
    {P : Mx k r} (hP : PI.UpqRep.IsCayleyU k r ε P) (h : PI.UpqRep.IsDS ε mu (fun g => R.σ (P⁻¹ * g * P))) :
    ∃ v, R.KFin v ∧ v ≠ 0 := by
  obtain ⟨S, hfin, hst, -, ⟨v, hvS, hv0, -⟩, -⟩ := h.2.2.2.2.2.1
  refine ⟨v, ⟨S, hfin, hvS, ?_⟩, hv0⟩
  rintro g ⟨hg, hgu⟩ x hx
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : star P * P = 1 := Unitary.star_mul_self_of_mem hP.2
  have hPP' : P * star P = 1 := Unitary.mul_star_self_of_mem hP.2
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hPP
  have hgu' : g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hgu
  have hu : P * g * star P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hP.2 hgu') (Unitary.star_mem hP.2)
  have hJ : (P * g * star P)ᴴ * PI.UpqRep.Jm ε * (P * g * star P) = PI.UpqRep.Jm ε := by
    have hg' : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hg
    have hc := hP.1.2
    rw [Matrix.star_eq_conjTranspose] at hPP' ⊢
    calc _ = P * (gᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * g) * Pᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (P * Pᴴ) * PI.UpqRep.Jm ε * (P * Pᴴ) := by
          rw [hc, hg', ← hc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPP']; simp
  have hK : P * g * star P ∈ PI.UpqRep.Kset ε := by
    refine ⟨hu, ?_⟩
    have h1 : (P * g * star P) * (P * g * star P)ᴴ = 1 := Unitary.mul_star_self_of_mem hu
    generalize P * g * star P = m at hJ h1
    calc m * PI.UpqRep.Jm ε = m * (mᴴ * PI.UpqRep.Jm ε * m) := by rw [hJ]
      _ = (m * mᴴ) * PI.UpqRep.Jm ε * m := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.one_mul]
  have := hst _ hK x hx
  have e : P⁻¹ * (P * g * star P) * P = g := by
    rw [hinv]
    calc _ = (star P * P) * g * (star P * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hPP]; simp
  simpa only [e] using this

theorem param_eq_of_equiv : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r), R.IsDS ε mu → R'.IsDS ε mu' → ∀ U : R.H ≃ₗᵢ[ℂ] R'.H, (∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) → mu = mu' := by
  intro hy k r ε mu mu' R R' hR hR' U hU
  obtain ⟨hm, P, hP, h⟩ := hR
  obtain ⟨hm', Q, hQ, h'⟩ := hR'
  obtain ⟨v, hv, hv0⟩ := exists_kfin R hP h
  have hs := hy.1.2.2.1 k r ε mu R.H R.σ hm ⟨P, hP, h⟩ v hv
  have hs' := smooth_conj (A := Formalism.REAL.Jm ε) hP.1.1 hP.1.2 hs
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hdQ := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.1.1
  have p1 := Matrix.mul_nonsing_inv _ hdP
  have q1 := Matrix.mul_nonsing_inv _ hdQ
  have p2 := Matrix.nonsing_inv_mul _ hdP
  have q2 := Matrix.nonsing_inv_mul _ hdQ
  have p3 : ∀ B : Mx k r, P⁻¹ * (P * B) = B := fun B => by rw [← Matrix.mul_assoc, p2, Matrix.one_mul]
  have q3 : ∀ B : Mx k r, Q⁻¹ * (Q * B) = B := fun B => by rw [← Matrix.mul_assoc, q2, Matrix.one_mul]
  have p4 : ∀ B : Mx k r, P * (P⁻¹ * B) = B := fun B => by rw [← Matrix.mul_assoc, p1, Matrix.one_mul]
  have ha := cayley_quot hQ.1.1 hP.1.2 hQ.1.2
  have hb := cayley_quot hP.1.1 hQ.1.2 hP.1.2
  obtain ⟨⟨hone, hmul⟩, -⟩ := h'.2.2.1
  set τ' : Mx k r → (R'.H →L[ℂ] R'.H) := fun g => R'.σ (Q⁻¹ * g * Q) with hτ'
  have hmul' : ∀ a ∈ PI.UpqRep.UJset ε, ∀ b ∈ PI.UpqRep.UJset ε, ∀ x, τ' a (τ' b x) = τ' (a * b) x := by
    intro a ha b hb x
    rw [hmul a ha b hb]; rfl
  have hab : (P * Q⁻¹) * (Q * P⁻¹) = 1 := by simp only [Matrix.mul_assoc, q3, p1]
  have hba : (Q * P⁻¹) * (P * Q⁻¹) = 1 := by simp only [Matrix.mul_assoc, p3, q1]
  let A : R'.H ≃L[ℂ] R'.H := ContinuousLinearEquiv.equivOfInverse (τ' (P * Q⁻¹)) (τ' (Q * P⁻¹))
    (fun x => by rw [hmul' _ hb _ ha, hba, hone]; rfl) (fun x => by rw [hmul' _ ha _ hb, hab, hone]; rfl)
  refine eq_of_equiv hy.2.2.1 hm hm' h h' (U.toContinuousLinearEquiv.trans A) ?_ hs' hv0
  intro g hg x
  have hg' : g ∈ PI.UpqRep.UJset ε := hg
  have hG : P⁻¹ * g * P ∈ GG k r := by
    show (P⁻¹ * g * P)ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * g * P) = PI.UpqRep.Hpk k r
    have hgg : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have hc := hP.1.2
    calc _ = (P * (P⁻¹ * g * P))ᴴ * PI.UpqRep.Jm ε * (P * (P⁻¹ * g * P)) := by
          rw [← hc, conjTranspose_mul P]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * (gᴴ * PI.UpqRep.Jm ε * g) * P := by
          simp only [Matrix.mul_assoc, p4, conjTranspose_mul g]
      _ = _ := by rw [hgg, hc]
  show τ' (P * Q⁻¹) (U (R.σ (P⁻¹ * g * P) x)) = τ' g (τ' (P * Q⁻¹) (U x))
  have e : R'.σ (P⁻¹ * g * P) = τ' (Q * P⁻¹ * g * (P * Q⁻¹)) := by
    simp only [hτ', Matrix.mul_assoc, q3, q2, Matrix.mul_one]
  rw [hU _ hG, e, hmul' _ ha _ (inUJ_mul (inUJ_mul hb hg') ha), hmul' _ hg' _ ha]
  congr 2
  simp only [Matrix.mul_assoc, q3, p4]

end DSInequiv
end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorBlockLinearMapIntertwine
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorBlockLinearMapIntertwine
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_ofFn_prod_apply_of_intertwine {M Wp : Type} [AddCommGroup M] [Module ℂ M]
    (l : M → Wp) :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ M) (g : Fin t → Wp → Wp),
      (∀ k v, l (f k v) = g k (l v)) → ∀ v,
      l ((List.ofFn f).prod v) = List.foldr (fun T h => T h) (l v) (List.ofFn g) := by
  intro t
  induction t with
  | zero => intro f g _ v; simp
  | succ t ih =>
    intro f g h v
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.foldr_cons, Module.End.mul_apply, h,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun k v => h k.succ v) v]

theorem qminor_block_intertwine : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (w : Fin m → Fin n) (Pop : Fin m → Fin m → Wp → Wp), Function.Injective w → (∀ i j v, l (E (w i) (w j) v) = Pop i j (l v)) → ∀ u v, l (Formalism.REAL.qminor E w w u v) = Formalism.FourierDecayAlt.Q.qmF Pop id id u (l v) := by
  intro M Wp _ _ _ _ n m E l w Pop hw h u v
  unfold Formalism.REAL.qminor Formalism.FourierDecayAlt.Q.qmF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key := map_ofFn_prod_apply_of_intertwine (l : M → Wp) m
    (fun k => Formalism.REAL.Tm E (u - ((k : ℕ) : ℂ)) (w (σ k)) (w k))
    (fun k y => (if id (σ k) = id k then (u - ((k : ℕ) : ℂ)) • y else 0) + Pop (id (σ k)) (id k) y)
    (fun k x => by
      unfold Formalism.REAL.Tm
      by_cases hk : σ k = k
      · simp [hk, h, sub_smul, Nat.cast_smul_eq_nsmul]
      · have : w (σ k) ≠ w k := fun e => hk (hw e)
        simp [hk, this, h]) v
  rw [← key, Module.End.mul_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorBlockLinearMapIntertwineStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantumMinor_block_linearMap_intertwine : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (w : Fin m → Fin n) (Pop : Fin m → Fin m → Wp → Wp), Function.Injective w → (∀ i j v, l (E (w i) (w j) v) = Pop i j (l v)) → ∀ u v, l (Formalism.REAL.qminor E w w u v) = Formalism.FourierDecayAlt.Q.qmF Pop id id u (l v) := by
  first | exact @GlobalTheory.qminor_block_intertwine | exact GlobalTheory.qminor_block_intertwine | (intros; apply GlobalTheory.qminor_block_intertwine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompoundMatrixCauchyBinetProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompoundMatrixCauchyBinetProperties
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem compound_mul {n : ℕ} (l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ) :
    BranchingSupport.cmp l (g * h) = BranchingSupport.cmp l g * BranchingSupport.cmp l h := by
  ext I J
  have e : (g * h).submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2)
      = g.submatrix (I.1.orderEmbOfFin I.2) id * h.submatrix id (J.1.orderEmbOfFin J.2) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [Matrix.mul_apply]
  unfold BranchingSupport.cmp
  rw [e, Formalism.HermitianLatticeCounting.P.ge_cauchyBinet]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [mul_comm]
  rfl

theorem compound_conjTranspose {n : ℕ} (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) :
    BranchingSupport.cmp l gᴴ = (BranchingSupport.cmp l g)ᴴ := by
  ext I J
  rw [Matrix.conjTranspose_apply]
  unfold BranchingSupport.cmp
  rw [← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]

theorem compound_one (n l : ℕ) : BranchingSupport.cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext I J
  unfold BranchingSupport.cmp
  by_cases hIJ : I = J
  · subst hIJ
    rw [Matrix.submatrix_one _ (I.1.orderEmbOfFin I.2).injective, Matrix.det_one, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hIJ]
    have hne : ¬ I.1 ⊆ J.1 := fun hs =>
      hIJ (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [I.2, J.2])))
    obtain ⟨x, hxI, hxJ⟩ := Finset.not_subset.mp hne
    have hx : x ∈ Set.range (I.1.orderEmbOfFin I.2) := by
      rw [Finset.range_orderEmbOfFin]; exact hxI
    obtain ⟨a, ha⟩ := hx
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply_ne]
    intro hab
    apply hxJ
    rw [← ha, hab]
    exact Finset.orderEmbOfFin_mem _ _ _

theorem compound_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) := by
  ext I
  have e : (Matrix.of fun a b : Fin l => (g *ᵥ f b) (I.1.orderEmbOfFin I.2 a))
      = g.submatrix (I.1.orderEmbOfFin I.2) id * (Matrix.of fun (c : Fin n) (b : Fin l) => f b c) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold BranchingSupport.wedge
  rw [e, Formalism.HermitianLatticeCounting.P.ge_cauchyBinet]
  unfold Matrix.mulVec dotProduct BranchingSupport.cmp
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [mul_comm]
  rfl

theorem compound_properties : ∀ (n l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ),
    BranchingSupport.cmp l (g * h) = BranchingSupport.cmp l g * BranchingSupport.cmp l h ∧ BranchingSupport.cmp l gᴴ = (BranchingSupport.cmp l g)ᴴ ∧
      BranchingSupport.cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 ∧
      ∀ f : Fin l → Fin n → ℂ, BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) :=
  fun n l g h => ⟨compound_mul l g h, compound_conjTranspose l g, compound_one n l, compound_mulVec_wedge g⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompoundMatrixCauchyBinetPropertiesStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compoundMatrix_cauchyBinet_properties : ∀ (n l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ), cmp l (g * h) = cmp l g * cmp l h ∧ cmp l gᴴ = (cmp l g)ᴴ ∧ cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 ∧ ∀ f : Fin l → Fin n → ℂ, cmp l g *ᵥ wedge f = wedge (fun b => g *ᵥ f b) := by
  first | exact @GlobalTheory.compound_properties | exact GlobalTheory.compound_properties | (intros; apply GlobalTheory.compound_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpMemUnipotentAndHasDerivAtCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpMemUnipotentAndHasDerivAtCharacter
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Nat

noncomputable section

namespace GlobalTheory.UnipotentExp


set_option backward.isDefEq.respectTransparency false in
theorem exp_apply_of_pattern {n : ℕ} (P : Fin n → Fin n → Prop)
    (htr : ∀ i m j, P i m → P m j → P i j) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ i j, ¬ P i j → Y i j = 0) (i j : Fin n) (hij : ¬ P i j) :
    NormedSpace.exp Y i j = if i = j then 1 else 0 := by
  have hp : ∀ m : ℕ, ∀ i j, ¬ P i j → (Y ^ (m + 1)) i j = 0 := by
    intro m
    induction m with
    | zero => simpa using hY
    | succ m ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases h1 : P i l
      · rw [hY l j (fun h2 => h (htr _ _ _ h1 h2)), mul_zero]
      · rw [ih i l h1, zero_mul]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m)) (NormedSpace.exp Y) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h2 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) (NormedSpace.exp Y i j) :=
    Pi.hasSum.1 (Pi.hasSum.1 h1 i) j
  have h3 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) (((0 ! : ℂ)⁻¹ • Y ^ 0) i j) := by
    refine hasSum_single (f := fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) 0 ?_
    intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [Matrix.smul_apply, hp m i j hij, smul_zero]
  rw [h2.unique h3]
  simp [Matrix.one_apply]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp_apply {k r : ℕ} (X : Mx k r) (i j : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero (1 : Mx k r) X
  simp only [Matrix.one_mul] at hγ
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hγ i) j

theorem hasDerivAt_ell {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) :
    HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.ell k r z (NormedSpace.exp ((t : ℂ) • X)))
      (Formalism.QuantumDeterminants.ell k r z X) 0 := by
  unfold Formalism.QuantumDeterminants.ell
  refine HasDerivAt.fun_sum fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [dif_pos h]
    exact hasDerivAt_exp_apply X _ _
  · simp only [dif_neg h, Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_exp_apply X _ _).mul_const _

theorem ell_one {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) :
    Formalism.QuantumDeterminants.ell k r z 1 = 0 := by
  unfold Formalism.QuantumDeterminants.ell
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · refine Matrix.one_apply_ne ?_
    intro e
    have := congrArg Fin.val e
    simp [Formalism.QuantumDeterminants.eI] at this
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl a.isLt)

theorem exp_mem_and_deriv : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r), Formalism.QuantumDeterminants.inWb k r z → PI.UpqRep.InLieHpk k r X → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → X i j = 0) → (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.Nset k r) ∧ HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X))) (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) 0 := by
  intro k r z X hz hX hP
  refine ⟨fun t => ?_, ?_⟩
  · have key := exp_apply_of_pattern
      (fun i j : Fin (2 * r + k + 1) => i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k))
      (fun i m j h1 h2 => by
        simp only [Fin.lt_def] at h1 h2 ⊢
        omega)
      ((t : ℂ) • X) (fun i j h => by rw [Matrix.smul_apply, hP i j h, smul_zero])
    refine ⟨CCRuleCW.exp_mem_UH _ _ (CCRuleCW.lie_smul _ X hX t), fun a i h => key _ _ ?_,
      fun i j h1 h2 h3 => key _ _ ?_⟩
    · simp only [Fin.lt_def, Formalism.QuantumDeterminants.eI]
      omega
    · tauto
  · have h1 := (hasDerivAt_ell z X).const_mul Formalism.QuantumDeterminants.cStd
    have h2 : HasDerivAt (fun t : ℝ => (Formalism.QuantumDeterminants.cStd *
        Formalism.QuantumDeterminants.ell k r z (NormedSpace.exp ((t : ℂ) • X))).re)
        (Formalism.QuantumDeterminants.cStd * Formalism.QuantumDeterminants.ell k r z X).re 0 :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    have h3 := (h2.ofReal_comp.const_mul Complex.I).cexp
    unfold Formalism.QuantumDeterminants.psi
    convert h3 using 1
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, ell_one hz, mul_zero,
      Complex.zero_re, Complex.exp_zero, one_mul]
    apply Complex.ext <;> simp [Formalism.QuantumDeterminants.cStd]
    ring

end GlobalTheory.UnipotentExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpMemUnipotentAndHasDerivAtCharacterStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_mem_unipotent_and_hasDerivAt_character : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r), Formalism.QuantumDeterminants.inWb k r z → PI.UpqRep.InLieHpk k r X → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → X i j = 0) → (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.Nset k r) ∧ HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X))) (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) 0 := by
  first | exact @GlobalTheory.UnipotentExp.exp_mem_and_deriv | exact GlobalTheory.UnipotentExp.exp_mem_and_deriv | (intros; apply GlobalTheory.UnipotentExp.exp_mem_and_deriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SectionEqZeroOfForallGeometricPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlatPoints

theorem isPullback_whiskerRight_left {S : Scheme.{0}} {T H : Over S} (q : T ⟶ H) (Y : Over S) :
    IsPullback (pullback.fst T.hom Y.hom) (q ▷ Y).left q.left (pullback.fst H.hom Y.hom) := by
  refine (IsPullback.of_right (h₁₁ := (q ▷ Y).left) (v₁₁ := pullback.fst T.hom Y.hom)
    (h₂₁ := q.left) (v₁₂ := pullback.fst H.hom Y.hom) ?_ (Over.whiskerRight_left_fst q)
    (IsPullback.of_hasPullback H.hom Y.hom).flip).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback T.hom Y.hom).flip

theorem section_eq_zero_of_cover {X : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}}
    (u : ∀ i, Z i ⟶ X) [∀ i, IsOpenImmersion (u i)] (hu : ∀ x : X, ∃ i z, u i z = x)
    (W : X.Opens) (f : Γ(X, W)) (h : ∀ i, ((u i).app W).hom f = 0) : f = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf W f 0 fun x hx => ?_
  obtain ⟨i, z, rfl⟩ := hu x
  have hinj : Function.Injective ((u i).stalkMap z).hom :=
    (asIso ((u i).stalkMap z)).commRingCatIsoToRingEquiv.injective
  change (X.presheaf.germ W _ hx).hom f = (X.presheaf.germ W _ hx).hom 0
  apply hinj
  rw [Scheme.Hom.germ_stalkMap_apply, h i]
  simp

theorem eq_zero_of_forall_point (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F]
    (hinj : Function.Injective (algebraMap O F)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] [_root_.IsReduced (TensorProduct O F A)] (a : A)
    (ha : ∀ φ : A →ₐ[O] F, φ a = 0) : a = 0 := by
  have := tensor_eq_zero_of_forall_geometric_point O F hinj A O (a ⊗ₜ 1) (fun φ => by simp [ha φ])
  simpa using congrArg (TensorProduct.rid O A) this

theorem finite_algHom (O F : Type) [CommRing O] [Field F] [Algebra O F] (A : Type) [CommRing A]
    [Algebra O A] [Module.Finite O A] : Finite (A →ₐ[O] F) := by
  have : Finite (TensorProduct O F A →ₐ[F] F) := inferInstance
  exact Finite.of_equiv _ (Algebra.TensorProduct.liftEquivRight O F A F).symm

theorem affine_case (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F]
    (hinj : Function.Injective (algebraMap O F)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] [_root_.IsReduced (TensorProduct O F A)]
    (H Y : Over (Spec (CommRingCat.of O))) (e : specO O A ≅ H) [Flat Y.hom]
    (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W))
    (h : ∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) : f = 0 := by
  have := finite_algHom O F A
  let Φ : A →ₐ[O] ((A →ₐ[O] F) → F) := Pi.algHom O (fun _ => F) (fun φ => φ)
  have hΦ : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact eq_zero_of_forall_point O F hinj A a fun φ => congrFun ha φ
  let q : specO O ((A →ₐ[O] F) → F) ⟶ H := ptMap Φ ≫ e.hom
  have h1 : IsSchemeTheoreticallyDominant (ptMap Φ).left :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hΦ
  have h2 : QuasiCompact (ptMap Φ).left :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom Φ.toRingHom)))
  have h0 : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h3 : IsSchemeTheoreticallyDominant q.left := by
    change IsSchemeTheoreticallyDominant ((ptMap Φ).left ≫ e.hom.left)
    infer_instance
  have h4 : QuasiCompact q.left := by
    change QuasiCompact ((ptMap Φ).left ≫ e.hom.left)
    infer_instance
  have hp := isPullback_whiskerRight_left q Y
  have h5 : IsSchemeTheoreticallyDominant (q ▷ Y).left := .of_isPullback hp
  have h6 : QuasiCompact (q ▷ Y).left := MorphismProperty.of_isPullback hp h4
  apply (q ▷ Y).left.app_injective W
  rw [map_zero]
  let u : (A →ₐ[O] F) → (specO O F ⟶ specO O ((A →ₐ[O] F) → F)) :=
    fun φ => ptMap (Pi.evalAlgHom O (fun _ => F) φ)
  have hu : ∀ φ, IsOpenImmersion (u φ).left := fun φ =>
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : A →ₐ[O] F => CommRingCat.of F) φ))))
  have hu' : ∀ φ, IsOpenImmersion (u φ ▷ Y).left := fun φ =>
    MorphismProperty.of_isPullback (isPullback_whiskerRight_left (u φ) Y) (hu φ)
  refine section_eq_zero_of_cover (fun φ => (u φ ▷ Y).left) (fun x => ?_) _ _ (fun φ => ?_)
  · obtain ⟨φ, p, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
      (R := fun _ : A →ₐ[O] F => F) (pullback.fst (specO O ((A →ₐ[O] F) → F)).hom Y.hom x)
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_whiskerRight_left (u φ) Y) p x hp
    exact ⟨φ, z, hz⟩
  · have := h (u φ ≫ q)
    rw [MonoidalCategory.comp_whiskerRight] at this
    exact this

end GlobalTheory.FlatPoints

namespace GlobalTheory

theorem section_eq_zero_of_forall_geometric_point :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (H Y : Over (Spec (CommRingCat.of O))), IsFinite H.hom → Flat H.hom → IsReduced (specO O F ⊗ H).left → Flat Y.hom → ∀ (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W)), (∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) → f = 0 := by
  intro O F _ _ _ _ hinj H Y hfin hflat hred hY W f h
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)
  letI : Algebra O Γ(H.left, ⊤) := ψ.hom.toAlgebra
  let e : specO O Γ(H.left, ⊤) ≅ H := Over.isoMk H.left.isoSpec.symm hψ.symm
  have h1 : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have h2 : Flat (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Module.Finite O Γ(H.left, ⊤) := (IsFinite.SpecMap_iff ψ).mp h1
  have : Module.Flat O Γ(H.left, ⊤) := (Flat.SpecMap_iff (f := ψ)).mp h2
  have h0 : IsIso (specO O F ◁ e.hom).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O F ◁ e.hom)))
  have h3 : IsReduced (specO O F ⊗ specO O Γ(H.left, ⊤)).left :=
    isReduced_of_isOpenImmersion (specO O F ◁ e.hom).left
  have h4 : IsReduced (Spec (CommRingCat.of (TensorProduct O F Γ(H.left, ⊤)))) :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O F Γ(H.left, ⊤)).inv _ h3
  have : _root_.IsReduced (TensorProduct O F Γ(H.left, ⊤)) := (affine_isReduced_iff _).mp h4
  exact FlatPoints.affine_case O F hinj Γ(H.left, ⊤) H Y e W f h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionParameters
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensForm

theorem common_bound {ι α β : Type} [DecidableEq ι] (P : α → Prop) (S : Set β) (n : α → β → ℝ)
    (hn : ∀ a v, 0 ≤ n a v) (f : ι → β → ℝ)
    (h : ∀ c, ∃ (C : ℝ) (L : List α), (∀ a ∈ L, P a) ∧ ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum)
    (s : Finset ι) :
    ∃ (C : ℝ) (L : List α), 0 ≤ C ∧ (∀ a ∈ L, P a) ∧
      ∀ c ∈ s, ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum := by
  have hs : ∀ (L : List α) v, 0 ≤ (L.map fun a => n a v).sum := by
    intro L v
    apply List.sum_nonneg
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact hn a v
  induction s using Finset.induction_on with
  | empty => exact ⟨0, [], le_rfl, by simp, by simp⟩
  | insert c s _ ih =>
    obtain ⟨C, L, hC, hL, hb⟩ := ih
    obtain ⟨C', L', hL', hb'⟩ := h c
    refine ⟨C + |C'|, L ++ L', by positivity, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hL a ha
      · exact hL' a ha
    · intro d hd v hv
      rw [List.map_append, List.sum_append]
      have h1 := hs L v
      have h2 := hs L' v
      have h3 := abs_nonneg C'
      have h4 := le_abs_self C'
      rcases Finset.mem_insert.1 hd with rfl | hd
      · have := hb' v hv
        nlinarith [mul_nonneg hC h1, mul_nonneg hC h2, mul_nonneg h3 h1,
          mul_le_mul_of_nonneg_right h4 h2]
      · have := hb d hd v hv
        nlinarith [mul_nonneg hC h2, mul_nonneg h3 h1, mul_nonneg h3 h2]

variable {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hh_act (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (R : Rep k r) (g : Mx k r)
    (hρ : (ρ g)ᴴ * Γ * ρ g = Γ) (hσ : ∀ v, ‖R.σ g v‖ = ‖v‖) (x y : ι → R.H) :
    hh Γ R (act ρ R g x) (act ρ R g y) = hh Γ R x y := by
  have hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 hσ
  conv_rhs => rw [← hρ]
  simp only [hh, act, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hiso, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ b, ∑ a, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) :=
        Finset.sum_comm
    _ = ∑ j, ∑ b, ∑ a, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [RCLike.star_def]
        ring


omit [DecidableEq ι] in
theorem norm_hh_le (Γ : Matrix ι ι ℂ) (R : Rep k r) (x y : ι → R.H) (A B : ℝ)
    (hx : ∀ c, ‖x c‖ ≤ A) (hy : ∀ c, ‖y c‖ ≤ B) :
    ‖hh Γ R x y‖ ≤ (∑ i, ∑ j, ‖Γ i j‖) * (A * B) := by
  rw [hh, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (norm_nonneg _)
  rw [mul_comm A B]
  exact mul_le_mul (hy i) (hx j) (norm_nonneg _) ((norm_nonneg _).trans (hy i))

theorem family_bound (R R' : Rep k r) (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c)) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
      ∀ c, ∀ v ∈ R.sm, ‖T c v‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖).sum := by
  obtain ⟨C, L, -, hL, hb⟩ := common_bound (fun W : List (Mx k r) => ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) R.sm
    (fun W v => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖) (fun _ _ => norm_nonneg _)
    (fun c v => ‖T c v‖) (fun c => (hT c).cont [] (by simp)) Finset.univ
  exact ⟨C, L, hL, fun c => hb c (Finset.mem_univ c)⟩

theorem pulledBack_isInvForm : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∀ I J, IsInvForm (RI I) (RI J) (fun y y' => hh Γ R (fun c => io I c y) (fun c => io J c y')) := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR _ hF hT I J
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' y _
    simp only [hh, fun c => (hT.io_sm I c).add x hx x' hx', inner_add_right, mul_add, Finset.sum_add_distrib]
  · intro a x hx y _
    simp only [hh, fun c => (hT.io_sm I c).smul a x hx, inner_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · intro x _ y hy y' hy'
    simp only [hh, fun c => (hT.io_sm J c).add y hy y' hy', inner_add_left, mul_add, Finset.sum_add_distrib]
  · intro a x _ y hy
    simp only [hh, fun c => (hT.io_sm J c).smul a y hy, inner_smul_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [RCLike.star_def]; ring
  · intro g hg x hx y hy
    show hh Γ R (fun c => io I c ((RI I).σ g x)) (fun c => io J c ((RI J).σ g y)) = _
    rw [hT.io_eq I g hg x hx, hT.io_eq J g hg y hy]
    exact hh_act ρ Γ R g (hF.2.2.2.2.1 g hg) ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2 g hg) _ _
  · obtain ⟨C, Ws, hW, hb⟩ := family_bound (RI I) R (io I) (hT.io_sm I)
    obtain ⟨C', Ws', hW', hb'⟩ := family_bound (RI J) R (io J) (hT.io_sm J)
    refine ⟨(∑ i, ∑ j, ‖Γ i j‖) * C * C', Ws, Ws', ?_, ?_⟩
    · intro W hWm
      rcases List.mem_append.1 hWm with h | h
      · exact hW W h
      · exact hW' W h
    · intro x hx y hy
      refine (norm_hh_le Γ R _ _ _ _ (fun c => hb c x hx) (fun c => hb' c y hy)).trans (le_of_eq ?_)
      ring

end GlobalTheory.TensForm
end

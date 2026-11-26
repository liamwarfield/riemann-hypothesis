module

public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTie
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalCompactReductionStandardFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorIdentityIsotypicConjugateType

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditio
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationLabelsNormalisedOfRowsTypesLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabelsFixedByTupleOperatorOfTypeSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumSeriesIdempotentCoeffRightTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdFixedPlaceAverage
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdFixedPlaceAverage
open Finset

namespace GlobalTheory

theorem sum_prod_fixed_place_average {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] {V : Type}
    [AddCommGroup V] [Module ℂ V] (a : ∀ i, G i → ℂ) (f : (∀ i, G i) → V)
    (hf : ∀ i (γ : ∀ i, G i), γ i = 1 → ∑ β : G i, a i β • f (Function.update γ i β) = f γ) :
    ∑ γ : (∀ i, G i), (∏ i, a i (γ i)) • f γ = f 1 := by
  classical
  let c : Finset ι → (∀ i, G i) → ℂ := fun S γ =>
    ∏ i, (if i ∈ S then a i (γ i) else if γ i = 1 then 1 else 0)
  have key : ∀ S : Finset ι, ∑ γ, c S γ • f γ = f 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.sum_eq_single (1 : ∀ i, G i)]
      · simp [c]
      · intro γ _ hγ
        obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 1 := by
          by_contra hcon
          push_neg at hcon
          exact hγ (funext hcon)
        have : c ∅ γ = 0 := Finset.prod_eq_zero (mem_univ i) (by simp [hi])
        rw [this, zero_smul]
      · intro h; exact absurd (mem_univ _) h
    | insert j S hj ih =>
      rw [← ih]
      let h : ∀ i, G i → ℂ := fun i x => if i ∈ S then a i x else if x = 1 then 1 else 0
      have cU : ∀ (γ : ∀ i, G i) (β : G j),
          c S (Function.update γ j β) = h j β * ∏ i ∈ univ.erase j, h i (γ i) := by
        intro γ β
        show ∏ i, h i (Function.update γ j β i) = _
        rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro i hi
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have cI : ∀ γ : ∀ i, G i, c (insert j S) γ = a j (γ j) * ∏ i ∈ univ.erase j, h i (γ i) := by
        intro γ
        show ∏ i, _ = _
        rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro i hi
          have : i ≠ j := Finset.ne_of_mem_erase hi
          simp [h, this]
      have step1 : ∑ γ, c S γ • f γ
          = ∑ γ, ∑ β : G j, (c S γ * a j β) • f (Function.update γ j β) := by
        apply Finset.sum_congr rfl
        intro γ _
        by_cases hγ : γ j = 1
        · rw [← hf j γ hγ, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro β _
          rw [mul_smul]
        · have : c S γ = 0 := Finset.prod_eq_zero (mem_univ j) (by simp [hj, hγ])
          simp [this]
      let e : (∀ i, G i) × G j ≃ (∀ i, G i) × G j :=
        { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
          invFun := fun p => (Function.update p.1 j p.2, p.1 j)
          left_inv := by intro p; simp
          right_inv := by intro p; simp }
      rw [step1, ← Fintype.sum_prod_type']
      rw [← Fintype.sum_equiv e
        (fun p => (c S (Function.update p.1 j p.2) * a j (p.1 j)) • f p.1) _ (by
          intro p
          simp [e])]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro γ _
      dsimp only
      rw [← Finset.sum_smul, ← Finset.sum_mul]
      simp_rw [cU]
      rw [← Finset.sum_mul, cI]
      have : ∑ β : G j, h j β = 1 := by simp [h, hj]
      rw [this, one_mul, mul_comm]
  have := key univ
  simpa [c] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdFixedPlaceAverageStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_fixed_place_average_alt : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] {V : Type} [AddCommGroup V] [Module ℂ V] (a : ∀ i, G i → ℂ) (f : (∀ i, G i) → V), (∀ i (γ : ∀ i, G i), γ i = 1 → ∑ β : G i, a i β • f (Function.update γ i β) = f γ) → ∑ γ : (∀ i, G i), (∏ i, a i (γ i)) • f γ = f 1 := by
  first | exact @GlobalTheory.sum_prod_fixed_place_average | exact GlobalTheory.sum_prod_fixed_place_average | (intros; apply GlobalTheory.sum_prod_fixed_place_average <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumSeriesIdempotentCoeffRightTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.LabFix

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem rt_mul (a b : GAf L n) (f : GAf L n → ℂ) :
    Formalism.L2.NG.rt L n (a * b) f = Formalism.L2.NG.rt L n a (Formalism.L2.NG.rt L n b f) := by
  funext g
  show f (g * (a * b)) = f (g * a * b)
  rw [mul_assoc]

theorem rt_one (f : GAf L n → ℂ) : Formalism.L2.NG.rt L n 1 f = f := by
  funext g
  show f (g * 1) = f g
  rw [mul_one]

theorem exists_lifts (n : ℕ) (s : SplitPlace L) (g : ℕ) (hg : g.Prime) :
    ∃ ℓ : GL (Fin n) (ZMod g) → GAf L n, ∀ γ, IsLift s (ℓ γ) γ := by
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  have key : ∀ γ : GL (Fin n) (ZMod g), ∃ x : GAf L n, IsLift s x γ := by
    intro γ
    let A : Matrix (Fin n) (Fin n) ℤ := fun i j => (((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ)
    have hA : (Int.castRingHom (ZMod g)).mapMatrix A = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
      ext i j
      show ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ) : ZMod g) = _
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hdet : A.det ≠ 0 := by
      intro h0
      have h1 := congrArg (Int.castRingHom (ZMod g)) h0
      rw [RingHom.map_det, hA, map_zero] at h1
      exact (Matrix.isUnits_det_units γ).ne_zero h1
    let B : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
      (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))).mapMatrix A
    have hB : IsUnit B.det := by
      rw [isUnit_iff_ne_zero, ← RingHom.map_det, eq_intCast]
      exact Int.cast_ne_zero.mpr hdet
    obtain ⟨x, hx, hloc⟩ := GlobalTheory.T.exists_adelicUnitary_trivialOutside_splitPlace_loc_eq n s (Matrix.nonsingInvUnit B hB)
    refine ⟨x, hx, fun i j => ?_⟩
    have hij : (s.loc n x : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j =
        ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L)) := by
      rw [hloc]
      show (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) (A i j) = _
      rw [eq_intCast]
      exact Int.cast_natCast _
    rw [hij, sub_self, map_zero]
    exact zero_lt_one
  choose ℓ hℓ using key
  exact ⟨ℓ, hℓ⟩

end Gen

theorem sum_serCoef_rt : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (c : GAf D.host.E D.R.r) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf) (lf : G0g D.nd → GAf D.host.E D.R.r), FrameRed X h t PY c red → IsSec X red sec → (∀ γ, PY.ψ (lf γ) = kap X h t (sec γ)) → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (τ : Tup2 D), HasTuple D π τ → ∀ φ ∈ π.S, (∀ k ∈ X.B.I.Kg X.B.g, ∀ κ, PY.ψ κ = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r κ φ = φ) → ∑ᶠ γ, serCoef τ γ • Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ = φ := by
  intro D X h t PY c red sec lf hFR hsec hlf π τ hτ φ hφ hfix
  classical
  obtain ⟨hred, hex, hlift⟩ := hFR
  obtain ⟨-, hmul, -, hker⟩ := hred
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have kap_mul : ∀ k k' : X.B.I.Gf, kap X h t (k * k') = kap X h t k * kap X h t k' := by
    intro k k'
    have e : ((1, k * k') : X.B.I.GA) = (1, k) * (1, k') := by rw [Prod.mk_mul_mk, one_mul]
    have cm : ∀ a b : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * (a * b) * t = t⁻¹ * a * t * (t⁻¹ * b * t) := by
      intro a b; group
    unfold kap
    rw [e, map_mul]
    exact cm _ _
  have kap_inv : ∀ k : X.B.I.Gf, kap X h t k⁻¹ = (kap X h t k)⁻¹ := by
    intro k
    have e : ((1, k⁻¹) : X.B.I.GA) = (1, k)⁻¹ := by rw [Prod.inv_mk, inv_one]
    have ci : ∀ a : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹ := by
      intro a; group
    unfold kap
    rw [e, map_inv]
    exact ci _
  have K_one : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, OneMemClass.coe_one]
    exact one_mem _
  have K_mul : ∀ a b : X.B.I.Gf, a ∈ X.B.I.Kset → b ∈ X.B.I.Kset → a * b ∈ X.B.I.Kset := by
    intro a b ha hb
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, Subgroup.coe_mul] at *
    exact mul_mem ha hb
  have K_inv : ∀ a : X.B.I.Gf, a ∈ X.B.I.Kset → a⁻¹ ∈ X.B.I.Kset := by
    intro a ha
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, InvMemClass.coe_inv] at *
    exact inv_mem ha
  have red_one : red 1 = 1 := by
    have e := hmul 1 K_one 1 K_one
    rw [one_mul] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  have red_inv : ∀ k ∈ X.B.I.Kset, red k⁻¹ = (red k)⁻¹ := by
    intro k hk
    have e := hmul k⁻¹ (K_inv k hk) k hk
    rw [inv_mul_cancel, red_one] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have key : ∀ (γ : G0g D.nd) (y : GAf D.host.E D.R.r) (k : X.B.I.Gf), k ∈ X.B.I.Kset → red k = γ →
      PY.ψ y = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r y φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by
    intro γ y k hk hrk hy
    obtain ⟨hs1, hs2⟩ := hsec γ
    have hm : (sec γ)⁻¹ * k ∈ X.B.I.Kg X.B.g := by
      refine (hker _ (K_mul _ _ (K_inv _ hs1) hk)).1 ?_
      rw [hmul _ (K_inv _ hs1) _ hk, red_inv _ hs1, hs2, hrk, inv_mul_cancel]
    have hψ : PY.ψ ((lf γ)⁻¹ * y) = kap X h t ((sec γ)⁻¹ * k) := by
      rw [map_mul, map_inv, hlf, hy, kap_mul, kap_inv]
    have e := hfix _ hm _ hψ
    calc Formalism.L2.NG.rt D.host.E D.R.r y φ
        = Formalism.L2.NG.rt D.host.E D.R.r (lf γ * ((lf γ)⁻¹ * y)) φ := by rw [mul_inv_cancel_left]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r ((lf γ)⁻¹ * y) φ) := rt_mul _ _ _
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by rw [e]
  set φ' := Formalism.L2.NG.rt D.host.E D.R.r c⁻¹ φ with hφ'
  have hφ'S : φ' ∈ π.S := π.stable _ _ hφ
  have back : Formalism.L2.NG.rt D.host.E D.R.r c φ' = φ := by
    rw [hφ', ← rt_mul, mul_inv_cancel, rt_one]
  have fix1 : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (s : SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 →
      ∀ x, IsLift s x (1 : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) → Formalism.L2.NG.rt D.host.E D.R.r x φ' = φ' := by
    intro kv s hs x hx
    obtain ⟨k, hk, hψ, hr1, hr2⟩ := hlift kv s hs x 1 hx
    have hrk : red k = 1 := by
      funext kv'
      rw [Pi.one_apply]
      by_cases e : kv' = kv
      · subst e; exact hr1
      · exact hr2 kv' e
    have e := hfix k ((hker k hk).1 hrk) _ hψ
    calc Formalism.L2.NG.rt D.host.E D.R.r x φ'
        = Formalism.L2.NG.rt D.host.E D.R.r c⁻¹ (Formalism.L2.NG.rt D.host.E D.R.r (c * x * c⁻¹) φ) := by
          rw [hφ', ← rt_mul, ← rt_mul]; congr 1; group
      _ = φ' := by rw [e]
  have step : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (γ : G0g D.nd), γ kv = 1 →
      ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
        Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by
    intro kv γ hγ
    obtain ⟨s, hs⟩ := hex kv
    obtain ⟨ℓ, hℓ⟩ := exists_lifts D.R.r s (D.host.g kv.1) (D.host.g_prime kv.1)
    have hser := ((hτ kv.1 kv.2).2 s hs) ℓ hℓ φ' hφ'S (fix1 kv s hs)
    rw [finsum_eq_sum_of_fintype] at hser
    have hterm : ∀ β, Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ =
        Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c (Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) := by
      intro β
      obtain ⟨k, hk, hψ, hr1, hr2⟩ := hlift kv s hs (ℓ β) β (hℓ β)
      obtain ⟨hs1, hs2⟩ := hsec γ
      have hred : red (sec γ * k) = Function.update γ kv β := by
        rw [hmul _ hs1 _ hk, hs2]
        funext kv'
        by_cases e : kv' = kv
        · subst e; simp [hγ, hr1]
        · simp [Function.update_of_ne e, hr2 kv' e]
      have e := key _ (lf γ * (c * ℓ β * c⁻¹)) (sec γ * k) (K_mul _ _ hs1 hk) hred
        (by rw [map_mul, hlf, hψ, kap_mul])
      rw [← e, hφ', ← rt_mul, ← rt_mul, ← rt_mul]
      congr 1
      group
    calc ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
          Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ
        = ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
          Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c (Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) :=
          Finset.sum_congr rfl fun β _ => by rw [hterm]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c
          (∑ β, (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β • Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by rw [hser, back]
  have hfin := GlobalTheory.T.sum_prod_fixed_place_average_alt (ι := Σ k : Fin 2, D.nd.PlG k) (G := fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (fun kv β => (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β) (fun γ => Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ) step
  have h1 : Formalism.L2.NG.rt D.host.E D.R.r (lf 1) φ = φ :=
    hfix (sec 1) ((hker _ (hsec 1).1).1 ((hsec 1).2)) _ (hlf 1)
  rw [finsum_eq_sum_of_fintype]
  exact hfin.trans h1

end GlobalTheory.LabFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumSeriesIdempotentCoeffRightTranslationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_seriesIdempotentCoeff_rightTranslation : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (c : GAf D.host.E D.R.r) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf) (lf : G0g D.nd → GAf D.host.E D.R.r), FrameRed X h t PY c red → IsSec X red sec → (∀ γ, PY.ψ (lf γ) = kap X h t (sec γ)) → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (τ : Tup2 D), HasTuple D π τ → ∀ φ ∈ π.S, (∀ k ∈ X.B.I.Kg X.B.g, ∀ κ, PY.ψ κ = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r κ φ = φ) → ∑ᶠ γ, serCoef τ γ • Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ = φ := by
  first | exact @GlobalTheory.LabFix.sum_serCoef_rt | exact GlobalTheory.LabFix.sum_serCoef_rt | (intros; apply GlobalTheory.LabFix.sum_serCoef_rt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRowsFixedByLabelTupleOpOfSumFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeffChosenRedEqRedHom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem coeff_goodAt_eq (D : D7) (X : HidaSetting D) (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ b, a * b = b * a)
    (x : X.B.I.Gf) (γ γ' : G0g D.nd) (h : GoodAt X x γ) (h' : GoodAt X x γ') : a.coeff γ' = a.coeff γ := by
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      γ' kv = P⁻¹ * γ kv * P := by
    intro kv
    exact Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2))
      (D.host.g kv.1) (D.host.g_prime kv.1)
      (by rw [Formalism.L2.SG.Pf.RowDictPf.card_wB, Formalism.L2.SG.Pf.RowDictPf.card_res_host]) D.R.r X.n_eq.symm x (γ kv) (γ' kv)
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h kv))
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h' kv))
  choose P hP using hP
  have e : γ' = (P : G0g D.nd)⁻¹ * γ * P := funext fun kv => hP kv
  rw [e]
  exact Formalism.L2.SG.Pf.RowDictPf.coeff_conj_of_central ha γ P

theorem coeff_chosenRed_eq_redHom : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd), IsRedHom X red →
    ∀ a : MonoidAlgebra ℂ (G0g D.nd), (∀ b, a * b = b * a) → ∀ x : X.B.I.Gf,
    (if h : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ then
      a.coeff (Classical.choose h.2) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0) =
    if x ∈ X.B.I.Kset then a.coeff (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 := by
  intro D X red hred a ha x
  by_cases hx : x ∈ X.B.I.Kset
  · have hc : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ := ⟨hx, red x, hred.1 x hx⟩
    rw [dite_eq_left hc, if_pos hx,
      coeff_goodAt_eq D X a ha x (red x) (Classical.choose hc.2) (hred.1 x hx) (Classical.choose_spec hc.2)]
  · rw [dite_eq_right (fun h => hx h.1), if_neg hx]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ESSingleCoeffCentral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabIdem

theorem ES_single_coeff_central : ∀ (D : D7) (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) →
    (∀ γ, (ES {t}).coeff γ = serCoef t γ) ∧ ∀ b, ES {t} * b = b * ES {t} := by
  intro D t _
  have e : (ES {t} : MonoidAlgebra ℂ (G0g D.nd)) = GlobalTheory.RowLev.zTup D t := GlobalTheory.RowLev.ES_singleton (D := D) t
  refine ⟨fun γ => ?_, fun b => ?_⟩
  · rw [e]; rfl
  · rw [e]; exact GlobalTheory.RowLev.zTup_comm t b

end GlobalTheory.LabIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvUniqueAddSmulMulComm
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.WeakConv

section General

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (μ : Measure G) (π : G → (H →L[ℂ] H))

def IsWeakInt (e : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  Integrable e μ ∧ ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ

variable {μ π}

private theorem integrable_mul_of_bounded {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f c : α → ℂ} (hf : Integrable f ν) (hc : AEStronglyMeasurable c ν) (C : ℝ)
    (hb : ∀ a, ‖c a‖ ≤ C) : Integrable (fun a => f a * c a) ν := by
  refine Integrable.mono' (hf.norm.mul_const C) (hf.aestronglyMeasurable.mul hc) (ae_of_all _ fun a => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb a) (norm_nonneg _)


omit [Group G] [IsTopologicalGroup G] [SecondCountableTopology G] [CompleteSpace H] in
theorem integrable_mul_coeff (hn : ∀ g y, ‖π g y‖ = ‖y‖) (hc : ∀ y, Continuous fun g => π g y)
    {e : G → ℂ} (he : Integrable e μ) (x y : H) :
    Integrable (fun g => e g * ⟪x, π g y⟫_ℂ) μ := by
  have hcm : Continuous fun g => ⟪x, π g y⟫_ℂ := continuous_const.inner (hc y)
  refine integrable_mul_of_bounded he hcm.aestronglyMeasurable (‖x‖ * ‖y‖) fun g => ?_
  calc ‖⟪x, π g y⟫_ℂ‖ ≤ ‖x‖ * ‖π g y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [hn]


omit [Group G] [IsTopologicalGroup G] [SecondCountableTopology G] [TopologicalSpace G] [BorelSpace G] in
theorem IsWeakInt.inner_comp {e : G → ℂ} {T : H →L[ℂ] H} (h : IsWeakInt μ π e T) (A : H →L[ℂ] H)
    (x y : H) : ⟪x, A (T y)⟫_ℂ = ∫ g, e g * ⟪x, A (π g y)⟫_ℂ ∂μ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, h.2]
  simp_rw [ContinuousLinearMap.adjoint_inner_left]

theorem IsWeakInt.conv [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (hm : ∀ g h, π (g * h) = (π g).comp (π h))
    (hn : ∀ g y, ‖π g y‖ = ‖y‖) (hc : ∀ y, Continuous fun g => π g y)
    {e e' : G → ℂ} {T T' : H →L[ℂ] H} (h : IsWeakInt μ π e T) (h' : IsWeakInt μ π e' T') :
    IsWeakInt μ π (fun k => ∫ g, e g * e' (g⁻¹ * k) ∂μ) (T.comp T') := by
  have hP : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2)) (μ.prod μ) := by
    have h0 : Integrable (fun z : G × G => e z.1 * e' z.2) (μ.prod μ) := h.1.mul_prod h'.1
    exact ((measurePreserving_prod_inv_mul μ μ).integrable_comp h0.aestronglyMeasurable).2 h0
  refine ⟨hP.integral_prod_right, fun x y => ?_⟩
  have hcm : Continuous fun k => ⟪x, π k y⟫_ℂ := continuous_const.inner (hc y)
  have hcm2 : Measurable fun z : G × G => ⟪x, π z.2 y⟫_ℂ := hcm.measurable.comp measurable_snd
  have hQ : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2) * ⟪x, π z.2 y⟫_ℂ) (μ.prod μ) := by
    refine integrable_mul_of_bounded hP hcm2.aestronglyMeasurable (‖x‖ * ‖y‖) fun z => ?_
    calc ‖⟪x, π z.2 y⟫_ℂ‖ ≤ ‖x‖ * ‖π z.2 y‖ := norm_inner_le_norm _ _
      _ = ‖x‖ * ‖y‖ := by rw [hn]
  have hin : ∀ g, ⟪x, π g (T' y)⟫_ℂ = ∫ k, e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ := by
    intro g
    rw [h'.inner_comp (π g) x y]
    refine (integral_mul_left_eq_self _ g⁻¹).symm.trans ?_
    congr 1
    ext k
    have hk : π g (π (g⁻¹ * k) y) = π k y := by
      rw [← ContinuousLinearMap.comp_apply, ← hm, mul_inv_cancel_left]
    simp only [hk]
  calc ⟪x, (T.comp T') y⟫_ℂ = ∫ g, e g * ⟪x, π g (T' y)⟫_ℂ ∂μ := h.2 x (T' y)
    _ = ∫ g, ∫ k, e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ ∂μ := by
        congr 1
        ext g
        rw [hin, ← integral_const_mul]
        congr 1
        ext k
        ring
    _ = ∫ k, ∫ g, e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ ∂μ :=
        integral_integral_swap (f := fun g k => e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ) hQ
    _ = ∫ k, (∫ g, e g * e' (g⁻¹ * k) ∂μ) * ⟪x, π k y⟫_ℂ ∂μ := by
        congr 1
        ext k
        rw [integral_mul_const]

end General

theorem rightConv_unique_add_smul_mul_comm : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)), I.IsFundDom (I.muA μf) fund → I.IsRightReg μf fund R → (∀ e T T', I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e T' → T = T') ∧ (∀ e e' T T', I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e' T' → I.IsRConvF μf fund R (e + e') (T + T')) ∧ (∀ (c : ℂ) e T, I.IsRConvF μf fund R e T → I.IsRConvF μf fund R (c • e) (c • T)) ∧ (∀ e e' T T', Continuous e → Continuous e' → I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e' T' → I.IsRConvF μf fund R (I.convF μf e e') (T.comp T')) ∧ ∀ e T (x : I.Ginf), I.IsRConvF μf fund R e T → T.comp (R (x, 1)) = (R (x, 1)).comp T := by
  intro I μf hH hS fund R hfund hR
  obtain ⟨-, hmul, hn, hc⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous I μf fund hfund R hR
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  have hm' : ∀ g h : I.Gf, R (1, g * h) = (R (1, g)).comp (R (1, h)) := by
    intro g h
    rw [← hmul, Prod.mk_mul_mk, one_mul]
  have hn' : ∀ (g : I.Gf) (F : I.L2 μf fund), ‖R (1, g) F‖ = ‖F‖ := fun g F => hn _ F
  have hc' : ∀ F : I.L2 μf fund, Continuous fun g : I.Gf => R (1, g) F := fun F =>
    Continuous.comp (g := fun x : I.GA => R x F) (f := fun g : I.Gf => ((1 : I.Ginf), g)) (hc F)
      (continuous_const.prodMk continuous_id)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e T T' h h'
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_
    rw [h.2, h'.2]
  · intro e e' T T' h h'
    refine ⟨h.1.add h'.1, fun z y => ?_⟩
    have i1 := integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h.1 z y
    have i2 := integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h'.1 z y
    rw [ContinuousLinearMap.add_apply, inner_add_right, h.2, h'.2, ← integral_add i1 i2]
    congr 1
    ext g
    simp only [Pi.add_apply]
    ring
  · intro c e T h
    refine ⟨h.1.smul c, fun z y => ?_⟩
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, h.2, ← integral_const_mul]
    congr 1
    ext g
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro e e' T T' _ _ h h'
    exact IsWeakInt.conv (μ := μf) (π := fun g : I.Gf => R (1, g)) hm' hn' hc' h h'
  · intro e T x h
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_
    have hcomm : ∀ g : I.Gf, R (1, g) (R (x, 1) y) = R (x, 1) (R (1, g) y) := by
      intro g
      have key : R ((1, g) * (x, 1)) = R ((x, 1) * (1, g)) := by
        congr 1
        simp
      rw [hmul, hmul] at key
      exact congrArg (fun A : I.L2 μf fund →L[ℂ] I.L2 μf fund => A y) key
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h.2 z (R (x, 1) y),
      IsWeakInt.inner_comp (μ := μf) (π := fun g : I.Gf => R (1, g)) h (R (x, 1)) z y]
    simp only [hcomm]

end GlobalTheory.WeakConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRowsFixedByLabelTupleOpOfSumFixed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabFix

theorem mem_VT_of_sum_fixed : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf), IsRedHom X red → IsSec X red sec → ∀ (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) → ∀ f ∈ HHX X, ∑ᶠ γ, serCoef t γ • X.B.R ((1, sec γ) : X.B.I.GA) f = f → f ∈ VT X t := by
  intro D X red sec hred hsec t ht f hf hsum
  classical
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  let ρ : GlobalTheory.RowLev.Red X.B.I X.B.g (G0g D.nd) :=
    { toFun := red, map_mul := hred.2.1, ker := hred.2.2.2, surj := hred.2.2.1 }
  obtain ⟨hcoef, hcent⟩ := GlobalTheory.LabIdem.ES_single_coeff_central D t ht
  have hegA : egA X (ES {t}) = ρ.lift X.B.μf (ES {t}) := by
    funext x
    rw [egA, GlobalTheory.coeff_chosenRed_eq_redHom D X red hred _ hcent x]
    by_cases hx : x ∈ X.B.I.Kset
    · rw [if_pos hx, GlobalTheory.RowLev.Red.lift_of_mem ρ _ _ hx]
    · rw [if_neg hx, GlobalTheory.RowLev.Red.lift_of_notMem ρ _ _ hx]
  obtain ⟨h1R, hm, hn, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  obtain ⟨huniq, -, -, hprod, -⟩ := GlobalTheory.WeakConv.rightConv_unique_add_smul_mul_comm X.B.I X.B.μf X.B.fund X.B.R
    X.B.fund_spec X.B.R_spec
  obtain ⟨hQ, -, -, -, -, hinfl, -, -, -⟩ := GlobalTheory.InflBasic.inflation_basic X.B.I X.B.g (G0g D.nd) ρ X.B.μf hg
  letI : Fintype (G0g D.nd) := Fintype.ofFinite _
  obtain ⟨hlint, hlloc, -⟩ := hinfl (ES {t})
  obtain ⟨Ta, hTa⟩ := (GlobalTheory.AutInst_exists_isRConvF_and_isRConv X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R
    X.B.R_spec).1 _ hlint
  have he := X.B.e_adm
  have hecont : Continuous X.B.e := he.1.continuous
  have hReRe : X.B.Re.comp X.B.Re = X.B.Re := by
    have h := hprod _ _ _ _ hecont hecont X.B.Re_spec X.B.Re_spec
    rw [he.2.1] at h
    exact huniq _ _ _ h X.B.Re_spec
  have hRT : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) (X.B.Re.comp Ta) := by
    unfold eT
    rw [hegA]
    exact hprod _ _ _ _ hecont hlloc.continuous X.B.Re_spec hTa
  have hReT : ReT X {t} = X.B.Re.comp Ta := by
    have hex : ∃ T, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) T := ⟨_, hRT⟩
    unfold ReT
    rw [dite_eq_left hex]
    exact huniq _ _ _ (Classical.choose_spec hex) hRT
  obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hf
  have hRef : X.B.Re f = f := by
    rw [← hz]
    show X.B.Re (X.B.Re (X.Rph z)) = X.B.Re (X.Rph z)
    rw [← ContinuousLinearMap.comp_apply X.B.Re X.B.Re, hReRe]
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := h1R
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b
    rw [ContinuousLinearMap.mul_def, ← hm]
    simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => hn _ v
  have hone : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
    refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, X.B.I.Lf.zero_mem, ?_⟩⟩
    have : X.B.I.fmat 1 = 1 := rfl
    simp [this]
  haveI : SecondCountableTopology X.B.I.Gf := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints X.B.I
  have hfix : ∀ k ∈ X.B.I.Kg X.B.g, X.B.R (1, k) f = f := by
    intro k hk
    have h := GlobalTheory.IdemProj.op_fixed X.B.μf (fun g => X.B.R (1, g)) p1 pm pn X.B.e X.B.Re X.B.Re_spec.2 k
      (fun x => by simpa using he.2.2.2.2.2.1 x k hk 1 hone)
    rw [← hRef, ← ContinuousLinearMap.comp_apply]
    exact DFunLike.congr_fun h f
  have hTaf : Ta f = f := by
    apply ext_inner_left ℂ
    intro v
    rw [hTa.2, GlobalTheory.LevelIdem.integral_lift ρ X.B.μf hg (ES {t}) sec hsec (fun x => ⟪v, X.B.R (1, x) f⟫_ℂ) ?_]
    · conv_rhs => rw [← hsum]
      rw [finsum_eq_sum_of_fintype, inner_sum]
      simp only [inner_smul_right, hcoef]
    · intro x k hk
      show ⟪v, X.B.R (1, x * k) f⟫_ℂ = ⟪v, X.B.R (1, x) f⟫_ℂ
      rw [show ((1 : X.B.I.Ginf), x * k) = ((1, x) : X.B.I.GA) * (1, k) by simp, hm,
        ContinuousLinearMap.comp_apply, hfix k hk]
  refine Submodule.mem_inf.2 ⟨hf, ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  show ReT X {t} f = f
  rw [hReT, ContinuousLinearMap.comp_apply, hTaf, hRef]

end GlobalTheory.LabFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRowsFixedByLabelTupleOpOfSumFixedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rowsFixedByLabelTupleOp_of_sum_fixed : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf), IsRedHom X red → IsSec X red sec → ∀ (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) → ∀ f ∈ HHX X, ∑ᶠ γ, serCoef t γ • X.B.R ((1, sec γ) : X.B.I.GA) f = f → f ∈ VT X t := by
  first | exact @GlobalTheory.LabFix.mem_VT_of_sum_fixed | exact GlobalTheory.LabFix.mem_VT_of_sum_fixed | (intros; apply GlobalTheory.LabFix.mem_VT_of_sum_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabelsFixedByTupleOperatorOfTypeSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.LabPinTop

theorem kap_mem_GfC {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (k : X.B.I.Gf) : kap X h t k ∈ GfC (Yc D 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (k : I.Gf),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm ((1, k) : I.GA) ∈ GfC (D.sp.Y 0) := by
    intro I hI k
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm (1, k) =
        (Formalism.IndefR.RationalEmbedding.iota D).symm (1, k) := rfl
    rw [e]
    exact (Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (D := D) (1, k)).2 rfl
  have hy : (iotaX X h).symm ((1, k) : X.B.I.GA) ∈ GfC (D.sp.Y 0) := aux X.B.I h k
  show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) ∈ GfC (D.sp.Y 0)
  unfold GfC at hy ⊢
  rw [MonoidHom.mem_ker] at hy ⊢
  rw [map_mul, map_mul, hy, mul_one, map_inv, inv_mul_cancel]

theorem R_translate_ae {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (Φ : GA D (D.sp.Y 0) → ℂ) (hinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g) (f : L2X X)
    (hf : f =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t)) (k : X.B.I.Gf) :
    ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      Φ ((iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k)) := by
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      Φ ((iotaX X h).symm (γ * y) * t) = Φ ((iotaX X h).symm y * t) := by
    intro γ hγ y
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
    Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
  have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
    have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
    rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
  have e1 := X.B.R_spec (1, k) f
  have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
      Φ ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
    refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = Φ ((iotaX X h).symm y * t)) h1 ?_
    rw [h2]
    exact hf
  filter_upwards [e1, e3] with x a1 a3
  rw [a1]
  show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
  rw [a3]
  obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
  rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
    hφinv γ hγ]
  congr 1
  unfold kap
  rw [map_mul]
  group

end GlobalTheory.LabPinTop

namespace GlobalTheory.LabPinTop

theorem labTie_of_series : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (C : Submodule ℂ (MMap (R.MY 0))), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ F, ι (D.sEE F) = conjHH X G (j F)) → RowJ R eE X h G t j → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotIn (actM PY (R.MY 0)) C (FinTyp.conjT (rep (D.what₂.ft σ)))) → (∀ σ, ∀ k ∈ X.B.I.Kg X.B.g, ∀ v y, R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t k) = R.HE.e (eE (D.what₂.onb σ)) v y) → (∀ σ v, ∀ γ ∈ Formalism.L2.Theta.GQ (Yc D 0), ∀ y, R.HE.e (eE (D.what₂.onb σ)) v (γ * y) = R.HE.e (eE (D.what₂.onb σ)) v y) → TypeLab D rep → (∀ σ, D.ntypes.goodTuple (labOf σ)) → LabTie X ι := by
  intro D X h t PY hF G' _ _ Pl0 T A Ks _ _ _ R eE G j ι rep C hStd hHEq hι hJ hiso hK hQ hTL hgood
  let _ : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
  have hlab : ∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v) := fun σ k v => ((hTL (D.what₂.ft σ)) k v).1
  refine ⟨hlab, hgood, fun σ => ?_⟩
  obtain ⟨c, red, hFR⟩ := GlobalTheory.T.exists_maximalCompact_reduction_standardFrame D X h t PY hF hStd hHEq
  have hRH : IsRedHom X red := hFR.1
  choose sec hsec using hRH.2.2.1
  have hIS : IsSec X red sec := fun γ => hsec γ
  choose lf hlf using fun γ => PY.onto _ (kap_mem_GfC X h t (sec γ))
  have hser := GlobalTheory.T.sum_seriesIdempotentCoeff_rightTranslation D X h t PY c red sec lf hFR hIS hlf (rep (D.what₂.ft σ)) (labOf σ) (hTL (D.what₂.ft σ))
  have hS := GlobalTheory.T.fixedVectorIdentity_isotypic_conjugateType D D.R.r (MMap (R.MY 0)) (actM PY (R.MY 0)) C (rep (D.what₂.ft σ))
    {κ | ∃ k ∈ X.B.I.Kg X.B.g, PY.ψ κ = kap X h t k} (G0g D.nd) (serCoef (labOf σ)) lf
    (fun φ hφ hU => hser φ hφ (fun k hk κ hκ => hU κ ⟨k, hk, hκ⟩)) (R.HE.e (eE (D.what₂.onb σ))) (hiso σ)
    (by
      rintro κ ⟨k, hk, hκ⟩
      refine MultilinearMap.ext fun v => funext fun y => ?_
      rw [actM_apply, hκ]
      exact hK σ k hk v y)
  have hpt : ∀ v y, ∑ γ, star (serCoef (labOf σ) γ) * R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t (sec γ)) =
      R.HE.e (eE (D.what₂.onb σ)) v y := by
    intro v y
    have e := congrArg (fun T : MMap (R.MY 0) => T v y) hS
    simp only [finsum_eq_sum_of_fintype] at e
    rw [← e, sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [smul_apply, Pi.smul_apply, smul_eq_mul, actM_apply, hlf]
  obtain ⟨v₀, -, a, -, hj⟩ := hJ
  refine GlobalTheory.T.mem_rowsFixedByLabelTupleOp_of_sum_fixed D X red sec hRH hIS (labOf σ) (fun k v => hlab σ k v) (bRow X ι σ)
    (ι (D.sEE (D.what₂.onb σ))).2 ?_
  set Φ : GA D (D.sp.Y 0) → ℂ := fun y => star ((a : ℂ) * R.HE.e (eE (D.what₂.onb σ)) v₀ y) with hΦ
  have hΦinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g := fun γ hγ g =>
    congrArg (fun z => star ((a : ℂ) * z)) (hQ σ v₀ γ hγ g)
  have hb : bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := by
    show ((ι (D.sEE (D.what₂.onb σ)) : HHX X) : L2X X) = _
    rw [hι]
    rfl
  have hbr : (bRow X ι σ : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t) := by
    rw [hb]
    filter_upwards [Lp.coeFn_star ((j (D.what₂.onb σ) : EEC X G) : L2X X), hj (D.what₂.onb σ)] with x b1 b2
    rw [b1, Pi.star_apply, b2]
    rfl
  have htr := fun γ => R_translate_ae X h t Φ hΦinv (bRow X ι σ) hbr (sec γ)
  rw [finsum_eq_sum_of_fintype]
  apply Lp.ext
  filter_upwards [coeFn_sum_smul (μ := muX X) (serCoef (labOf σ)) (fun γ => X.B.R ((1, sec γ) : X.B.I.GA) (bRow X ι σ)),
    ae_all_iff.2 htr, hbr] with x b1 b2 b3
  rw [b1, b3]
  simp only [b2, hΦ]
  rw [← hpt v₀ ((iotaX X h).symm x * t)]
  rw [Finset.mul_sum, star_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have e : ∀ (c b s : ℂ), c * star (b * s) = star (b * (star c * s)) := fun c b s => by
    simp only [star_mul', star_star]; ring
  exact e _ _ _

end GlobalTheory.LabPinTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabelsFixedByTupleOperatorOfTypeSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labels_fixed_by_tupleOperator_of_typeSeries : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (C : Submodule ℂ (MMap (R.MY 0))), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ F, ι (D.sEE F) = conjHH X G (j F)) → RowJ R eE X h G t j → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotIn (actM PY (R.MY 0)) C (FinTyp.conjT (rep (D.what₂.ft σ)))) → (∀ σ, ∀ k ∈ X.B.I.Kg X.B.g, ∀ v y, R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t k) = R.HE.e (eE (D.what₂.onb σ)) v y) → (∀ σ v, ∀ γ ∈ Formalism.L2.Theta.GQ (Yc D 0), ∀ y, R.HE.e (eE (D.what₂.onb σ)) v (γ * y) = R.HE.e (eE (D.what₂.onb σ)) v y) → TypeLab D rep → (∀ σ, D.ntypes.goodTuple (labOf σ)) → LabTie X ι := by
  first | exact @GlobalTheory.LabPinTop.labTie_of_series | exact GlobalTheory.LabPinTop.labTie_of_series | (intros; apply GlobalTheory.LabPinTop.labTie_of_series <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationLabelsNormalisedOfRowsTypesLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open scoped TensorProduct

namespace GlobalTheory.LabPinAt

theorem mult_lev_left {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    (∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g) ∧ ∀ v, ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact ⟨hx.lev, fun v γ hγ g => (hx.aut v).left γ hγ g⟩
  | zero => exact ⟨fun v k _ g => by simp, fun v γ _ g => by simp⟩
  | add x y _ _ hx hy =>
    refine ⟨fun v k hk g => ?_, fun v γ hγ g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.1 v k hk g, hy.1 v k hk g]; ring
    · simp only [MultilinearMap.add_apply, Pi.add_apply, hx.2 v γ hγ g, hy.2 v γ hγ g]
  | smul c x _ hx =>
    refine ⟨fun v k hk g => ?_, fun v γ hγ g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.1 v k hk g]; ring
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx.2 v γ hγ g]

end GlobalTheory.LabPinAt

theorem GlobalTheory.LabPinAt.labTie_at : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (F : Face D A), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ y, ι (D.sEE y) = conjHH X G (j y)) → RowJ R eE X h G t j → LevelMatchA R F X h t → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → TypeLab D rep → GoodFTAll D → LabTie X ι := by
  intro D X h t PY hF G' _ _ Pl0 T A Ks _ _ _ R eE G j ι rep F hPsi hE hι hRJ hLev hIso hTL hGood
  have hM : ∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ Mult R.θ (R.MY 0) (JR R F) (chiR R F) := fun σ => (hIso σ).1.1
  refine GlobalTheory.T.labels_fixed_by_tupleOperator_of_typeSeries D X h t PY hF G' Pl0 T A Ks R eE G j ι rep (Minf R.θ PY (R.MY 0)) hPsi hE hι hRJ
    (fun σ => (hIso σ).2) ?_ ?_ hTL (fun σ => hGood (D.what₂.ft σ))
  · intro σ k hk v y
    obtain ⟨hk2, hc⟩ := (Formalism.L2.SG.Closed.level_subgroup_properties X).1 k hk
    obtain ⟨hJ, hχ⟩ := hLev k hk2
    rw [(GlobalTheory.LabPinAt.mult_lev_left R.θ (hM σ)).1 v _ hJ y, show chiR R F (kap X h t k) = star (X.chi2 k) from hχ, hc,
      star_one, one_mul]
  · intro σ v γ hγ y
    exact (GlobalTheory.LabPinAt.mult_lev_left R.θ (hM σ)).2 v γ hγ y
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationLabelsNormalisedOfRowsTypesLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisationLabels_normalised_of_rowsTypes_levels : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (F : Face D A), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ y, ι (D.sEE y) = conjHH X G (j y)) → RowJ R eE X h G t j → LevelMatchA R F X h t → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → TypeLab D rep → GoodFTAll D → LabTie X ι := by
  first | exact @GlobalTheory.LabPinAt.labTie_at | exact GlobalTheory.LabPinAt.labTie_at | (intros; apply GlobalTheory.LabPinAt.labTie_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditio
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl Formalism.IndefR.principalLevelFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.Sat

theorem ties_at : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (F0 : ∀ u, Forms0 D u) (s : SAt R F eE F0) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r), StdPsi hF PY → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → GlobalTheory.LabPin.TypeLab D rep → GoodFTAll D → Formalism.MainNotions.S.AutTie D s.P.X.B s.P.X.pl ∧ RowDictTie s.P.X s.P.G s.S.hI.eHH ∧ GlobalTheory.LabPin.LabTie s.P.X s.S.hI.eHH := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F eE F0 s PY hF rep hP hiso hT hG
  exact ⟨s.S.autTie, s.S.rowTie,
    GlobalTheory.T.realisationLabels_normalised_of_rowsTypes_levels D s.P.X s.P.inst s.t PY hF G' Pl0 T A Ks R eE s.P.G s.S.j s.S.hI.eHH rep F hP s.P.pin s.S.rowPin s.rowJ
      s.see.levelMatchA hiso hT hG⟩

end GlobalTheory.Sat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditioStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl Formalism.IndefR.principalLevelFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constructedSpectralObjects_irreducibilityConditions : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (F0 : ∀ u, Forms0 D u) (s : SAt R F eE F0) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r), StdPsi hF PY → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → GlobalTheory.LabPin.TypeLab D rep → GoodFTAll D → Formalism.MainNotions.S.AutTie D s.P.X.B s.P.X.pl ∧ RowDictTie s.P.X s.P.G s.S.hI.eHH ∧ GlobalTheory.LabPin.LabTie s.P.X s.S.hI.eHH := by
  first | exact @GlobalTheory.Sat.ties_at | exact GlobalTheory.Sat.ties_at | (intros; apply GlobalTheory.Sat.ties_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsTerAlt
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.principalLevelFrame GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.RowFrameParts

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R F X0), StdPsi Y.hF Y.PY ∧ ∀ σ, R.HE.e (Y.eE (D.what₂.onb σ)) ∈ isotE R.θ Y.PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rowRepR R.θ (Y.eFT (D.what₂.ft σ))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y
  refine ⟨Y.stdPsi.1, fun σ => ?_⟩
  have h := Y.tied.sharp.ft σ
  have h1 := Y.prtE (D.what₂.ft σ)
  have h2 := Y.eE_read (D.what₂.onb σ)
  have h3 := h1 ▸ h
  obtain ⟨z, hz, hze⟩ := h3
  rw [h2] at hze
  have : z = R.HE.e (Y.eE (D.what₂.onb σ)) := LinearEquiv.injective _ hze
  rw [← this]
  exact hz

end GlobalTheory.Mem.R3.RowFrameParts
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.Fc.LabLinked

def Ties (D : D7) : Prop :=
  ∃ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X),
    Formalism.MainNotions.S.AutTie D X.B X.pl ∧ Formalism.L2.SG.RowDict.RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι


section Rows

open _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX


end Rows

theorem lab_of_rows {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
  fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩


end GlobalTheory.Fc.LabLinked

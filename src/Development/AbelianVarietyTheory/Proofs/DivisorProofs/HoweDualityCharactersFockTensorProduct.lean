module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWeilDatumTransportCmApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthTensorProductFactors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.HarmonicAllOfCompact
noncomputable section
namespace GlobalTheory.FockAlg.Model
open Formalism.BasicNotions.TH MvPolynomial

def fockEmb (σ : Type) [DecidableEq σ] :
    MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2 :=
  (basisMonomials σ ℂ).constr ℂ fun α =>
    lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ)

theorem isFockIsometry_fockEmb (σ : Type) [DecidableEq σ] : IsFockIP (fockEmb σ) := by
  intro α β
  have h : ∀ γ : σ →₀ ℕ, fockEmb σ (monomial γ 1) =
      lp.single 2 γ ((Real.sqrt (γ.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro γ
    have := (basisMonomials σ ℂ).constr_basis ℂ (fun α : σ →₀ ℕ =>
      (lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) :
        lp (fun _ : σ →₀ ℕ => ℂ) 2)) γ
    simpa [fockEmb] using this
  rw [h, h, lp.inner_single_left]
  split_ifs with e
  · subst e
    have h0 : 0 ≤ α.prod fun _ k => (k.factorial : ℝ) :=
      Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    rw [lp.single_apply_self, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt h0]
    simp [Finsupp.prod]
  · rw [lp.single_apply_ne _ _ _ e, inner_zero_right]

end GlobalTheory.FockAlg.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomials
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightLeSpanSupFockCoinvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionHomogeneousEigenvector
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.JointHarm

namespace GlobalTheory.FockScalarType

theorem injective_of_isFockIP {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι) :
    Function.Injective ι := by
  have key : ∀ (α : σ →₀ ℕ) (P : MvPolynomial σ ℂ), inner ℂ (ι (monomial α 1)) (ι P) =
      AddMonoidAlgebra.coeff P α * α.prod (fun _ k => (k.factorial : ℂ)) := by
    intro α P
    induction P using MvPolynomial.induction_on' with
    | add P P' h h' => simp only [map_add (f := _), inner_add_right, h, h', MvPolynomial.coeff_add, add_mul]
    | monomial β c =>
      rw [monomial_eq_smul β c, map_smul, inner_smul_right, hι, coeff_smul, coeff_monomial]
      by_cases e : α = β
      · subst e; simp
      · simp [e, Ne.symm e]
  refine (injective_iff_map_eq_zero ι).2 fun P hP => ?_
  ext α
  have h := key α P
  rw [hP, inner_zero_right, eq_comm, mul_eq_zero] at h
  refine h.resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

variable {p q r s : ℕ}

def charSub (p q r s : ℕ) (x : ℚ) : Submodule ℂ (Pol p q r s) where
  carrier := {f | ∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y f = ((x : ℂ) * Y.trace) • f}
  add_mem' := fun ha hb Y hY => by rw [map_add (f := _), ha Y hY, hb Y hY, smul_add]
  zero_mem' := fun Y _ => by simp
  smul_mem' := fun c _ ha Y hY => by rw [map_smul, ha Y hY, smul_comm]

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem isHW_of_mem {x : ℚ} {f : Pol p q r s} (h0 : f ≠ 0) (hf : f ∈ charSub p q r s x) :
    IsHW (fockAct1 p q r s) (fun _ => x) f := by
  refine ⟨h0, ?_, ?_⟩
  · simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [hf _ (isKC_Eab (by rcases a with a | a <;> trivial))]
    simp [Eab]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    have h1 : sameBlock a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]
    have h2 : a ≠ b := by
      rintro rfl
      rcases a with a | a <;> simp [posC] at hab
    rw [hf _ (isKC_Eab h1), Eab, Matrix.trace_single_eq_of_ne _ _ _ h2]
    simp

theorem comm_parts {Y : Mat p q} (hY : IsKC Y) {Z : Mat r s} (hZ : IsPC Z) {d : ℕ}
    {v : Pol p q r s} (hv : v ∈ homog (Ln p q r s) d) :
    fockAct1 p q r s Y (upOp (kron2 p q Z) v) = upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∧
    fockAct1 p q r s Y (dnOp (kron2 p q Z) v) = dnOp (kron2 p q Z) (fockAct1 p q r s Y v) := by
  have hK : ∀ {d : ℕ} {w : Pol p q r s}, w ∈ homog (Ln p q r s) d →
      fockAct1 p q r s Y w ∈ homog (Ln p q r s) d := fun hw =>
    GlobalTheory.FockDeg.omAct_mem_homog (GlobalTheory.FockDeg.lineMatrixKroneckerLeftFactor_eq_zero_of_isKC hY) hw
  have hc := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute p q r s).2.2 Y Z) v
  rw [Module.End.mul_apply, Module.End.mul_apply, fockAct2_eq, omAct_odd (odd_kron2 hZ),
    LinearMap.add_apply, LinearMap.add_apply, map_add] at hc
  have h1 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∈
      homog (Ln p q r s) (d + 2) :=
    Submodule.sub_mem _ (hK (upOp_homog _ d v hv)) (upOp_homog _ d _ (hK hv))
  have h2 : dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) ∈
      homog (Ln p q r s) (d - 2) :=
    Submodule.sub_mem _ (dnOp_homog _ d _ (hK hv)) (hK (dnOp_homog _ d v hv))
  have e : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) =
      dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) := by
    linear_combination hc
  have h0 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) -
      upOp (kron2 p q Z) (fockAct1 p q r s Y v) = 0 := by
    by_contra hne
    have := IsHomogeneous.inj_right h1 (e ▸ h2) hne
    omega
  exact ⟨sub_eq_zero.1 h0, (sub_eq_zero.1 (e ▸ h0)).symm⟩

theorem upOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    upOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).1, hc Y hY, map_smul]

theorem dnOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    dnOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).2, hc Y hY, map_smul]

theorem eq_zero_of_lowering {x : ℚ} {e e₀ : ℕ} {g v : Pol p q r s} (hg0 : g ≠ 0)
    (hg : g ∈ homog (Ln p q r s) e₀) (hgc : g ∈ charSub p q r s x) (he : e₀ < e)
    (hv : v ∈ homog (Ln p q r s) e) (hvc : v ∈ charSub p q r s x)
    (hd : ∀ Z : Mat r s, IsPC Z → dnOp (kron2 p q Z) v = 0) : v = 0 := by
  by_contra h0
  have h1 := isSide_one.degW_le Function.bijective_id hg (isHW_of_mem hg0 hgc)
  obtain ⟨d, hd1, hd2⟩ := isSide_one.homog_of_hw Function.bijective_id (isHW_of_mem h0 hvc)
    ((mem_harm1 v).1 fun Z hZ => by
      rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) v).2, hd Z hZ])
  obtain rfl : d = e := IsHomogeneous.inj_right hd2 hv h0
  rw [← hd1, Nat.cast_le] at h1
  omega

theorem mem_span_raising : ∀ (P Q R S : ℕ) (x : ℚ) (e e₀ : ℕ) (f g : Pol P Q R S),
    f ∈ homog (Ln P Q R S) e →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y f = ((x : ℂ) * Y.trace) • f) →
    g ≠ 0 → g ∈ homog (Ln P Q R S) e₀ →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g = ((x : ℂ) * Y.trace) • g) →
    e₀ < e →
    f ∈ Submodule.span ℂ {f' | ∃ Z : Mat R S, IsPC Z ∧
      ∃ g' ∈ homog (Ln P Q R S) (e - 2),
        (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 P Q R S Z) g'} := by
  intro p q r s x e e₀ f g hf hfc hg0 hg hgc he
  by_cases h2 : e < 2
  · rw [eq_zero_of_lowering hg0 hg hgc he hf hfc fun Z _ => dnOp_low _ e h2 f hf]
    exact Submodule.zero_mem _
  have hι := GlobalTheory.FockAlg.Model.isFockIsometry_fockEmb (Ln p q r s)
  have hinj := injective_of_isFockIP hι
  set U := Submodule.span ℂ {f' | ∃ Z : Mat r s, IsPC Z ∧
      ∃ g' ∈ homog (Ln p q r s) (e - 2),
        (∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 p q r s Z) g'} with hU
  have hle : U ≤ homog (Ln p q r s) e ⊓ charSub p q r s x := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, hZ, g', h1, h3, rfl⟩
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) g').1]
    refine ⟨?_, upOp_mem_charSub hZ h1 h3⟩
    have := upOp_homog (kron2 p q Z) _ g' h1
    rwa [show e - 2 + 2 = e by omega] at this
  have := Submodule.finiteDimensional_of_le (hle.trans inf_le_left)
  obtain ⟨u, hu, ho⟩ := exists_orth (GlobalTheory.FockAlg.Model.fockEmb (Ln p q r s)) U f
  have hh := Submodule.sub_mem _ hf (hle hu).1
  have hc : f - u ∈ charSub p q r s x := Submodule.sub_mem _ hfc (hle hu).2
  have h0 : f - u = 0 := eq_zero_of_lowering hg0 hg hgc he hh hc fun Z hZ => by
    have hZ' := isPC_conjTranspose hZ
    have h1 := ho _ (Submodule.subset_span ⟨_, hZ', _, dnOp_homog (kron2 p q Z) e _ hh,
      dnOp_mem_charSub hZ hh hc, rfl⟩)
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ') _).1, inner_upOp hι (odd_kron2 hZ'),
      ← lineKroneckerRightMatrix_conjTranspose, neg_eq_zero, inner_self_eq_zero] at h1
    exact hinj (h1.trans (map_zero _).symm)
  rw [sub_eq_zero.1 h0]
  exact hu

end GlobalTheory.FockScalarType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightLeSpanSupFockCoinvariants
noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.HoweR.MultOne

variable {P Q R S : ℕ}

theorem coinv_stable2 (x : ℂ) (Y : Mat R S) {v : Pol P Q R S} (hv : v ∈ coinv P Q R S x) :
    fockAct2 P Q R S Y v ∈ coinv P Q R S x := by
  induction hv using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Y f, ?_⟩
    rw [map_sub, map_smul, GlobalTheory.FockAlg.MinFirst.fockAct1_fockAct2_commute]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

theorem fockHarmonicsSecondMember_of_jointShape_highestWeight {x : ℚ} {μ' : Ix R S → ℚ} (hJ : JointShape P Q R S (fun _ => x) μ') {f : Pol P Q R S}
    (h2 : f ∈ harm2 P Q R S) (hc : f ∈ GlobalTheory.FockScalarType.charSub P Q R S x)
    (hw : f ∈ hwSub (fockAct2 P Q R S) μ') : f ∈ harm1 P Q R S := by
  by_cases h0 : f = 0
  · subst h0; intro Z _; simp [minusPart]
  obtain ⟨d, hd, hdf⟩ := isSide_two.homog_of_hw Prod.swap_bijective ⟨h0, hw⟩ ((mem_harm2 f).1 h2)
  have hdeg := (GlobalTheory.JointShapeUniq.jointShape_unique_deg P Q R S _ _ _ _ hJ hJ).2
  intro Z hZ
  rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) f).2]
  by_cases hd2 : d < 2
  · exact dnOp_low _ d hd2 f hdf
  by_contra hne
  have h1 := isSide_one.degW_le Function.bijective_id (dnOp_homog _ d f hdf)
    (GlobalTheory.FockScalarType.isHW_of_mem hne (GlobalTheory.FockScalarType.dnOp_mem_charSub hZ hdf hc))
  rw [hdeg, ← hd] at h1
  have e : ((d - 2 : ℕ) : ℚ) = (d : ℚ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ d)]; ring
  rw [e] at h1
  linarith

end GlobalTheory.HoweR.MultOne

namespace GlobalTheory.HoweR


set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.HoweR.MultOne in
theorem hw_le_span_sup_coinv : ∀ (P Q R S : ℕ) (x : ℚ) (μ' : Ix R S → ℚ), JointShape P Q R S (fun _ => x) μ' →
    ∃ f₀ : Formalism.BasicNotions.TH.Pol P Q R S, hwSub (fockAct2 P Q R S) μ' ≤ Submodule.span ℂ {f₀} ⊔ coinv P Q R S (x : ℂ) := by
  intro P Q R S x μ' hJ
  set L := hwSub (fockAct1 P Q R S) (fun _ => x) ⊓ hwSub (fockAct2 P Q R S) μ' ⊓
    Submodule.span ℂ (jointHarm P Q R S) with hL
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 (GlobalTheory.JointHarm.finrank_joint_highest_of_shape P Q R S _ _ hJ)
  refine ⟨v.1, fun g hg => ?_⟩
  set C := coinv P Q R S (x : ℂ) with hC
  let pr := C.mkQ
  have hker : ∀ w, pr w = 0 ↔ w ∈ C := fun w => by rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hpr1 : ∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f := by
    intro X f
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact (hker _).2 (Submodule.subset_span ⟨X, f, rfl⟩)
  have hpr2 : ∀ Y w w', pr w = pr w' → pr (fockAct2 P Q R S Y w) = pr (fockAct2 P Q R S Y w') := by
    intro Y w w' h
    rw [← sub_eq_zero, ← map_sub] at h
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact (hker _).2 (coinv_stable2 _ Y ((hker _).1 h))
  have hPC : ∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0 := by
    intro Z hZ f; rw [hpr1, GlobalTheory.HarmLift.trace_PC hZ, mul_zero, zero_smul]
  obtain ⟨h, hh, hprh⟩ := GlobalTheory.HarmLift.lemA P Q R S _ pr hPC g
  obtain ⟨H0, hfin, hH0, hharm, hs1, hs2⟩ := GlobalTheory.HarmLift.lemB P Q R S h hh
  obtain ⟨ι, hιIP, hιinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)
  let A : Set (Module.End ℂ (Pol P Q R S)) :=
    {a | (∃ X, IsKC X ∧ a = fockAct1 P Q R S X) ∨ ∃ Y, IsKC Y ∧ a = fockAct2 P Q R S Y}
  have hadj := GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hιIP
  obtain ⟨c, hc, hcpr, hceig⟩ := GlobalTheory.HarmLift.lemC (Pol P Q R S) (Pol P Q R S ⧸ C) _ ι hιinj pr H0 hfin A
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w hw
      exacts [hs1 X hX w hw, hs2 Y hY w hw])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) w _ hw
      · rw [hpr1, hw, smul_zero]
      · rw [hpr2 Y w 0 (by rw [hw, map_zero]), map_zero, map_zero])
    (by
      rintro a (⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨_, Or.inl ⟨_, GlobalTheory.HarmLift.isKC_adjZ hX, rfl⟩, hadj.2.1 X⟩
      · exact ⟨_, Or.inr ⟨_, GlobalTheory.HarmLift.isKC_adjZ hY, rfl⟩, hadj.2.2 Y⟩)
    h hH0
  rw [hprh] at hcpr
  have hcc : c ∈ GlobalTheory.FockScalarType.charSub P Q R S x := fun X hX =>
    hceig _ (Or.inl ⟨X, hX, rfl⟩) _ (by rw [hpr1])
  have hcw : c ∈ hwSub (fockAct2 P Q R S) μ' := by
    have hg2 := hg
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hg2 ⊢
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have hs : sameBlock a a := by rcases a with a | a <;> simp [sameBlock]
      refine hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) _ ?_
      rw [hpr2 (Eab a a) c g hcpr, hg2.1 a, map_smul, hcpr]
    · have hs : sameBlock a b := by
        revert hab; rcases a with a | a <;> rcases b with b | b <;> simp [posC, sameBlock]
      rw [hceig _ (Or.inr ⟨_, GlobalTheory.HarmLift.isKC_Eab hs, rfl⟩) 0
        (by rw [hpr2 (Eab a b) c g hcpr, hg2.2 a b hab, map_zero, zero_smul]), zero_smul]
  have hcJ : c ∈ jointHarm P Q R S := ⟨hharm c hc, fockHarmonicsSecondMember_of_jointShape_highestWeight hJ (hharm c hc) hcc hcw⟩
  have hcL : c ∈ L := by
    by_cases h0 : c = 0
    · rw [h0]; exact L.zero_mem
    exact ⟨⟨(GlobalTheory.FockScalarType.isHW_of_mem h0 hcc).2, hcw⟩, Submodule.subset_span hcJ⟩
  obtain ⟨t, ht⟩ := hv ⟨c, hcL⟩
  have hct : c = t • v.1 := by
    have := congrArg Subtype.val ht
    simpa using this.symm
  have hgc : g - c ∈ C := (hker _).1 (by rw [map_sub, hcpr, sub_self])
  rw [← sub_add_cancel g c, add_comm]
  exact Submodule.add_mem_sup (hct ▸ Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)) hgc

end GlobalTheory.HoweR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightLeSpanSupFockCoinvariantsStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeight_le_span_sup_fockCoinvariants : ∀ (P Q R S : ℕ) (x : ℚ) (μ' : Ix R S → ℚ), JointShape P Q R S (fun _ => x) μ' → ∃ f₀ : Formalism.BasicNotions.TH.Pol P Q R S, hwSub (fockAct2 P Q R S) μ' ≤ Submodule.span ℂ {f₀} ⊔ coinv P Q R S (x : ℂ) := by
  first | exact @GlobalTheory.HoweR.hw_le_span_sup_coinv | exact GlobalTheory.HoweR.hw_le_span_sup_coinv | (intros; apply GlobalTheory.HoweR.hw_le_span_sup_coinv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvTopOrRat
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem coinv_top_or_rat (P Q R S : ℕ) (x : ℂ) :
    coinv P Q R S x = ⊤ ∨ ∃ x' : ℚ, coinv P Q R S x = coinv P Q R S (x' : ℂ) := by
  by_cases hx : ∃ x' : ℚ, x = x'
  · obtain ⟨x', rfl⟩ := hx
    exact Or.inr ⟨x', rfl⟩
  push_neg at hx
  by_cases hI : IsEmpty (Ix P Q)
  · right
    refine ⟨0, ?_⟩
    unfold coinv
    congr 1
    ext g
    simp [Matrix.trace, Finset.univ_eq_empty]
  · left
    rw [not_isEmpty_iff] at hI
    obtain ⟨a⟩ := hI
    let K : Subring ℂ := (Rat.castHom ℂ).range
    have hxK : x ∉ K := by
      rintro ⟨q, hq⟩
      exact hx q hq.symm
    have hsign : ∀ c : Ix R S, lineSign a c ∈ K := by
      intro c
      rcases a with a | a <;> rcases c with c | c <;> simp only [lineSign] <;>
        first | exact K.one_mem | exact K.neg_mem K.one_mem
    have hc : ∀ α : Ln P Q R S →₀ ℕ, (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) ∈ K := by
      intro α
      refine K.sum_mem fun c _ => K.mul_mem (hsign c) (K.add_mem (natCast_mem K _) ?_)
      exact RingHom.mem_range.mpr ⟨1 / 2, by simp⟩
    have hmon : ∀ α : Ln P Q R S →₀ ℕ, (MvPolynomial.monomial α (1 : ℂ) : Pol P Q R S) ∈ coinv P Q R S x := by
      intro α
      have hne : (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x ≠ 0 := by
        intro h
        apply hxK
        rw [sub_eq_zero] at h
        rw [← h]
        exact hc α
      have hg : fockAct1 P Q R S (Eab a a) (MvPolynomial.monomial α 1) -
          (x * (Eab a a : Mat P Q).trace) • MvPolynomial.monomial α 1 ∈ coinv P Q R S x :=
        Submodule.subset_span ⟨Eab a a, _, rfl⟩
      have htr : (Eab a a : Mat P Q).trace = 1 := by simp [Eab]
      rw [cartan1, htr, mul_one, ← sub_smul] at hg
      have h2 := (coinv P Q R S x).smul_mem ((∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x)⁻¹ hg
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    rw [eq_top_iff]
    intro f _
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    have he : (MvPolynomial.monomial α (AddMonoidAlgebra.coeff f α) : Pol P Q R S) =
        AddMonoidAlgebra.coeff f α • MvPolynomial.monomial α 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [he]
    exact (coinv P Q R S x).smul_mem _ (hmon α)

end GlobalTheory.HoweR
end

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.Cyc

theorem coinv_eq_rel (P Q R S : ℕ) (x : ℚ) : coinv P Q R S (x : ℂ) = GlobalTheory.FockQuot.rel P Q R S x := rfl

theorem fockAct2_good (P Q R S : ℕ) : Good (fockAct2 P Q R S) :=
  ⟨(fock_lie_and_commute P Q R S).2.2.1, fun v => ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v).2,
    GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩

theorem rel_stab (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (y : Pol P Q R S) (hy : y ∈ GlobalTheory.FockQuot.rel P Q R S x) :
    fockAct2 P Q R S Y y ∈ GlobalTheory.FockQuot.rel P Q R S x := by
  have h := GlobalTheory.FockQuot.fockTraceCharacterRelations_le_comap_secondAction P Q R S x 0 Y hy
  rw [Submodule.mem_comap, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply] at h
  simpa using h

theorem actQ_zero_mk (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (fockAct2 P Q R S Y f) := by
  rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; simp

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (T : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act T) : act Z y ∈ genSub act T := by
  unfold genSub at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  intro N hN
  exact hN.2 Z y (hy N hN)

theorem mem_genSub_self {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (v : V) : v ∈ genSub act {v} := by
  unfold genSub
  rw [Submodule.mem_sInf]
  intro N hN
  exact hN.1 rfl

theorem cycMod_rel (P Q R S : ℕ) (x : ℚ) (hne : GlobalTheory.FockQuot.rel P Q R S x ≠ ⊤) :
    CycMod (fockAct2 P Q R S) (GlobalTheory.FockQuot.rel P Q R S x) := by
  set C := GlobalTheory.FockQuot.rel P Q R S x with hC
  have hnt : Nontrivial (GlobalTheory.FockQuot.gkQ P Q R S x 0).V := by
    show Nontrivial (Pol P Q R S ⧸ C)
    exact Submodule.Quotient.nontrivial_iff.2 hne
  have hlift : IsLift x 0 (GlobalTheory.FockQuot.gkQ P Q R S x 0) C.mkQ := by
    refine ⟨Submodule.mkQ_surjective _, fun X f => GlobalTheory.FockQuot.mk_fockFirstAction_eq_trace_smul P Q R S x X f, fun Y f => ?_⟩
    show GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) = _
    rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; rfl
  obtain ⟨μ', hJ, w, ⟨hw0, hwhw⟩, hgen⟩ :=
    GlobalTheory.RealLift.GenLift.genBy_of_isLift P Q R S x 0 _ _ hlift hnt
  change w ∈ hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) _ at hwhw
  change genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {w} = ⊤ at hgen
  obtain ⟨f₁, rfl⟩ := Submodule.Quotient.mk_surjective C w
  change (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ≠ 0 at hw0
  have hwhw' : (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ∈
      hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) (fun c => μ' c + 0) := hwhw
  obtain ⟨hwt0, hpos0⟩ := Submodule.mem_inf.1 hwhw'
  have hwt : ∀ c, GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c c) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) =
      (((μ' c + 0 : ℚ)) : ℂ) • (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) := fun c => by
    unfold wtSub at hwt0
    have h := (Submodule.mem_iInf _).1 hwt0 c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    simpa using h
  have hpos : ∀ c d, posC c d →
      GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c d) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) = 0 := fun c d hcd => by
    have h := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hpos0 c) d) hcd
    exact h
  have hKC : KStable (fockAct2 P Q R S) C := fun X _ y hy => rel_stab P Q R S x X y hy
  have hKT : KStable (fockAct2 P Q R S) (⊤ : Submodule ℂ (Pol P Q R S)) := fun _ _ _ _ => Submodule.mem_top
  have h1 : ∀ c, fockAct2 P Q R S (Eab c c) f₁ - ((μ' c : ℚ) : ℂ) • f₁ ∈ C := by
    intro c
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← actQ_zero_mk, hwt c]
    simp
  have h2 : ∀ c d, posC c d → fockAct2 P Q R S (Eab c d) f₁ ∈ C := by
    intro c d hcd
    rw [← Submodule.Quotient.mk_eq_zero, ← actQ_zero_mk]
    exact hpos c d hcd
  obtain ⟨v, -, hv, hfv⟩ :=
    GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace R S (Pol P Q R S) (fockAct2 P Q R S) (fockAct2_good P Q R S) C ⊤ hKC hKT μ' f₁
      Submodule.mem_top h1 h2
  have hmk : (Submodule.Quotient.mk v : Pol P Q R S ⧸ C) = Submodule.Quotient.mk f₁ :=
    ((Submodule.Quotient.eq C).2 hfv).symm
  refine ⟨μ', v, hv, ?_, ?_⟩
  ·
    set N := genSub (fockAct2 P Q R S) {v} ⊔ C with hN
    have hNst : ∀ Z, ∀ y ∈ N, fockAct2 P Q R S Z y ∈ N := by
      intro Z y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add (f := _)]
      exact N.add_mem (Submodule.mem_sup_left (genSub_stable _ _ Z a ha))
        (Submodule.mem_sup_right (rel_stab P Q R S x Z b hb))
    have hle : genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {Submodule.Quotient.mk f₁} ≤ N.map C.mkQ := by
      refine sInf_le ⟨?_, ?_⟩
      · rw [Set.singleton_subset_iff, ← hmk]
        exact ⟨v, Submodule.mem_sup_left (mem_genSub_self _ v), rfl⟩
      · rintro Z _ ⟨n, hn, rfl⟩
        refine ⟨fockAct2 P Q R S Z n, hNst Z n hn, ?_⟩
        simp only [Submodule.mkQ_apply]
        rw [actQ_zero_mk]
    have hle2 : N.map C.mkQ = ⊤ := top_le_iff.1 (le_trans (le_of_eq hgen.symm) hle)
    rw [eq_top_iff]
    intro f _
    have hf : Submodule.Quotient.mk f ∈ N.map C.mkQ := by rw [hle2]; exact Submodule.mem_top
    obtain ⟨n, hn, hnf⟩ := hf
    have hd : n - f ∈ C := (Submodule.Quotient.eq C).1 hnf
    have : f = n - (n - f) := by abel
    rw [this]
    exact N.sub_mem hn (Submodule.mem_sup_right hd)
  ·
    obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.highestWeight_le_span_sup_fockCoinvariants P Q R S x μ' hJ
    rw [coinv_eq_rel] at hf₀
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.1 (hf₀ hv)
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz : z ≠ 0 := by
      rintro rfl
      apply hw0
      rw [← hmk, Submodule.Quotient.mk_eq_zero, ← hyc]
      simpa using hc
    have hf₀mem : f₀ ∈ Submodule.span ℂ {v} ⊔ C := by
      have : f₀ = z⁻¹ • v - z⁻¹ • c := by
        rw [← hyc, smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
        (Submodule.mem_sup_right (C.smul_mem _ hc))
    refine hf₀.trans (sup_le ?_ le_sup_right)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hf₀mem

end GlobalTheory.HoweR.Cyc

theorem GlobalTheory.HoweR.coinv_cycMod : ∀ (P Q R S : ℕ) (x : ℂ), CycMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  rcases GlobalTheory.HoweR.coinv_top_or_rat P Q R S x with h | ⟨x', h⟩
  · rw [h]
    refine ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
  · rw [h, GlobalTheory.HoweR.Cyc.coinv_eq_rel] at *
    by_cases hne : GlobalTheory.FockQuot.rel P Q R S x' = ⊤
    · rw [hne]
      exact ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
    · exact GlobalTheory.HoweR.Cyc.cycMod_rel P Q R S x' hne
end
end

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoinvariants_highestWeightCyclic_multiplicityOne : ∀ (P Q R S : ℕ) (x : ℂ), CycMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  first | exact @GlobalTheory.HoweR.coinv_cycMod | exact GlobalTheory.HoweR.coinv_cycMod | (intros; apply GlobalTheory.HoweR.coinv_cycMod <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariants
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.SecondQuad

section Ring

variable {A : Type} [Ring A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (u l : I × J → A)

theorem left_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) =
      ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  have h1 : ∀ d a b, u (a, c) * l (a, d) * (u (b, d) * l (b, e)) =
      u (a, c) * u (b, d) * (l (a, d) * l (b, e)) + if a = b then u (a, c) * l (a, e) else 0 := by
    intro d a b
    have h := hlu (a, d) (b, d)
    simp only [Prod.mk.injEq, and_true] at h
    have : u (a, c) * l (a, d) * (u (b, d) * l (b, e)) = u (a, c) * (l (a, d) * u (b, d)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hab : a = b
    · subst hab; simp [mul_add, add_mul, mul_assoc]
    · simp [hab, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul_sum, h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem right_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) +
        Fintype.card I • ∑ b, u (b, c) * l (b, e) := by
  have h1 : ∀ a b d, u (b, d) * l (a, d) * (u (a, c) * l (b, e)) =
      u (b, d) * u (a, c) * (l (a, d) * l (b, e)) + if d = c then u (b, c) * l (b, e) else 0 := by
    intro a b d
    have h := hlu (a, d) (a, c)
    simp only [Prod.mk.injEq, true_and] at h
    have : u (b, d) * l (a, d) * (u (a, c) * l (b, e)) = u (b, d) * (l (a, d) * u (a, c)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hdc : d = c
    · subst hdc; simp [mul_add, add_mul, mul_assoc]
    · simp [hdc, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul, h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem key (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0)
    (huu : ∀ i j, u i * u j = u j * u i) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) + Fintype.card I • ∑ a, u (a, c) * l (a, e) =
      ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  rw [left_expand u l hlu, right_expand u l hlu]
  have hT : ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [huu]
  rw [hT]
  abel

end Ring

variable {P Q R S : ℕ}

theorem raiB_comm (l m : Ln P Q R S) : raiB l * raiB m = raiB m * raiB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun f => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [raiB, hl, hm, MvPolynomial.pderiv_X, Pi.single_apply, hlm, Ne.symm hlm,
      GlobalTheory.FockCasimir.pderiv_pderiv_comm l m, mul_left_comm]

theorem fockSecondAction_matrixUnit_eq (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) = ∑ a, raiB (a, c) * lowB (a, d) +
      if c = d then ((Fintype.card (Ix P Q) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct2_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, true_and]
  by_cases hcd : c = d
  · simp [hcd, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hcd]

theorem fockFirstAction_matrixUnit_eq (b a : Ix P Q) :
    fockAct1 P Q R S (Eab b a) = ∑ d, raiB (b, d) * lowB (a, d) +
      if b = a then ((Fintype.card (Ix R S) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct1_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, and_true]
  by_cases hba : b = a
  · simp [hba, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hba]

theorem trace_Eab (b a : Ix P Q) : (Eab b a).trace = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h; simp [Eab, Matrix.trace, Matrix.single_apply]
  · simp [Eab, Matrix.trace, Matrix.single_apply, h]

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem sq_shift (X : J → J → A) (k : ℂ) (c e : J) :
    ∑ d, (X c d + if c = d then k • (1 : A) else 0) * (X d e + if d = e then k • (1 : A) else 0) =
      ∑ d, X c d * X d e + (2 * k) • X c e + if c = e then (k * k) • (1 : A) else 0 := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
    smul_mul_assoc, one_mul, mul_smul_comm, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, smul_smul]
  by_cases hce : c = e
  · subst hce; simp only [if_true]; module
  · simp only [hce, if_false]; module

theorem rhs_shift (E : I → I → A) (Y : I → I → A) (m x : ℂ) :
    ∑ a, ∑ b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      ∑ a, ∑ b, E b a * Y a b + (m - x) • ∑ a, Y a a := by
  have : ∀ a b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      E b a * Y a b + if b = a then (m - x) • Y a b else 0 := by
    intro a b
    by_cases h : b = a
    · simp only [h, if_true, mul_one, sub_mul, add_mul, smul_mul_assoc, one_mul, sub_smul]; abel
    · simp [h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]

end Alg

variable {P Q R S : ℕ}

theorem qop_eq (x : ℂ) (c e : Ix R S) :
    qop (units (fockAct2 P Q R S)) (x + (Fintype.card (Ix R S) : ℂ) / 2)
        ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2)) c e =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab b a) - (x * (Eab b a).trace) • (1 : Module.End ℂ (Pol P Q R S))) *
        (raiB (a, c) * lowB (b, e)) := by
  have hk := key (fun i : Ln P Q R S => raiB i) (fun i => lowB i) GlobalTheory.FockCasimir.lowB_mul_raiB raiB_comm c e
  simp only [← Nat.cast_smul_eq_nsmul ℂ] at hk
  simp only [qop, units, fockSecondAction_matrixUnit_eq, fockFirstAction_matrixUnit_eq, trace_Eab]
  have hs := sq_shift (A := Module.End ℂ (Pol P Q R S)) (fun c d => ∑ a, raiB (a, c) * lowB (a, d))
    ((Fintype.card (Ix P Q) : ℂ) / 2) c e
  have hr := rhs_shift (A := Module.End ℂ (Pol P Q R S)) (fun b a => ∑ d, raiB (b, d) * lowB (a, d))
    (fun a b => raiB (a, c) * lowB (b, e)) ((Fintype.card (Ix R S) : ℂ) / 2) x
  rw [hs, hr]
  by_cases hce : c = e
  · subst hce; simp only [if_true]
    linear_combination (norm := module) hk
  · simp only [hce, if_false]
    linear_combination (norm := module) hk

theorem qop_mem_coinv (P Q R S : ℕ) (x : ℂ) :
    ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  refine ⟨x + (Fintype.card (Ix R S) : ℂ) / 2,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2),
    fun c e f => ?_⟩
  rw [qop_eq x c e, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  refine Submodule.subset_span ⟨Eab b a, (raiB (a, c) * lowB (b, e)) f, ?_⟩
  simp [Module.End.mul_apply, LinearMap.sub_apply]

end GlobalTheory.HoweR.SecondQuad

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariantsStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | exact GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | (intros; apply GlobalTheory.HoweR.SecondQuad.qop_mem_coinv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.QuadT

section Abstract

variable {A ι κ : Type} [Ring A] [Algebra ℂ A] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (u l : ι → κ → A)

theorem core_term (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (a b : ι) (i j k : κ) :
    u a k * l a i * (u b j * l b k) =
      u a k * l b k * (l a i * u b j) - if k = j then u a k * l a i else 0 := by
  have e1 : u b j * l b k = l b k * u b j - if k = j then 1 else 0 := by
    rw [h b k j]; abel
  have e2 : u a k * l a i * (l b k * u b j) = u a k * l b k * (l a i * u b j) := by
    calc _ = u a k * (l a i * l b k) * u b j := by simp only [mul_assoc]
      _ = u a k * (l b k * l a i) * u b j := by rw [hll]
      _ = _ := by simp only [mul_assoc]
  rw [e1, mul_sub, e2]
  split_ifs <;> simp

theorem core1 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (i j : κ) :
    ∑ k, (∑ a, u a k * l a i) * (∑ b, u b j * l b k) =
      (∑ a, ∑ b, (∑ k, u a k * l b k) * (l a i * u b j)) -
        (Fintype.card ι : ℂ) • ∑ a, u a j * l a i := by
  simp only [Finset.sum_mul, Finset.mul_sum, core_term u l h hll, Finset.sum_sub_distrib]
  congr 1
  · calc (∑ k, ∑ b, ∑ a, u a k * l b k * (l a i * u b j))
          = ∑ b, ∑ k, ∑ a, u a k * l b k * (l a i * u b j) := Finset.sum_comm
        _ = ∑ b, ∑ a, ∑ k, u a k * l b k * (l a i * u b j) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum]

theorem core2 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0) (i j : κ) :
    ∑ a, l a i * u a j = ∑ a, u a j * l a i + if i = j then (Fintype.card ι : ℂ) • (1 : A) else 0 := by
  simp only [h, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

end Abstract

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

section Main

variable {V ι κ : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] (u l : ι → κ → Module.End ℂ V) (E : ι → ι → Module.End ℂ V) (G : κ → κ → Module.End ℂ V)

theorem quad_main (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c)
    (hE : ∀ a b, E a b = ∑ c, u a c * l b c + (if a = b then (Fintype.card κ : ℂ) / 2 else 0) • 1)
    (hG : ∀ c d, G c d = ∑ a, u a c * l a d + (if c = d then (Fintype.card ι : ℂ) / 2 else 0) • 1)
    (x : ℂ) (i j : κ) :
    qop (fun c d => -G d c) ((Fintype.card κ : ℂ) / 2 - x)
        ((Fintype.card ι : ℂ) ^ 2 / 4 + (x - (Fintype.card κ : ℂ) / 2) * (Fintype.card ι : ℂ) / 2) i j =
      ∑ a, ∑ b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) := by
  have hR : ∀ a b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) =
      (∑ c, u a c * l b c) * (l a i * u b j) +
        (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) := by
    intro a b
    rw [hE]
    split_ifs <;> simp [add_mul, sub_mul, sub_smul, smul_mul_assoc, add_sub_assoc]
  simp only [hR, Finset.sum_add_distrib]
  have hD : ∑ a, ∑ b, (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) =
      ((Fintype.card κ : ℂ) / 2 - x) • ∑ a, l a i * u a j := by
    simp [ite_smul, Finset.sum_ite_eq, Finset.smul_sum]
  have h1 := core1 u l h hll i j
  rw [eq_sub_iff_add_eq] at h1
  rw [hD, core2 u l h, ← h1]
  simp only [qop, hG]
  simp only [neg_mul_neg, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, Finset.sum_add_distrib, ite_smul, zero_smul, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    module
  · simp only [hij, Ne.symm hij, if_false]
    module

end Main

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

theorem fockAct1_Eab_eq {P Q R S : ℕ} (a b : Ix P Q) :
    fockAct1 P Q R S (Eab a b) =
      ∑ c, raiB (a, c) * lowB (b, c) + (if a = b then (Fintype.card (Ix R S) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct1_Eab]
  simp only [omE, Prod.mk.injEq, and_true, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem fockAct2_Eab_eq {P Q R S : ℕ} (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) =
      ∑ a, raiB (a, c) * lowB (a, d) + (if c = d then (Fintype.card (Ix P Q) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct2_Eab]
  simp only [omE, Prod.mk.injEq, true_and, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem negT_fockAct2_quad : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f,
    qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  intro P Q R S x
  refine ⟨(Fintype.card (Ix R S) : ℂ) / 2 - x,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 + (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2,
    fun i j f => ?_⟩
  have key : qop (negT (units (fockAct2 P Q R S))) ((Fintype.card (Ix R S) : ℂ) / 2 - x)
      ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 +
        (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2) i j =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab a b) - (if a = b then x else 0) • 1) *
        (lowB (a, i) * raiB (b, j)) :=
    quad_main (fun (a : Ix P Q) (c : Ix R S) => raiB (a, c)) (fun a c => lowB (a, c))
      (fun a b => fockAct1 P Q R S (Eab a b)) (fun c d => fockAct2 P Q R S (Eab c d))
      (fun b c e => by simp [GlobalTheory.FockCasimir.lowB_mul_raiB])
      (fun a c b e => GlobalTheory.FockCasimir.lowB_comm _ _) fockAct1_Eab_eq fockAct2_Eab_eq x i j
  rw [key, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [Module.End.mul_apply]
  apply Submodule.subset_span
  refine ⟨Eab a b, (lowB (a, i) * raiB (b, j)) f, ?_⟩
  by_cases hab : a = b
  · subst hab
    simp [Eab, Matrix.trace_single_eq_same]
  · simp [hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab]

end GlobalTheory.HoweR.QuadT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvariStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | exact GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | (intros; apply GlobalTheory.HoweR.QuadT.negT_fockAct2_quad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomials
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_pack : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  obtain ⟨-, hLie, -, hWt, -⟩ := GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S
  obtain ⟨hStab, hAdm⟩ := GlobalTheory.T.fockCoinvariantKernel_stable_and_admissible P Q R S x
  obtain ⟨α, β, hq⟩ := GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants P Q R S x
  obtain ⟨α', β', hqt⟩ := GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants P Q R S x
  refine ⟨⟨hLie, hWt, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩, hStab, ⟨α, β, α', β', fun a b v _ => ⟨hq a b v, hqt a b v⟩⟩, hAdm, GlobalTheory.T.fockCoinvariants_highestWeightCyclic_multiplicityOne P Q R S x⟩

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomialsStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeQuotientFiniteLength_fockPolynomials : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  first | exact @GlobalTheory.HoweR.fock_pack | exact GlobalTheory.HoweR.fock_pack | (intros; apply GlobalTheory.HoweR.fock_pack <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityCharactersFockTensorProduct
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory
theorem howeAlg_fock_tensor : ∀ (T : Type) [Fintype T] [DecidableEq T] (P Q R S : T → ℕ) (x : T → ℂ), HoweAlg (fun w => actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (tensAny fun w => coinv (P w) (Q w) (R w) (S w) (x w)) := by
  intro T _ _ P Q R S x
  exact GlobalTheory.T.howe_finite_length_tensor_product_factors T (fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) _ _ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) (fun w => coinv (P w) (Q w) (R w) (S w) (x w)) (fun w => GlobalTheory.T.howeQuotientFiniteLength_fockPolynomials (P w) (Q w) (R w) (S w) (x w))
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityCharactersFockTensorProductStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howe_duality_characters_fock_tensor_product : ∀ (T : Type) [Fintype T] [DecidableEq T] (P Q R S : T → ℕ) (x : T → ℂ), HoweAlg (fun w => actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (tensAny fun w => coinv (P w) (Q w) (R w) (S w) (x w)) := by
  first | exact @GlobalTheory.howeAlg_fock_tensor | exact GlobalTheory.howeAlg_fock_tensor | (intros; apply GlobalTheory.howeAlg_fock_tensor <;> assumption)
end

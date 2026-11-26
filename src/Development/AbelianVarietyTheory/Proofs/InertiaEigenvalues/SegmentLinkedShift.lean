module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentLinkedShift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentLinkedShift
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.SmGL.Segment

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_carrier_nu {Δ : Segment k} {s : ℂ} {x : IrrGL (k := k)} :
    x ∈ (Δ.nu s).carrier ↔ ∃ a : ℕ, a < Δ.len ∧ Δ.first.nu (s + a) = x := by
  rw [mem_carrier]
  show (∃ a : ℕ, a < Δ.len ∧ (Δ.first.nu s).nu a = x) ↔ _
  simp only [IrrGL.nu_nu]

theorem linked_nu_nu_sub_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ) :
    (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ)) := by
  have hd : 0 < Δ.first.1 := Δ.isCusp_first.1
  have inj : ∀ r s : ℝ, Δ.first.nu (r : ℂ) = Δ.first.nu (s : ℂ) → r = s :=
    fun r s h => (IrrGL.nu_ofReal_inj hd).1 h
  refine ⟨⟨ofFirst (Δ.first.nu ((t - 1 : ℝ) : ℂ)) (Δ.isCusp_first.nu _) (Δ.len + 1) (Nat.succ_pos _), ?_⟩, ?_, ?_⟩
  · ext x
    rw [Set.mem_union, mem_carrier_nu, mem_carrier_nu, mem_carrier]
    simp only [first_ofFirst, len_ofFirst, IrrGL.nu_nu]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | h
      · exact Or.inr ⟨a, h, rfl⟩
      · refine Or.inl ⟨a - 1, by have := Δ.len_pos; omega, ?_⟩
        congr 1
        have h1 : ((a - 1 : ℕ) : ℂ) = (a : ℂ) - 1 := by
          rw [Nat.cast_sub (by have := Δ.len_pos; omega)]; simp
        rw [h1]; push_cast; ring
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · refine ⟨a + 1, by omega, ?_⟩
        congr 1; push_cast; ring
      · exact ⟨a, by omega, rfl⟩
  · intro hsub
    have hm : Δ.first.nu ((t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ)) ∈ (Δ.nu (t : ℂ)).carrier :=
      mem_carrier_nu.2 ⟨Δ.len - 1, by have := Δ.len_pos; omega, rfl⟩
    obtain ⟨a, ha, he⟩ := mem_carrier_nu.1 (hsub hm)
    have e1 : ((t - 1 : ℝ) : ℂ) + (a : ℂ) = ((t - 1 + a : ℝ) : ℂ) := by push_cast; ring
    have e2 : (t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ) = ((t + ((Δ.len - 1 : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2] at he
    have h3 := inj _ _ he
    have h4 : (a : ℝ) = ((Δ.len - 1 : ℕ) : ℝ) + 1 := by linarith
    have h5 : a = Δ.len - 1 + 1 := by exact_mod_cast h4
    have := Δ.len_pos
    omega
  · intro hsub
    have hm : Δ.first.nu (((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ)) ∈ (Δ.nu ((t - 1 : ℝ) : ℂ)).carrier :=
      mem_carrier_nu.2 ⟨0, Δ.len_pos, rfl⟩
    obtain ⟨a, ha, he⟩ := mem_carrier_nu.1 (hsub hm)
    have e1 : (t : ℂ) + (a : ℂ) = ((t + a : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ) = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2] at he
    have h3 := inj _ _ he
    have h4 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith

end GlobalTheory.SmGL.Segment
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentLinkedShiftStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_linked_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ), (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one | exact GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one | (intros; apply GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompat
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WDListLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpZero (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (WD.lpZero (h := h)).lpTwist ξ hξ = WD.lpZero (h := h) := by
  rw [WD.lpZero, WD.lpTwist_mk]
  exact WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩

theorem lpTwist_lpSum (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpSum_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpSum_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  rfl

theorem lpTwist_lpChar (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpChar_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpChar_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  simp only [WDRep.tensor_ρ, WDRep.twist_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left,
    LinearMap.smul_apply]

theorem lpChar_lpZero (x : WD h) : x.lpChar (WD.lpZero (h := h)) = WD.lpZero (h := h) := by
  induction x using WD.ind with
  | hP n a =>
  rw [WD.lpZero, WD.lpChar_mk]
  exact WD.sound ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem lpChar_lpSum (x a b : WD h) : x.lpChar (a.lpSum b) = (x.lpChar a).lpSum (x.lpChar b) := by
  induction x using WD.ind with
  | hP n c =>
  induction a using WD.ind with
  | hP m a =>
  induction b using WD.ind with
  | hP k b =>
  rw [WD.lpSum_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpSum_mk]
  refine WD.sound ⟨TensorProduct.prodRight ℂ ℂ _ _ _, fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
  · induction v using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero (WD.charPol_monic _ σ)
    ((WD.charPol_natDegree _ σ).trans (WD.lpDim_zero h))

end GlobalTheory.WDListLaws


open GlobalTheory.WDListLaws in
open GlobalTheory.LocLanglands (sumList) in
theorem GlobalTheory.sumList_laws : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  intro E Ω _ _ _ _ _ A w h
  refine ⟨fun l l' hp => ?_, fun l ξ hξ => ?_, fun x y ξ hξ => ⟨lpTwist_lpSum x y ξ hξ, lpTwist_lpChar x y ξ hξ⟩,
    fun x l => ?_, fun l => ⟨?_, fun σ => ?_⟩⟩
  · induction hp with
    | nil => rfl
    | cons x _ ih =>
      show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)
      rw [ih]
    | swap x y l =>
      show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))
      rw [← WD.lpSum_assoc, WD.lpSum_comm y x, WD.lpSum_assoc]
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · induction l with
    | nil => exact lpTwist_lpZero ξ hξ
    | cons x l ih =>
      show (WD.lpSum x (sumList l)).lpTwist ξ hξ = WD.lpSum _ (sumList _)
      rw [lpTwist_lpSum, ih]
  · induction l with
    | nil => exact lpChar_lpZero x
    | cons y l ih =>
      show x.lpChar (WD.lpSum y (sumList l)) = WD.lpSum _ (sumList _)
      rw [lpChar_lpSum, ih]
  · induction l with
    | nil => exact WD.lpDim_zero h
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).lpDim = _
      rw [WD.lpDim_sum, ih, List.map_cons, List.sum_cons]
  · induction l with
    | nil => exact charPol_lpZero σ
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).charPol σ = _
      rw [WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompatStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_sum_twist_compat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  exact @GlobalTheory.sumList_laws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicModulusSqrtCharRefinedBlocksInStages
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicModulusSqrtCharRefinedBlocksInStages
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem toLex_sigma_lt_iff_same {s : ℕ} {t : Fin s → ℕ} (a : Fin s) (b b' : Fin (t a)) :
    toLex (⟨a, b⟩ : Σ a, Fin (t a)) < toLex ⟨a, b'⟩ ↔ b < b' := by
  show Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨a, b⟩ : Σ a, Fin (t a)) ⟨a, b'⟩ ↔ _
  rw [Sigma.lex_iff]
  simp

theorem toLex_sigma_lt_iff_ne {s : ℕ} {t : Fin s → ℕ} (a a' : Fin s) (b : Fin (t a)) (b' : Fin (t a'))
    (h : a ≠ a') : toLex (⟨a, b⟩ : Σ a, Fin (t a)) < toLex ⟨a', b'⟩ ↔ a < a' := by
  show Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨a, b⟩ : Σ a, Fin (t a)) ⟨a', b'⟩ ↔ _
  rw [Sigma.lex_iff]
  simp [h]

theorem sum_toLex_gt {s : ℕ} {t : Fin s → ℕ} (f : (Σ a, Fin (t a)) → ℤ) (a : Fin s) (b : Fin (t a)) :
    ∑ q, (if toLex (⟨a, b⟩ : Σ a, Fin (t a)) < toLex q then f q else 0) =
      (∑ a' with a < a', ∑ b', f ⟨a', b'⟩) + ∑ b' with b < b', f ⟨a, b'⟩ := by
  rw [Fintype.sum_sigma, Fintype.sum_eq_add_sum_compl a, add_comm]
  congr 1
  · rw [Finset.sum_filter, Fintype.sum_eq_add_sum_compl a, if_neg (lt_irrefl a), zero_add]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    have hne : a ≠ a' := fun h => by simp [h] at ha'
    by_cases hlt : a < a'
    · rw [if_pos hlt]
      exact Finset.sum_congr rfl fun b' _ => by rw [if_pos ((toLex_sigma_lt_iff_ne a a' b b' hne).2 hlt)]
    · rw [if_neg hlt]
      exact Finset.sum_eq_zero fun b' _ => by rw [if_neg (mt (toLex_sigma_lt_iff_ne a a' b b' hne).1 hlt)]
  · rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun b' _ => by simp only [toLex_sigma_lt_iff_same]

theorem sum_toLex_lt {s : ℕ} {t : Fin s → ℕ} (f : (Σ a, Fin (t a)) → ℤ) (a : Fin s) (b : Fin (t a)) :
    ∑ q, (if toLex q < toLex (⟨a, b⟩ : Σ a, Fin (t a)) then f q else 0) =
      (∑ a' with a' < a, ∑ b', f ⟨a', b'⟩) + ∑ b' with b' < b, f ⟨a, b'⟩ := by
  rw [Fintype.sum_sigma, Fintype.sum_eq_add_sum_compl a, add_comm]
  congr 1
  · rw [Finset.sum_filter, Fintype.sum_eq_add_sum_compl a, if_neg (lt_irrefl a), zero_add]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    have hne : a' ≠ a := fun h => by simp [h] at ha'
    by_cases hlt : a' < a
    · rw [if_pos hlt]
      exact Finset.sum_congr rfl fun b' _ => by rw [if_pos ((toLex_sigma_lt_iff_ne a' a b' b hne).2 hlt)]
    · rw [if_neg hlt]
      exact Finset.sum_eq_zero fun b' _ => by rw [if_neg (mt (toLex_sigma_lt_iff_ne a' a b' b hne).1 hlt)]
  · rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun b' _ => by simp only [toLex_sigma_lt_iff_same]

end GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem modExp_flat {s : ℕ} (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (c : Fin (∑ a, t a)) :
    modExp (fun c : Fin (∑ a, t a) => Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) c =
      modExp (fun a => Fin (d a)) (finSigmaFinEquiv.symm c).1 +
        modExp (fun b => Fin (d' (finSigmaFinEquiv.symm c).1 b)) (finSigmaFinEquiv.symm c).2 := by
  have hiff : ∀ x y : Fin (∑ a, t a),
      toLex (finSigmaFinEquiv.symm x : Σ a, Fin (t a)) < toLex (finSigmaFinEquiv.symm y) ↔ x < y :=
    fun x y => (finSigmaFinEquiv_symm_strictMono_lex s t).lt_iff_lt
  have hd : ∀ a, ∑ b, (d' a b : ℤ) = d a := fun a => by
    have := Fintype.card_congr (e' a)
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    exact_mod_cast this
  set F : (Σ a, Fin (t a)) → ℤ := fun q => (d' q.1 q.2 : ℤ) with hF
  have hgt : ∑ c' with c < c', (Fintype.card (Fin (d' (finSigmaFinEquiv.symm c').1 (finSigmaFinEquiv.symm c').2)) : ℤ) =
      ∑ q, if toLex (finSigmaFinEquiv.symm c) < toLex q then F q else 0 := by
    rw [Finset.sum_filter]
    exact Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun c' => by simp only [hiff, hF, Fintype.card_fin]
  have hlt : ∑ c' with c' < c, (Fintype.card (Fin (d' (finSigmaFinEquiv.symm c').1 (finSigmaFinEquiv.symm c').2)) : ℤ) =
      ∑ q, if toLex q < toLex (finSigmaFinEquiv.symm c) then F q else 0 := by
    rw [Finset.sum_filter]
    exact Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun c' => by simp only [hiff, hF, Fintype.card_fin]
  unfold modExp
  rw [hgt, hlt]
  generalize finSigmaFinEquiv.symm c = p
  obtain ⟨a, b⟩ := p
  rw [sum_toLex_gt, sum_toLex_lt]
  simp only [hF, Fintype.card_fin, hd]
  ring

end GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem deltaHalf_flatHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) k) :
    deltaHalf k (fun c : Fin (∑ a, t a) => Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2))
        (flatHom (fun a b => GL (Fin (d' a b)) k) g) =
      deltaHalf k (fun a => Fin (d a)) (relEmbD k e' g) * relDeltaHalfD k (fun a b => Fin (d' a b)) g := by
  rw [deltaHalf_apply, deltaHalf_apply, relDeltaHalfD_apply]
  simp only [relEmbD_apply, det_leviEmb, map_prod, deltaHalf_apply, ← Finset.prod_mul_distrib,
    ← MonoidHom.mul_apply, ← absPow_add]
  rw [← Fintype.prod_sigma (fun p : Σ a, Fin (t a) => absPow k ((modExp (fun a => Fin (d a)) p.1 : ℂ) / 2 +
      (modExp (fun b => Fin (d' p.1 b)) p.2 : ℂ) / 2) (Matrix.GeneralLinearGroup.det (g p.1 p.2))),
    ← Equiv.prod_comp finSigmaFinEquiv.symm]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [flatHom_apply, modExp_flat d t d' e' c]
  congr 2
  push_cast
  ring

end GlobalTheory.JacStages
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicModulusSqrtCharRefinedBlocksInStagesStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicModulusSqrtChar_refinedBlocks_in_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) k),
    deltaHalf k (fun c : Fin (∑ a, t a) => Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2))
        (flatHom (fun a b => GL (Fin (d' a b)) k) g) =
      deltaHalf k (fun a => Fin (d a)) (relEmbD k e' g) * relDeltaHalfD k (fun a b => Fin (d' a b)) g := by
  first | exact @GlobalTheory.JacStages.deltaHalf_flatHom | exact GlobalTheory.JacStages.deltaHalf_flatHom | (intros; apply GlobalTheory.JacStages.deltaHalf_flatHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTraceCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTraceCompletion
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.TraceCompl

theorem le_one_iff_of_mul_eq_one {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (hab : a * b = 1)
    (hb : b ≤ 1) : a ≤ 1 ↔ b = 1 := by
  constructor
  · intro ha
    by_contra hb1
    have hlt : b < 1 := lt_of_le_of_ne hb hb1
    have : (1 : Γ) < 1 := calc
      (1 : Γ) = a * b := hab.symm
      _ ≤ 1 * b := by gcongr
      _ = b := one_mul b
      _ < 1 := hlt
    exact lt_irrefl _ this
  · rintro rfl
    rw [mul_one] at hab
    exact hab.le

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

theorem algebraMap_int_mem (A : ValuationSubring Ω) (x : 𝓞 K) : algebraMap K Ω x ∈ A := by
  have h1 : IsIntegral ℤ (algebraMap K Ω x) := x.2.map (algebraMap K Ω).toIntAlgHom
  have h2 : IsIntegral A (algebraMap K Ω x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact hy ▸ y.2

theorem algebraMap_mem_iff {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    (x : K) : algebraMap K Ω x ∈ A ↔ v.valuation K x ≤ 1 := by
  have key : ∀ n : 𝓞 K, A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 ∧
      v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 ∧
      (A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔
        v.valuation K (algebraMap (𝓞 K) K n) = 1) := by
    intro n
    have h1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 :=
      (A.valuation_le_one_iff _).2 (algebraMap_int_mem A n)
    have h2 : v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 := v.valuation_le_one n
    have h3 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) < 1 ↔ n ∈ v.asIdeal := h n
    have h4 : v.valuation K (algebraMap (𝓞 K) K n) < 1 ↔ n ∈ v.asIdeal := v.valuation_lt_one_iff_mem n
    refine ⟨h1, h2, ?_⟩
    have e1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h3, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h1 e⟩
    have e2 : v.valuation K (algebraMap (𝓞 K) K n) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h4, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h2 e⟩
    exact e1.trans e2.symm
  obtain ⟨n, d, hd | hd⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1, mul_one] at e1 e2
    rw [← A.valuation_le_one_iff, e1, e2]
    exact iff_of_true (key n).1 (key n).2.1
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1] at e1 e2
    rw [← A.valuation_le_one_iff, le_one_iff_of_mul_eq_one e1 (key n).1,
      le_one_iff_of_mul_eq_one e2 (key n).2.1]
    exact (key n).2.2

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem trace_mem {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    (hL : IsLocalExt L h) (z : L) (hz : algebraMap L Ω z ∈ A) :
    algebraMap K Ω (Algebra.trace K L z) ∈ A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  rw [trace_eq_sum_embeddings Ω]
  refine sum_mem fun s _ => ?_
  obtain ⟨τ, hτ⟩ := hL (AlgEquiv.ofBijective (s.liftNormal Ω) (AlgHom.normal_bijective K Ω Ω _))
  have e : s z = (τ : G K Ω) (algebraMap L Ω z) := ((hτ z).trans (s.liftNormal_commutes Ω z)).symm
  rw [e]
  exact (apply_mem_iff_of_mem_Dec (Weil_le_Dec h τ.2) _).2 hz

theorem valuation_trace_le {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hL : IsLocalExt L h)
    {c : K} (hc : c ≠ 0) {z : L} (hz : v'.valuation L z ≤ v'.valuation L (algebraMap K L c)) :
    v.valuation K (Algebra.trace K L z) ≤ v.valuation K c := by
  have hc' : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).2 hc
  have h1 : v'.valuation L (z * (algebraMap K L c)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ hz zero_le'
  have h2 := trace_mem h hL _ ((algebraMap_mem_iff h' _).2 h1)
  rw [algebraMap_mem_iff h, ← map_inv₀, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul,
    map_mul, map_inv₀] at h2
  have hv : v.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  calc v.valuation K (Algebra.trace K L z)
      = (v.valuation K c)⁻¹ * v.valuation K (Algebra.trace K L z) * v.valuation K c := by
        rw [mul_comm _ (v.valuation K c), ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    _ ≤ 1 * v.valuation K c := by gcongr
    _ = v.valuation K c := one_mul _

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

open WithZero

variable (K : Type) {L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def traceMap (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) :
    WithVal (v'.valuation L) →+ v.adicCompletion K :=
  ((algebraMap K (v.adicCompletion K)).toAddMonoidHom.comp (Algebra.trace K L).toAddMonoidHom).comp
    (WithVal.equiv (v'.valuation L)).toAddMonoidHom

variable {K} {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  [IsScalarTower K L Ω]

theorem continuous_traceMap {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hL : IsLocalExt L h) :
    Continuous (traceMap K v v') := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hc0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := (_root_.map_ne_zero _).2 γ.ne_zero
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt hc0
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hp0 : algebraMap (𝓞 K) K (π ^ n) ≠ 0 :=
    (_root_.map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (pow_ne_zero n hπ0)
  have hpv : v.valuation K (algebraMap (𝓞 K) K (π ^ n)) ≤ exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact Ideal.pow_mem_pow hπ n
  have hd : v'.valuation L (algebraMap K L (algebraMap (𝓞 K) K (π ^ n))) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((_root_.map_ne_zero _).2 hp0)
  rw [Filter.mem_map, Valued.mem_nhds_zero]
  refine ⟨Units.mk0 ((Valued.v : Valuation (WithVal (v'.valuation L)) ℤᵐ⁰).restrict
    (WithVal.toVal _ (algebraMap K L (algebraMap (𝓞 K) K (π ^ n))))) ?_, fun z hz => hγ ?_⟩
  · simpa using hd
  · rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    have e : traceMap K v v' z = algebraMap K _ (Algebra.trace K L (WithVal.ofVal z)) := rfl
    rw [e, GlobalTheory.Idele.valued_algebraMap]
    exact (valuation_trace_le h h' hL hp0 hz.le).trans_lt (hpv.trans_lt hn)

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

theorem exists_trace_extension : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), IsLocalExt L h → ∃ T : v'.adicCompletion L →+ v.adicCompletion K, Continuous T ∧ ∀ z : L, T (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' hL
  refine ⟨(AddMonoidHom.extension (traceMap K v v') (continuous_traceMap h h' hL)).comp
    (HeightOneSpectrum.adicCompletion.equiv L v').toAddMonoidHom, ?_, fun z => ?_⟩
  · exact (AddMonoidHom.continuous_extension _ (continuous_traceMap h h' hL)).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v')
  · exact AddMonoidHom.extension_coe _ (continuous_traceMap h h' hL) (WithVal.toVal _ z)

end GlobalTheory.LocLanglands.TraceCompl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTraceCompletionStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_trace_completion : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), IsLocalExt L h → ∃ T : v'.adicCompletion L →+ v.adicCompletion K, Continuous T ∧ ∀ z : L, T (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) := by
  first | exact @GlobalTheory.LocLanglands.TraceCompl.exists_trace_extension | exact GlobalTheory.LocLanglands.TraceCompl.exists_trace_extension | (intros; apply GlobalTheory.LocLanglands.TraceCompl.exists_trace_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorPowEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorPowEqSum
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem htOp_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (C : Core l) (ξ : Ainf l) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (σ : GQ l) (z : ℂ_[l]) (H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), U * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) → IsHT C ξ (fun g => (r g).val.map σ) z u → ∀ n : ℕ, u ^ n = ∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x) := by
  intro l _ K C ξ a d ρ r b e hR σ z H U u hU hu
  have hσz : ∀ c : ℤ_[l], σ (zOm l c) = zOm l c := fun c => by simp [zOm]
  have hθo : ∀ w : Om l, Per.θD l (C.o w) = algebraMap (Om l) ℂ_[l] w := fun w => C.o_sec.th w

  let S : Set (Om l) := Set.range fun t : Fin d × Fin a × Fin a => σ (b t.1 t.2.1 t.2.2)
  haveI : Finite S := (Set.finite_range _).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S, hfd⟩
  have hfix : ∀ g : GQ l, g ∈ GK K' → ∀ i m k, g (σ (b i m k)) = σ (b i m k) := by
    intro g hg i m k
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg _
      (IntermediateField.subset_adjoin _ _ ⟨(i, m, k), rfl⟩)
  let B : Fin a → Matrix (Fin a) (Fin d) ℂ_[l] := fun k m i => algebraMap (Om l) ℂ_[l] (σ (b i m k))
  have hVu : IsUnit (H.V.map (Per.θD l)) := H.unit.map (Per.θD l).mapMatrix
  have col : ∀ k, u * B k * H.V.map (Per.θD l) = B k * U * H.V.map (Per.θD l) := by

    intro k
    ext m j
    let y : Fin a → Per.BdRp l := fun m => ∑ i, C.o (σ (b i m k)) * H.V i j
    let x : Fin a → Per.BdR l := fun m => ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * H.Q i j
    have hy : ∀ m, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * x m = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * y m) := by
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [x, y, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hq := H.Q_eq i j
      calc algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * (algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * H.Q i j)
          = algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * H.Q i j) := by ring
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * H.V i j) := by rw [hq]
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * (C.o (σ (b i m k)) * H.V i j)) := by simp only [map_mul, map_pow]; ring
    have hx : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
        ((r g).val.map σ).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) *ᵥ (fun i => Per.σD (g : GQ l) (x i)) = x := by
      intro g hg
      funext m'
      have hσD : ∀ m, Per.σD (g : GQ l) (x m) = ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * Per.σD (g : GQ l) (H.Q i j) := by
        intro m
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [x, map_sum, map_mul, PrimeEx.sigD_o, hfix _ hg]
      have e1 : ∀ i, ∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) =
          ∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k))) := by
        intro i
        have h1 := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (M m' k)))) (hR.equi g i)
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [Matrix.mul_apply, Matrix.sum_apply, map_sum, map_mul, hσz] using h1
      have e2 : ∀ s, ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * Per.σD (g : GQ l) (H.Q i j) = H.Q s j := by
        intro s
        have h1 := congrFun (congrFun (H.inv g g.2) s) j
        simpa [Matrix.mul_apply] using h1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.comp_apply, hσD]
      calc ∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * Per.σD (g : GQ l) (H.Q i j)
          = ∑ i, (∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k)))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            exact Finset.sum_comm
        _ = ∑ i, (∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k)))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [e1]
        _ = ∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k))) * ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x m' := by simp only [e2, x]
    have h := hu K' (H.p j) H.q x y hx hy
    have hθy : (fun m => Per.θD l (y m)) = fun m => (B k * H.V.map (Per.θD l)) m j := by
      funext m'
      simp only [y, Matrix.mul_apply, Matrix.map_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hθo]
    rw [hθy] at h
    have h2 := congrFun h m
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_assoc u, Matrix.mul_assoc (B k), hU, ← Matrix.mul_assoc (B k), Matrix.mul_diagonal, Matrix.mul_apply, h2, mul_comm]
  have comm : ∀ k, u * B k = B k * U := by
    intro k
    have hd : IsUnit (H.V.map (Per.θD l)).det := (Matrix.isUnit_iff_isUnit_det _).1 hVu
    calc u * B k = u * B k * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by
          rw [Matrix.mul_assoc (u * B k), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      _ = B k * U * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by rw [col k]
      _ = B k * U := by rw [Matrix.mul_assoc (B k * U), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have key : ∀ x : Fin d → ℂ_[l], u * (∑ i, x i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w)) =
      ∑ i, (U *ᵥ x) i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w) := by
    intro x
    ext m k
    have h := congrFun (congrArg (· *ᵥ x) (comm k)) m
    simp only [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, B] at h
    refine (Finset.sum_congr rfl fun x1 _ => ?_).trans (h.trans (Finset.sum_congr rfl fun c _ => ?_))
    · congr 1
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    · simp only [Matrix.mulVec, dotProduct]
      exact mul_comm _ _
  have one : ∑ i, (fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map (fun w => algebraMap (Om l) ℂ_[l] (σ w)) = 1 := by
    ext m k
    have h := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (Om l) ℂ_[l] (σ (M m k))) hR.one
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hσz] at h
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [h]
    by_cases hmk : m = k <;> simp [Matrix.one_apply, hmk]
  intro n
  induction n with
  | zero => simpa using one.symm
  | succ n ih => rw [pow_succ', ih, key, Matrix.mulVec_mulVec, ← pow_succ']

end GlobalTheory.BKLim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorPowEqSumStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateOperator_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (C : Core l) (ξ : Ainf l) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (σ : GQ l) (z : ℂ_[l]) (H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), U * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) → IsHT C ξ (fun g => (r g).val.map σ) z u → ∀ n : ℕ, u ^ n = ∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x) := by
  first | exact @GlobalTheory.BKLim.htOp_pow_eq_sum | exact GlobalTheory.BKLim.htOp_pow_eq_sum | (intros; apply GlobalTheory.BKLim.htOp_pow_eq_sum; all_goals assumption)
end
end

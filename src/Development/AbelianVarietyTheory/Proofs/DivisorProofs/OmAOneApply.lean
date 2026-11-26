module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip
public import Formalism.FormalDegreeBessel.StatementDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil

namespace GlobalTheory.RankFibreKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tw (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : ℂ :=
  (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)

def minor {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : k := (Y.submatrix id J).det

def idx {a d : ℕ} : (Fin a ↪ Fin d) ≃ Fin (Fintype.card (Fin a ↪ Fin d)) := Fintype.equivFin _


variable (k) in
def slice (a d : ℕ) : Set (Matrix (Fin a) (Fin d) k) :=
  {Z | ∃ J : Fin a ↪ Fin d, Z.submatrix id J = 1 ∧ ∀ J' : Fin a ↪ Fin d,
    valuation k (minor Z J') ≤ 1 ∧ (idx J' < idx J → valuation k (minor Z J') < 1)}

def IsFirstMax {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : Prop :=
  minor Y J ≠ 0 ∧ ∀ J' : Fin a ↪ Fin d, valuation k (minor Y J') ≤ valuation k (minor Y J) ∧
    (idx J' < idx J → valuation k (minor Y J') < valuation k (minor Y J))


open Classical in
def sec {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) : GL (Fin a) k := by
  classical
  exact if h : ∃ J, IsFirstMax Y J then
    GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id h.choose) h.choose_spec.1
  else 1

theorem tw_mul (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g x : GL (Fin a) k) : tw ν d (g * x) = tw ν d g * tw ν d x := by
  simp only [tw, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring

theorem tw_ne_zero (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : tw ν d g ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

theorem omA_one_apply (ν β : kˣ →* ℂˣ) {a b : ℕ} (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (Y : Matrix (Fin a) (Fin (a + b)) k) : omA ν β g 1 Ψ Y = (tw ν (a + b) g)⁻¹ * Ψ ((g⁻¹).val * Y) := by
  have e : apow (gdet g) (-(((a + b : ℕ)) : ℂ) / 2) = (apow (gdet g) (((a + b : ℕ) : ℂ) / 2))⁻¹ := by
    rw [neg_div, apow_neg]
  simp only [omA, tw, Fintype.card_fin, e, map_one, Units.val_one, apow_one, mul_one, invT_val, inv_one,
    transpose_one, Units.val_inv_eq_inv_val, mul_inv, Matrix.mul_one]

theorem minor_mul {a d : ℕ} (g : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    minor (g * Y) J = g.det * minor Y J := by
  rw [minor, minor, ← det_mul]
  congr 1

end GlobalTheory.RankFibreKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetMorphismExtendingTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZeroStatement
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jet_extension_square_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C), f₁.deg = f₂.deg → (∀ a, n a ∈ T.J) → (∀ a b, n a * n b = 0) → (∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) → ∃ χ : K.jet k ⟶ T, χ.deg = f₁.deg ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧ ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), χ.φ x = f₁.φ (x.fst : Hol (K.W k)) + ∑ a, f₁.φ (x.snd a : Hol (K.W k)) * n a := by
  first | exact @GlobalTheory.AnPer.Charts.exists_jet_factor | exact GlobalTheory.AnPer.Charts.exists_jet_factor | (intros; apply GlobalTheory.AnPer.Charts.exists_jet_factor <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetMorphismExtendingTranslation
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem tsze_expand_fst_snd {g : ℕ} {O : Type} [CommRing O] (h : O) (v : Fin g → O) :
    (TrivSqZeroExt.inl h + ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) :
        TrivSqZeroExt O (Fin g → O)).fst = h ∧
    ∀ b, (TrivSqZeroExt.inl h + ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) :
        TrivSqZeroExt O (Fin g → O)).snd b = v b := by
  rw [← tsze_expand]
  exact ⟨by simp, fun b ↦ by simp⟩

theorem jet_sh : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {l : Λ}
    {k k' : K.K} (e : K.le l k' k), ∃ χ : K.jet k ⟶ K.jet k', χ.deg = l ∧
      jet0 k ≫ χ = ptHom (K.triv k') e ≫ jet0 k' ∧ jet1 k ≫ χ = ptHom (K.triv k') e ≫ jet1 k' ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        (TrivSqZeroExt.fst (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) = sh e x.fst) ∧
        ∀ a, TrivSqZeroExt.snd (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) a = sh e (x.snd a) := by
  intro I _ g Λ _ F K l k k' e
  have hf1 : ∀ y : Hol (K.W k), (ptHom (K.triv k') e ≫ jet0 k').φ y = TrivSqZeroExt.inl (sh e y) := fun y ↦ by
    change TrivSqZeroExt.inl (sh (K.le_refl k') (sh e y)) = _
    rw [sh_refl]
  have hf2 : ∀ y : Hol (K.W k), (ptHom (K.triv k') e ≫ jet1 k').φ y =
      TrivSqZeroExt.inl (sh e y) + TrivSqZeroExt.inr (fun a ↦ dw a (sh e y)) := fun y ↦ rfl
  obtain ⟨χ, hdeg, h0, h1, hφ⟩ := GlobalTheory.T.exists_jet_extension_square_zero K (T := K.jet k') (ptHom (K.triv k') e ≫ jet0 k')
    (ptHom (K.triv k') e ≫ jet1 k') (fun a ↦ TrivSqZeroExt.inr (Pi.single a 1)) rfl (fun _ ↦ rfl)
    (fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _) (fun x ↦ by
      rw [hf2, hf1]
      simp only [hf1]
      rw [tsze_expand]
      simp only [dw_sh])
  refine ⟨χ, hdeg.trans (add_zero l), h0, h1, fun x ↦ ?_⟩
  have hx : χ.φ x = TrivSqZeroExt.inl (sh e x.fst) +
      ∑ a, TrivSqZeroExt.inl (sh e (x.snd a)) * TrivSqZeroExt.inr (Pi.single a 1) := by
    rw [hφ, hf1]
    simp only [hf1]
  rw [hx]
  exact tsze_expand_fst_snd (sh e x.fst) (fun a ↦ sh e (x.snd a))

end GlobalTheory.AnPer.Charts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetMorphismExtendingTranslationStatement
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jet_morphism_extending_translation : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {l : Λ} {k k' : K.K} (e : K.le l k' k), ∃ χ : K.jet k ⟶ K.jet k', χ.deg = l ∧ jet0 k ≫ χ = ptHom (K.triv k') e ≫ jet0 k' ∧ jet1 k ≫ χ = ptHom (K.triv k') e ≫ jet1 k' ∧ ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), (TrivSqZeroExt.fst (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) = sh e x.fst) ∧ ∀ a, TrivSqZeroExt.snd (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) a = sh e (x.snd a) := by
  first | exact @GlobalTheory.AnPer.Charts.jet_sh | exact GlobalTheory.AnPer.Charts.jet_sh | (intros; apply GlobalTheory.AnPer.Charts.jet_sh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupPeriodic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupPeriodic
open Filter Topology

namespace GlobalTheory.WeilM

theorem SB.exists_periodic {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type}
    (L : ι → AddSubgroup X) (hL : ∀ i, IsOpen (L i : Set X)) (hb : ∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) :
    ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  have key : ∀ Y : X, ∃ i, ∀ C ∈ L i, f (Y + C) = f Y := by
    intro Y
    have h1 : f ⁻¹' {f Y} ∈ 𝓝 (Y + 0) := by rw [add_zero]; exact (hlc.isOpen_fiber _).mem_nhds rfl
    have h2 : {C : X | f (Y + C) = f Y} ∈ 𝓝 (0 : X) := (continuous_const_add Y).continuousAt.preimage_mem_nhds h1
    obtain ⟨i, hi⟩ := hb _ h2
    exact ⟨i, fun C hC => hi hC⟩
  choose g hg using key
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun Y => {Z : X | Z - Y ∈ L (g Y)})
    (fun Y => (hL _).preimage (continuous_sub_right Y))
    (fun Z _ => Set.mem_iUnion.2 ⟨Z, by simp⟩)
  have hW : (⋂ Y ∈ t, (L (g Y) : Set X)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun Y _ => (hL _).mem_nhds (L (g Y)).zero_mem
  obtain ⟨j, hj⟩ := hb _ hW
  refine ⟨j, fun Y C hC => ?_⟩
  have hCt : ∀ Y0 ∈ t, C ∈ L (g Y0) := fun Y0 h0 => by
    have := hj hC
    simp only [Set.mem_iInter] at this
    exact this Y0 h0
  by_cases h : ∃ Y0 ∈ t, Y - Y0 ∈ L (g Y0)
  · obtain ⟨Y0, h0, hY⟩ := h
    have e1 := hg Y0 _ hY
    have e2 := hg Y0 _ (add_mem hY (hCt Y0 h0))
    rw [show Y0 + (Y - Y0) = Y by abel] at e1
    rw [show Y0 + (Y - Y0 + C) = Y + C by abel] at e2
    rw [e1, e2]
  · push_neg at h
    have hn : ∀ Z, Z ∈ tsupport f → ∃ Y0 ∈ t, Z - Y0 ∈ L (g Y0) := fun Z hZ => by
      have := ht hZ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨Y0, h0, h1⟩ := this
      exact ⟨Y0, h0, h1⟩
    have hY : Y ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn Y hZ
      exact h Y0 h0 h1
    have hYC : Y + C ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn _ hZ
      apply h Y0 h0
      have := sub_mem h1 (hCt Y0 h0)
      rwa [show Y + C - Y0 - C = Y - Y0 by abel] at this
    rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYC]

end GlobalTheory.WeilM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupPeriodicStatement
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroup_periodic : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type} (L : ι → AddSubgroup X), (∀ i, IsOpen (L i : Set X)) → (∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) → ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  first | exact @GlobalTheory.WeilM.SB.exists_periodic | exact GlobalTheory.WeilM.SB.exists_periodic | (intros; apply GlobalTheory.WeilM.SB.exists_periodic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetEqSumAddCosetIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetEqSumAddCosetIndicator
open Filter Topology

namespace GlobalTheory.LinSchur


open Classical in
theorem exists_finset_eq_sum_cind {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : AddSubgroup X) (hL : IsOpen (L : Set X)) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hper : ∀ Y, ∀ C ∈ L, f (Y + C) = f Y) :
    ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  have hK : IsCompact (tsupport f) := hf.2
  obtain ⟨F0, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {Y | Y - x ∈ L}) (fun x _ =>
    (hL.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))
  refine ⟨(F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ?_⟩
  have hmk : ∀ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ∀ Y : X,
      Y - y ∈ L ↔ (QuotientAddGroup.mk Y : X ⧸ L) = QuotientAddGroup.mk y := by
    intro y _ Y
    rw [QuotientAddGroup.eq, ← neg_mem_iff]
    simp [sub_eq_add_neg, add_comm]
  funext Y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.LinSchur.cind]
  by_cases hex : ∃ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, Y - y ∈ L
  · obtain ⟨y, hy, hYy⟩ := hex
    rw [Finset.sum_eq_single y]
    · rw [if_pos hYy, mul_one]
      have := hper y (Y - y) hYy
      rw [add_sub_cancel] at this
      exact this
    · intro y' hy' hne
      rw [if_neg, mul_zero]
      intro hY'
      apply hne
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hy'
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
      have e1 := (hmk _ hy' Y).mp hY'
      have e2 := (hmk _ hy Y).mp hYy
      simp only [QuotientAddGroup.out_eq'] at e1 e2
      rw [← e1, ← e2]
    · intro h; exact absurd hy h
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun y hy => by rw [if_neg (hex y hy), mul_zero])]
    apply image_eq_zero_of_notMem_tsupport
    intro hY
    have := hcov hY
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
    obtain ⟨y0, hy0, hYy0⟩ := this
    have hmem : (QuotientAddGroup.mk y0 : X ⧸ L).out ∈
        (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out :=
      Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨y0, hy0, rfl⟩, rfl⟩
    apply hex _ hmem
    rw [hmk _ hmem, QuotientAddGroup.out_eq']
    rw [← QuotientAddGroup.eq_iff_sub_mem.mpr hYy0]

end GlobalTheory.LinSchur
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetEqSumAddCosetIndicatorStatement
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (L : AddSubgroup X), IsOpen (L : Set X) → ∀ f ∈ GlobalTheory.WeilM.SB X, (∀ Y, ∀ C ∈ L, f (Y + C) = f Y) → ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  first | exact @GlobalTheory.LinSchur.exists_finset_eq_sum_cind | exact GlobalTheory.LinSchur.exists_finset_eq_sum_cind | (intros; apply GlobalTheory.LinSchur.exists_finset_eq_sum_cind <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformMemSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformMemSchwartzBruhat
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

namespace GlobalTheory.KSp.FourMem

theorem eventually_invariant {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {f : X → ℂ} (hf : f ∈ SB X) : ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x := by
    have h3 : Filter.Tendsto (fun t : X => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact h3.eventually h1
  filter_upwards [h1, h2] with t ht ht' x
  by_cases hx : x ∈ tsupport f
  · exact ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · rw [← ht' _ hx', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem four_mem_SB : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by
  intro X _ _ _ _ h μ _ e he φ hφ
  haveI := h.grp
  haveI := h.t2
  haveI := h.lc
  haveI := h.sc
  obtain ⟨K, hK, hKm⟩ := he.big _ (eventually_invariant hφ)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_, HasCompactSupport.intro hK fun y hy => ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport φ, e z x = e y x := by
      refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
      have h2 : IsLocallyConstant fun q : X × X => (e q.1 q.2, e y q.2) :=
        he.lc.prodMk (he.lc.comp_continuous (continuous_const.prodMk continuous_snd))
      filter_upwards [h2.eventually_eq (y, x)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with z hz
    unfold four
    congr 1
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hz x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · obtain ⟨t, ht, hne⟩ : ∃ t, (∀ x, φ (x + t) = φ x) ∧ e t y ≠ 1 := by
      by_contra hne
      exact hy (hKm y fun t ht => by
        by_contra h4
        exact hne ⟨t, ht, h4⟩)
    have h1 := integral_add_right_eq_self (μ := μ) (fun x => e y x * φ x) t
    have h2 : ∀ x, e y (x + t) * φ (x + t) = e t y * (e y x * φ x) := by
      intro x
      rw [ht, he.symm y (x + t), he.add, he.symm x y]; ring
    simp only [h2, integral_const_mul] at h1
    refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
    unfold four
    rw [sub_mul, h1, one_mul, sub_self]

end GlobalTheory.KSp.FourMem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformMemSchwartzBruhatStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by
  first | exact @GlobalTheory.KSp.FourMem.four_mem_SB | exact GlobalTheory.KSp.FourMem.four_mem_SB | (intros; apply GlobalTheory.KSp.FourMem.four_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerOneHolds
noncomputable section

open Complex DirichletCharacter

namespace GlobalTheory.LogDerOneProof

theorem logDerOne_holds : GlobalTheory.Mem.An.LogDerOne := by
  classical
  obtain ⟨C, hC, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨2 * C, fun q _ χ hq hp => ?_⟩
  have hne : χ ≠ 1 := by
    intro h
    have h1 : χ.conductor = q := hp
    rw [h, DirichletCharacter.conductor_one] at h1
    omega
  have hL : LFunction χ 1 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simp)
  obtain ⟨hfin, hcount, hmain⟩ := H q χ hne 1 (by norm_num) (by norm_num) hL
  simp only [Complex.one_im, abs_zero, zero_add, Complex.ofReal_zero, zero_mul, add_zero] at hfin hcount hmain
  set D : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hD
  set Z : Set ℂ := GlobalTheory.Mem.An.zerosIn χ 0 1 with hZ
  have hsub : Z ⊆ D := by
    rintro w ⟨h0, h1, h2, h3⟩
    refine ⟨?_, h3⟩
    have h4 := Complex.norm_le_abs_re_add_abs_im (w - 2)
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero] at h4 h2
    have h5 : |w.re - 2| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hZfin : Z.Finite := hfin.subset hsub
  have hsub' : hZfin.toFinset ⊆ hfin.toFinset := by
    intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    exact hsub hw
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount hmain
  have hz : GlobalTheory.Mem.An.zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) =
      ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) := by
    unfold GlobalTheory.Mem.An.zsum
    rw [← hZ, finsum_mem_eq_finite_toFinset_sum _ hZfin]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [GlobalTheory.Mem.An.zmult]
    ring
  rw [hz]
  rw [← Finset.sum_sdiff hsub'] at hmain
  have hrest : ‖∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)‖ ≤
      ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun w hw => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => Nat.cast_nonneg _))
    simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset] at hw
    obtain ⟨⟨_, hw0⟩, hwn⟩ := hw
    have hre : w.re < 1 := by
      by_contra h
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (not_lt.1 h) hw0
    have h1 : 1 ≤ ‖1 - w‖ := by
      by_cases h0 : 0 < w.re
      · have him : 1 < |w.im| := by
          by_contra h
          exact hwn ⟨h0, hre, by simpa using not_lt.1 h, hw0⟩
        have h4 := Complex.abs_im_le_norm (1 - w)
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h4
        linarith
      · have h4 := Complex.re_le_norm (1 - w)
        simp only [Complex.sub_re, Complex.one_re] at h4
        linarith [not_lt.1 h0]
    rw [norm_div, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg _) h1
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log (q * 2) ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : C * Real.log (q * 2) ≤ C * Real.log (3 * q) := mul_le_mul_of_nonneg_left hlog hC.le
  set A := deriv (LFunction χ) 1 / LFunction χ 1
  set R := ∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  set S := ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  have e : A - S = (A - (R + S)) + R := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end GlobalTheory.LogDerOneProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZero
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem inCell_iff_det_ne_zero : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)),
    InCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0 := by
  intro F _ _ E _ _ c δ hE ν _ _ g
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    have hdet : ∀ x : UG c (stdJ ν E), (mat c x).det ≠ 0 := fun x =>
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (x : GL (ν ⊕ ν) E))).ne_zero
    have hp0 : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0 (mat c p).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hp, fromBlocks_toBlocks]
    have hq0 : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0 (mat c q).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hq, fromBlocks_toBlocks]
    have hpd := hdet p
    have hqd := hdet q
    rw [hp0, det_fromBlocks_zero₂₁] at hpd
    rw [hq0, det_fromBlocks_zero₂₁] at hqd
    change (mat c p * stdJ ν E * mat c q).toBlocks₂₁.det ≠ 0
    rw [hp0, hq0]
    simp only [stdJ, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [det_neg, det_mul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (mul_ne_zero (right_ne_zero_of_mul hpd) (left_ne_zero_of_mul hqd))
  · intro hC
    set A := (mat c g).toBlocks₁₁ with hA
    set B := (mat c g).toBlocks₁₂ with hB
    set C := (mat c g).toBlocks₂₁ with hCdef
    set D := (mat c g).toBlocks₂₂ with hD
    have hg0 : mat c g = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    have hrel : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
    have hkey : C * (D.map c)ᵀ = D * (C.map c)ᵀ := by
      have h := congrArg Matrix.toBlocks₂₂ hrel
      rw [hg0] at h
      simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
      simp at h
      exact (neg_add_eq_zero.1 h).symm
    have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 (isUnit_iff_ne_zero.2 hC)
    have hCs : IsUnit (C.map c)ᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, det_transpose]
      exact (hCu.map (RingHom.mapMatrix (c : E →+* E))).map detMonoidHom
    have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hC)
    set v := C⁻¹ * D with hv
    have hvh : (v.map c)ᵀ = v := by
      apply hCu.mul_left_cancel
      apply hCs.mul_right_cancel
      have e1 : ((v.map c)ᵀ) * (C.map c)ᵀ = (D.map c)ᵀ := by
        rw [hv, Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← transpose_mul, ← Matrix.map_mul, hCC,
          Matrix.map_one _ (map_zero c) (map_one c), transpose_one, Matrix.mul_one]
      rw [Matrix.mul_assoc, e1, hkey, hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
    let q := unip c v hvh
    have hq : q ∈ sieg c ν := by
      change (fromBlocks (1 : Matrix ν ν E) v 0 1).toBlocks₂₁ = 0
      rw [toBlocks_fromBlocks₂₁]
    refine ⟨g * q⁻¹ * (weyl c ν)⁻¹, ?_, q, hq, by group⟩
    rw [mem_sieg]
    change (mat c g * fromBlocks 1 (-v) 0 1 * -stdJ ν E).toBlocks₂₁ = 0
    rw [hg0]
    simp only [stdJ, fromBlocks_neg, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul, neg_add_cancel]

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZeroStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)), InCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0 := by
  first | exact @GlobalTheory.KSp.inCell_iff_det_ne_zero | exact GlobalTheory.KSp.inCell_iff_det_ne_zero | (intros; apply GlobalTheory.KSp.inCell_iff_det_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorsorFieldPoint


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor (B D : Type) [CommRing B] [CommRing D]
    [Algebra B D] (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act) : Algebra.FormallyUnramified B D := by
  obtain ⟨-, -, hff, hbij⟩ := h
  haveI : NeZero q := ⟨hq.ne'⟩
  let g : D →ₐ[B] (Multiplicative (ZMod q) → D) :=
    Pi.algHom B (fun _ ↦ D) fun σ ↦ (act σ : D →ₐ[B] D)
  let F : D ⊗[B] D →ₐ[D] (Multiplicative (ZMod q) → D) :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId D _) g
  have hF : (F : D ⊗[B] D → _) = Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ ↦ D) fun _ ↦ AlgHom.id B D) g := by
    ext x : 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp_all
  have hFb : Function.Bijective F := by rw [hF]; exact hbij
  haveI : Algebra.FormallyUnramified D (Multiplicative (ZMod q) → D) :=
    (Algebra.FormallyUnramified.pi_iff _).2 fun _ ↦ inferInstance
  haveI : Algebra.FormallyUnramified D (D ⊗[B] D) :=
    Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofBijective F hFb).symm
  exact Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat D


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.TorsorFieldPoint.exists_point_finite_separable : ∀ (B K : Type) [CommRing B] [Field K]
    (f : B →+* K) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L)
      (σ : D →+* L), σ.comp (algebraMap B D) = (algebraMap K L).comp f := by
  intro B K _ _ f D _ _ q hq act h
  haveI := _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor B D q hq act h
  obtain ⟨hfin, -, hff, -⟩ := h
  letI : Algebra B K := f.toAlgebra
  haveI : Nontrivial (K ⊗[B] D) := Module.FaithfullyFlat.rTensor_nontrivial B D K
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[B] D)
  letI : Field (K ⊗[B] D ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (K ⊗[B] D ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.FormallyUnramified K (K ⊗[B] D ⧸ m) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective
  refine ⟨K ⊗[B] D ⧸ m, inferInstance, inferInstance, inferInstance,
    Algebra.FormallyUnramified.isSeparable K _,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext b
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.algebraMap_eq]
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rfl

end GlobalTheory.TorsorFieldPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparableStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_exists_point_finite_separable : ∀ (B K : Type) [CommRing B] [Field K] (f : B →+* K) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
      (σ : D →+* L), σ.comp (algebraMap B D) = (algebraMap K L).comp f := by
  first | (exact @GlobalTheory.TorsorFieldPoint.exists_point_finite_separable) | (exact GlobalTheory.TorsorFieldPoint.exists_point_finite_separable) | (intros; apply GlobalTheory.TorsorFieldPoint.exists_point_finite_separable  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapConditionsOfLargeGaps
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEG

def GapNum : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ),
    (∀ i j : Fin r, (j : ℕ) = i + 1 → 100 * (r : ℤ) ^ 4 ≤ lam i - lam j) →
    Formalism.QuantumDeterminants.IsHCParam (fun a => (lam a : ℝ)) ∧ StdGap ε (fun a => (lam a : ℝ)) ∧ Gap3 ε (fun a => (lam a : ℝ)) ∧
      ∃ h : ℝ, GapAtLeast ε (fun a => (lam a : ℝ)) h ∧ thrStar ε < h

end GlobalTheory.PsCo.PcEG

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG (GapNum)

namespace GapNumber

theorem chain {r : ℕ} {lam : Fin r → ℤ} {H : ℤ} (hH : 0 ≤ H)
    (hg : ∀ i j : Fin r, (j : ℕ) = i + 1 → H ≤ lam i - lam j) :
    ∀ i j : Fin r, i < j → H ≤ lam i - lam j := by
  suffices h : ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k + 1 → H ≤ lam i - lam j by
    intro i j hij
    have : (i : ℕ) < j := hij
    exact h ((j : ℕ) - i - 1) i j (by omega)
  intro k
  induction k with
  | zero => intro i j h; exact hg i j (by omega)
  | succ k ih =>
    intro i j h
    have hm : (i : ℕ) + k + 1 < r := by have := j.isLt; omega
    have h1 := ih i ⟨(i : ℕ) + k + 1, hm⟩ rfl
    have h2 := hg ⟨(i : ℕ) + k + 1, hm⟩ j (by show (j : ℕ) = (i : ℕ) + k + 1 + 1; omega)
    linarith

end GapNumber

theorem gapConditions_of_largeGaps : GapNum := by
  intro r hr ε lam hg
  obtain ⟨k, hk⟩ := hr
  have hr1 : 1 ≤ r := by omega
  have hH : (0 : ℤ) ≤ 100 * (r : ℤ) ^ 4 := by positivity
  have hc := GapNumber.chain hH hg
  have hcR : ∀ i j : Fin r, i < j → 100 * (r : ℝ) ^ 4 ≤ (lam i : ℝ) - lam j := fun i j h => by
    exact_mod_cast hc i j h
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hpos : (0 : ℝ) < 100 * (r : ℝ) ^ 4 := by positivity
  have hanti : StrictAnti (fun a => (lam a : ℝ)) := fun i j h => by
    have := hcR i j h
    show (lam j : ℝ) < lam i
    linarith
  have hgap : GapAtLeast ε (fun a => (lam a : ℝ)) (100 * (r : ℝ) ^ 4) := by
    intro a b hab
    have hne : a ≠ b := fun h => hab (h ▸ rfl)
    show 100 * (r : ℝ) ^ 4 ≤ |(lam a : ℝ) - lam b|
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hcR a b h).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hcR b a h).trans (le_abs_self _)
  have hp : pOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq : qOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq0 : S7.q0 ε ≤ r := (min_le_left _ _).trans hp
  have hpR : (pOf ε : ℝ) ≤ r := by exact_mod_cast hp
  have hqR : (qOf ε : ℝ) ≤ r := by exact_mod_cast hq
  have hq0R : (S7.q0 ε : ℝ) ≤ r := by exact_mod_cast hq0
  have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hrR
  have h4 : (r : ℝ) ≤ (r : ℝ) ^ 4 := le_self_pow₀ hrR (by norm_num)
  have h2 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have h3 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have hbig : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < 100 * (r : ℝ) ^ 4 := by
    have : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ r * r * r := by gcongr
    nlinarith
  refine ⟨⟨hanti, fun a => ⟨lam a - k, ?_⟩⟩, ⟨hanti, _, hgap, hbig⟩, ⟨hanti, _, hgap, by linarith⟩, _, hgap, ?_⟩
  · have hkR : (r : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    show (lam a : ℝ) - ((r : ℝ) - 1) / 2 = ((lam a - k : ℤ) : ℝ)
    rw [hkR]; push_cast; ring
  · unfold thrStar
    refine max_lt hbig ?_
    have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * r := by
      rw [show (2 : ℝ) * r = Real.sqrt ((2 * r) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hm : (r : ℝ) * (S7.q0 ε : ℝ) ≤ r * r := mul_le_mul_of_nonneg_left hq0R (by positivity)
    nlinarith

end GlobalTheory.PsCo.PcEF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSubgroupExhaustion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSubgroupExhaustion
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

namespace GlobalTheory.KSp.GoodSpace

open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi ValuativeRel

theorem good_of_addEquiv {X Y : Type} [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y]
    (f : X ≃+ Y) (hf : Continuous f) (hg : Continuous f.symm) (h : Good Y) : Good X := by
  let H : X ≃ₜ Y := { toEquiv := f.toEquiv, continuous_toFun := hf, continuous_invFun := hg }
  haveI := h.grp; haveI := h.t2; haveI := h.lc; haveI := h.sc
  refine ⟨?_, H.isEmbedding.t2Space, H.isClosedEmbedding.locallyCompactSpace, H.isInducing.secondCountableTopology,
    ?_, ?_⟩
  · haveI : ContinuousAdd X := by
      refine ⟨?_⟩
      have : (fun p : X × X => p.1 + p.2) = fun p => f.symm (f p.1 + f p.2) := by
        funext p; simp
      rw [this]; exact hg.comp ((hf.comp continuous_fst).add (hf.comp continuous_snd))
    haveI : ContinuousNeg X := by
      refine ⟨?_⟩
      have : (fun x : X => -x) = fun x => f.symm (-f x) := by funext x; simp
      rw [this]; exact hg.comp hf.neg
    exact {}
  · intro K hK
    obtain ⟨L, hLc, hLo, hKL⟩ := h.large (f '' K) (hK.image hf)
    refine ⟨L.comap f.toAddMonoidHom, ?_, ?_, ?_⟩
    · have : ((L.comap f.toAddMonoidHom : AddSubgroup X) : Set X) = H ⁻¹' (L : Set Y) := rfl
      rw [this]; exact H.isCompact_preimage.mpr hLc
    · exact hLo.preimage hf
    · intro x hx; exact hKL ⟨x, hx, rfl⟩
  · intro U hU
    have hU' : f.symm ⁻¹' U ∈ 𝓝 (0 : Y) := by
      apply hg.continuousAt.preimage_mem_nhds; simpa using hU
    obtain ⟨L, hLc, hLo, hLU⟩ := h.small _ hU'
    refine ⟨L.comap f.toAddMonoidHom, ?_, hLo.preimage hf, ?_⟩
    · have : ((L.comap f.toAddMonoidHom : AddSubgroup X) : Set X) = H ⁻¹' (L : Set Y) := rfl
      rw [this]; exact H.isCompact_preimage.mpr hLc
    · intro x hx
      have := hLU hx
      simpa using this

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def boxSub (n : Type) [Fintype n] [DecidableEq n] (s : Fˣ) : AddSubgroup (n → F) where
  carrier := box n s
  zero_mem' := fun i _ => by simp [cball]
  add_mem' := fun ha hb i _ => add_mem_cball (ha i trivial) (hb i trivial)
  neg_mem' := fun ha i _ => neg_mem_cball (ha i trivial)

theorem cball_mono {s t : Fˣ} (h : valuation F (s : F) ≤ valuation F (t : F)) : cball s ⊆ cball t :=
  fun x hx => show valuation F x ≤ valuation F (t : F) from le_trans hx h

theorem mem_some_cball (y : F) : ∃ s : Fˣ, y ∈ cball s := by
  by_cases hy : y = 0
  · exact ⟨1, by simp [cball, hy]⟩
  · exact ⟨Units.mk0 y hy, by simp [cball]⟩

theorem mem_some_box (n : Type) [Fintype n] [DecidableEq n] (x : n → F) : ∃ s : Fˣ, x ∈ box n s := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, fun i => isEmptyElim i⟩
  · choose u hu using fun i => mem_some_cball (x i)
    obtain ⟨j, hj⟩ := Finite.exists_max fun i => valuation F (u i : F)
    exact ⟨u j, fun i _ => cball_mono (hj i) (hu i)⟩

theorem good_pi (n : Type) [Fintype n] [DecidableEq n] : Good (n → F) := by
  haveI := secondCountable F
  haveI := t2Space F
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro K hK
    obtain ⟨s, hs⟩ := hK.elim_directed_cover (fun s : Fˣ => box n s) (fun s => isOpen_box s)
      (fun x _ => Set.mem_iUnion.mpr (mem_some_box n x)) (by
        intro s t
        rcases le_total (valuation F (s : F)) (valuation F (t : F)) with h | h
        · exact ⟨t, fun x hx i _ => cball_mono h (hx i trivial), le_rfl⟩
        · exact ⟨s, le_rfl, fun x hx i _ => cball_mono h (hx i trivial)⟩)
    exact ⟨boxSub n s, isCompact_box s, isOpen_box s, hs⟩
  · intro U hU
    obtain ⟨s, hs⟩ := exists_box_subset hU
    exact ⟨boxSub n s, isCompact_box s, isOpen_box s, hs⟩

end GlobalTheory.KSp.GoodSpace

theorem GlobalTheory.KSp.good_of_finiteDimensional : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V], Good V := by
  intro F _ _ _ _ _ V _ _ _ _ _
  haveI := IsModuleTopology.topologicalAddGroup F V
  let b := Module.finBasis F V
  let e := b.equivFun
  exact GlobalTheory.KSp.GoodSpace.good_of_addEquiv e.toAddEquiv
    (IsModuleTopology.continuous_of_linearMap (R := F) e.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap (R := F) e.symm.toLinearMap)
    (GlobalTheory.KSp.GoodSpace.good_pi _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSubgroupExhaustionStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V], Good V := by
  first | exact @GlobalTheory.KSp.good_of_finiteDimensional | exact GlobalTheory.KSp.good_of_finiteDimensional | (intros; apply GlobalTheory.KSp.good_of_finiteDimensional <;> assumption)
end
end

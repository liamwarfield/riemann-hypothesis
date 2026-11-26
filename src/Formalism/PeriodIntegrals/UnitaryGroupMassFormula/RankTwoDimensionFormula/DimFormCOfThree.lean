module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.FlagLevelCharacterEqPsiDivN

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfSteps
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.GammaOneEqProd
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem gam1_eq_prod_card_div_cardU (TR : TypedRed X) :
    Gam1 TR = ∏ v, ((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ)) := by
  have h1 : Formalism.L2.SG.GGMirabolic.gamProd TR.psi0 (1 : Iof TR) =
      ((∏ v, ((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ)) : ℝ) : ℂ) := by
    simp only [Formalism.L2.SG.GGMirabolic.gamProd, Pi.one_apply, Formalism.L2.SG.GGMirabolic.gam_one]
    push_cast
    rfl
  unfold Gam1
  rw [h1, Complex.ofReal_re]

theorem cardU_pos (F : Type) [Field F] [Fintype F] (k : ℕ) : 0 < Formalism.L2.SG.GGMirabolic.cardU F k := by
  unfold Formalism.L2.SG.GGMirabolic.cardU
  have h1 : Formalism.L2.SG.GGMirabolic.IsUni k (1 : GL (Fin k) F) := by
    simp [Formalism.L2.SG.GGMirabolic.IsUni, Matrix.one_apply]
    intro i j h e
    subst e
    exact lt_irrefl _ h
  have : Nonempty {x : GL (Fin k) F // Formalism.L2.SG.GGMirabolic.IsUni k x} := ⟨⟨1, h1⟩⟩
  exact Nat.card_pos

theorem gamma_one_pos (TR : TypedRed X) : 0 < Gam1 TR := by
  rw [gam1_eq_prod_card_div_cardU]
  apply Finset.prod_pos
  intro v _
  apply div_pos
  · exact_mod_cast Fintype.card_pos
  · exact_mod_cast cardU_pos _ _

variable {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem card_classes_eq (hK : X.LevelSubgroupCharacter) (cs : ColSys X u what₂) (hR : ColReps hK cs) :
    Nat.card (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK)) = Fintype.card cs.Cl := by
  rw [← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_eq_of_bijective
    (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u hK) (cs.h ρ)) ⟨?_, ?_⟩
  · intro ρ ρ' he
    obtain ⟨a, ha, b, hb, hab⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 he
    obtain ⟨γ, rfl⟩ := ha
    obtain ⟨ρ₀, _, hu⟩ := hR (cs.h ρ')
    have e1 := hu ρ' ⟨1, 1, by simp⟩
    have e2 := hu ρ ⟨γ, ⟨b, hb⟩, hab⟩
    exact e2.trans e1.symm
  · intro q
    induction q using Quotient.inductionOn' with
    | h h =>
      obtain ⟨ρ, ⟨γ, κ, hh⟩, _⟩ := hR h
      refine ⟨ρ, ?_⟩
      show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ _
      rw [DoubleCoset.eq]
      exact ⟨iotaF X u γ, ⟨γ, rfl⟩, κ, κ.2, hh⟩

theorem classFin_of (hK : X.LevelSubgroupCharacter) (cs : ColSys X u what₂) (hR : ColReps hK cs) :
    Formalism.L2.SG.PoincareInHH.Cut.ClassFin X u hK := by
  have hs : Function.Surjective
      (fun ρ : cs.Cl => DoubleCoset.mk (iotaF X u).range (Ku X u hK) (cs.h ρ)) := by
    intro q
    induction q using Quotient.inductionOn' with
    | h h =>
      obtain ⟨ρ, ⟨γ, κ, hh⟩, _⟩ := hR h
      refine ⟨ρ, ?_⟩
      show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ _
      rw [DoubleCoset.eq]
      exact ⟨iotaF X u γ, ⟨γ, rfl⟩, κ, κ.2, hh⟩
  exact Finite.of_surjective _ hs

theorem duC_eq (Y : Full X) (u : D.what₂.Word) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) :
    Formalism.L2.SG.RowsConc.duC X Y u = Formalism.L2.SG.KappaOffDiagonal.dpiC X u * (Fintype.card (Y.cs u).Cl : ℝ) := by
  unfold Formalism.L2.SG.RowsConc.duC Formalism.L2.SG.KappaOffDiagonal.dpiC
  rw [(Formalism.L2.SG.PoincareInHH.Cut.cols_dim_of_neat X u Y.hK hN
      (classFin_of Y.hK (Y.cs u) (Y.colReps u))).2, card_classes_eq Y.hK (Y.cs u) (Y.colReps u)]
  push_cast; ring

def fib (cs : ColSys X u what₂) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Finset cs.Cl :=
  Finset.univ.filter fun ρ => cs.lamOf ρ = Λ

theorem card_cl_eq_sum (cs : ColSys X u what₂) :
    (Fintype.card cs.Cl : ℝ) = ∑ Λ ∈ what₂, ((fib cs Λ).card : ℝ) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset cs.Cl)) (t := what₂) (f := cs.lamOf)
    (fun ρ _ => cs.lam_mem ρ)
  rw [Finset.card_univ] at h
  rw [h, Nat.cast_sum]
  rfl

def FibreBound : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ Λ ∈ Y.what₂ u, Gam1 Y.TR * wRow D (X.Fu u) Λ ≤ ((fib (Y.cs u) Λ).card : ℝ)

theorem dimFormC_of (h4 : FibreBound) : Formalism.L2.SG.KappaOffDiagonal.DimFormC := by
  intro D X Y u hT
  have hG : (Y.tO u u).Gam1 = Gam1 Y.TR := rfl
  rw [hG]
  refine ⟨(gamma_one_pos Y.TR).le, ?_⟩
  rw [duC_eq Y u (hT.2.1 u), card_cl_eq_sum]
  have hd : 0 ≤ Formalism.L2.SG.KappaOffDiagonal.dpiC X u := by unfold Formalism.L2.SG.KappaOffDiagonal.dpiC; positivity
  have hm : Gam1 Y.TR * Formalism.L2.SG.KappaOffDiagonal.massC Y u ≤ ∑ Λ ∈ Y.what₂ u, ((fib (Y.cs u) Λ).card : ℝ) := by
    unfold Formalism.L2.SG.KappaOffDiagonal.massC massRows
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun Λ hΛ => h4 D X Y u hT Λ hΛ
  calc Gam1 Y.TR * Formalism.L2.SG.KappaOffDiagonal.massC Y u * Formalism.L2.SG.KappaOffDiagonal.dpiC X u
      ≤ (∑ Λ ∈ Y.what₂ u, ((fib (Y.cs u) Λ).card : ℝ)) * Formalism.L2.SG.KappaOffDiagonal.dpiC X u :=
        mul_le_mul_of_nonneg_right hm hd
    _ = _ := by ring

end PI.UnitaryDimensionFormula
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def latS {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (h : X.B.I.Gf) : Set (VS D).V :=
  {y | (X.B.I.fmat (h * X.xu u)⁻¹).mulVec (incl X.B.I (X.crd y)) ∈ X.B.I.Lf}

theorem lamOf_eq_latS {D : D7} {X : HidaSetting D} {u : D.what₂.Word}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (ρ : cs.Cl) :
    ((cs.lamOf ρ : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) = latS X u (cs.h ρ : X.B.I.Gf) := by
  ext y
  exact cs.lat_eq ρ y

def OrbitCount : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (n : ℕ) (t : Fin n → G) (A : Set G) (N : ℕ),
    A.Finite → Nat.card A ≤ N →
    (∀ i j, (t i)⁻¹ * t j ∈ K → i = j) →
    (∀ i j, ∀ γ ∈ Γ, ∀ κ ∈ K, t j = γ * t i * κ → γ ∈ A) →
    n ≤ N * Nat.card (Set.range fun i => DoubleCoset.mk Γ K (t i))

def Transport : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ g ∈ stabF D (X.Fu u),
    ∀ h : X.B.I.Gf, latS X u ((iotaF X u γ : X.B.I.Gf) * h) = g '' latS X u h

def KuStab : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (h : X.B.I.Gf) (κ : Ku X u hK),
    latS X u (h * ((κ : Hfin X u) : X.B.I.Gf)) = latS X u h

def StabBound : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ Λ ∈ Y.what₂ u, (autLz D (X.Fu u) Λ).Finite →
      ∃ A : Set (Hfin X u), A.Finite ∧ Nat.card A ≤ Nat.card (autLz D (X.Fu u) Λ) ∧
        ∀ h h' : Hfin X u, latS X u (h : X.B.I.Gf) = (Λ : Set (VS D).V) →
          latS X u (h' : X.B.I.Gf) = (Λ : Set (VS D).V) →
          ∀ γ ∈ (iotaF X u).range, ∀ κ ∈ Ku X u Y.hK, h' = γ * h * κ → γ ∈ A

def IndexGe : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ Λ ∈ Y.what₂ u, ∃ (n : ℕ) (t : Fin n → Hfin X u), Gam1 Y.TR ≤ (n : ℝ) ∧
      (∀ i, latS X u (t i : X.B.I.Gf) = (Λ : Set (VS D).V)) ∧
      ∀ i j, (t i)⁻¹ * t j ∈ Ku X u Y.hK → i = j

theorem fibreCover (hT : Transport) (hS : KuStab) {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ Y.what₂ u) (h : Hfin X u)
    (hh : latS X u (h : X.B.I.Gf) = (Λ : Set (VS D).V)) :
    ∃ ρ ∈ fib (Y.cs u) Λ, DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) h =
      DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ) := by
  obtain ⟨ρ, ⟨γ, κ, hρ⟩, -⟩ := Y.colReps u h
  refine ⟨ρ, ?_, ?_⟩
  · simp only [fib]
    have h1 : latS X u (h : X.B.I.Gf) =
        latS X u ((iotaF X u γ : X.B.I.Gf) * ((Y.cs u).h ρ : X.B.I.Gf)) := by
      rw [hρ, Subgroup.coe_mul, hS D X u Y.hK _ κ, Subgroup.coe_mul]
    obtain ⟨g, hg, hgt⟩ := hT D X u γ
    have h2 : (Λ : Set (VS D).V) = g '' ((((Y.cs u).lamOf ρ) : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) := by
      rw [← hh, h1, hgt, lamOf_eq_latS]
    have hR := Y.rowsOK u
    unfold IsRowReps at hR
    obtain ⟨hRl, hU⟩ := hR
    obtain ⟨Λ0, -, huniq⟩ := hU Λ (hRl Λ hΛ)
    have e1 : Λ = Λ0 := huniq Λ ⟨hΛ, 1, by simp [stabF], by ext; simp [Formalism.HermitianLatticesTheory.gmap]⟩
    have e2 : (Y.cs u).lamOf ρ = Λ0 := by
      refine huniq _ ⟨(Y.cs u).lam_mem ρ, g, hg, ?_⟩
      apply SetLike.coe_injective
      rw [h2]
      simp [Formalism.HermitianLatticesTheory.gmap]
    simpa using e2.trans e1.symm
  · exact ((@DoubleCoset.eq _ _ _ _ _ _).mpr ⟨iotaF X u γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩, κ, κ.2, hρ⟩).symm

theorem fibreBound_of (hO : OrbitCount) (hT : Transport) (hS : KuStab) (hB : StabBound) (hI : IndexGe) :
    FibreBound := by
  intro D X Y u hC Λ hΛ
  obtain ⟨n, t, hn, ht, hd⟩ := hI D X Y u hC Λ hΛ
  unfold wRow
  by_cases hN0 : Nat.card (autLz D (X.Fu u) Λ) = 0
  · simp [hN0]
  have hfin : (autLz D (X.Fu u) Λ).Finite :=
    Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hN0)
  obtain ⟨A, hAf, hAc, hA⟩ := hB D X Y u hC Λ hΛ hfin
  have horb := hO (Hfin X u) (iotaF X u).range (Ku X u Y.hK) n t A _ hAf hAc hd
    (fun i j γ hγ κ hκ he => hA (t i) (t j) (ht i) (ht j) γ hγ κ hκ he)
  have hsub : Set.range (fun i => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (t i)) ⊆
      (((fib (Y.cs u) Λ).image
        (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)) : Finset _) : Set _) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨ρ, hρ, he⟩ := fibreCover hT hS Y u Λ hΛ (t i) (ht i)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ρ, hρ, he.symm⟩)
  have hc : Nat.card (Set.range (fun i => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (t i))) ≤
      (fib (Y.cs u) Λ).card := by
    calc _ ≤ Nat.card (((fib (Y.cs u) Λ).image
          (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)) : Finset _) : Set _) :=
          Nat.card_mono (Finset.finite_toSet _) hsub
      _ = ((fib (Y.cs u) Λ).image
          (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ))).card := by
          rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ _ := Finset.card_image_le
  have hNpos : (0 : ℝ) < (Nat.card (autLz D (X.Fu u) Λ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hN0
  have key : (n : ℝ) ≤ (Nat.card (autLz D (X.Fu u) Λ) : ℝ) * ((fib (Y.cs u) Λ).card : ℝ) := by
    exact_mod_cast horb.trans (Nat.mul_le_mul_left _ hc)
  calc Gam1 Y.TR * ((Nat.card (autLz D (X.Fu u) Λ) : ℝ))⁻¹
      ≤ (n : ℝ) * ((Nat.card (autLz D (X.Fu u) Λ) : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hn (inv_nonneg.mpr hNpos.le)
    _ ≤ ((fib (Y.cs u) Λ).card : ℝ) := by
        rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
        linarith [key]

theorem dimFormC_of_steps (hO : OrbitCount) (hT : Transport) (hS : KuStab) (hB : StabBound) (hI : IndexGe) :
    Formalism.L2.SG.KappaOffDiagonal.DimFormC :=
  dimFormC_of (fibreBound_of hO hT hS hB hI)

end PI.UnitaryDimensionFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfThree
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem orbitCount : OrbitCount := by
  intro G _ Γ K n t A N hA hAN hK hΓ
  classical
  have key : ∀ j i, DoubleCoset.mk Γ K (t i) = DoubleCoset.mk Γ K (t j) →
      ∃ γ ∈ Γ, ∃ κ ∈ K, t j = γ * t i * κ := fun j i h => (@DoubleCoset.eq _ _ Γ K (t i) (t j)).mp h
  have hcard : (Finset.univ : Finset (Fin n)).card ≤
      N * (Finset.univ.image fun i => DoubleCoset.mk Γ K (t i)).card := by
    apply Finset.card_le_mul_card_image
    intro a ha
    obtain ⟨i0, -, rfl⟩ := Finset.mem_image.mp ha
    let g : Fin n → G := fun j =>
      if h : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j) then (key j i0 h).choose else 1
    calc (Finset.univ.filter fun j => DoubleCoset.mk Γ K (t j) = DoubleCoset.mk Γ K (t i0)).card
        ≤ hA.toFinset.card := by
          apply Finset.card_le_card_of_injOn g
          · intro j hj
            have hj' : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j) :=
              ((Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2).symm
            obtain ⟨hγ, κ, hκ, he⟩ := (key j i0 hj').choose_spec
            rw [Finset.mem_coe, Set.Finite.mem_toFinset]
            simp only [g, dif_pos hj']
            exact hΓ i0 j _ hγ κ hκ he
          · intro j hj j' hj' hgg
            have h1 : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j) :=
              ((Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2).symm
            have h2 : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j') :=
              ((Finset.mem_filter.mp (Finset.mem_coe.mp hj')).2).symm
            obtain ⟨-, κ, hκ, he⟩ := (key j i0 h1).choose_spec
            obtain ⟨-, κ', hκ', he'⟩ := (key j' i0 h2).choose_spec
            simp only [g, dif_pos h1, dif_pos h2] at hgg
            apply hK
            rw [he, he', hgg]
            have e1 : ((key j' i0 h2).choose * t i0 * κ)⁻¹ * ((key j' i0 h2).choose * t i0 * κ') = κ⁻¹ * κ' := by
              group
            rw [e1]
            exact K.mul_mem (K.inv_mem hκ) hκ'
      _ ≤ N := by
          rw [← Set.ncard_eq_toFinset_card A hA, ← Nat.card_coe_set_eq]
          exact hAN
  have e : Nat.card (Set.range fun i => DoubleCoset.mk Γ K (t i)) =
      (Finset.univ.image fun i => DoubleCoset.mk Γ K (t i)).card := by
    first
      | rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_range]
      | simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
  rw [e]
  simpa using hcard

theorem kuStab : KuStab := by
  intro D X u hK h κ
  obtain ⟨⟨κ, hκ'⟩, hκ⟩ := κ
  have hk : (X.xu u)⁻¹ * κ * X.xu u ∈ X.K2 := hκ
  show latS X u (h * κ) = latS X u h
  have h2 : ((X.xu u)⁻¹ * κ * X.xu u)⁻¹ ∈ X.K2 := hK.2.2.1 _ hk
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.K2 K2set at h2
  have hs : ∀ x, x ∈ X.B.I.Lf ↔
      (X.B.I.fmat ((X.xu u)⁻¹ * κ * X.xu u)⁻¹).mulVec x ∈ X.B.I.Lf := h2.1
  have he : (h * κ * X.xu u)⁻¹ = ((X.xu u)⁻¹ * κ * X.xu u)⁻¹ * (h * X.xu u)⁻¹ := by
    group
  have hm : X.B.I.fmat (((X.xu u)⁻¹ * κ * X.xu u)⁻¹ * (h * X.xu u)⁻¹) =
      X.B.I.fmat ((X.xu u)⁻¹ * κ * X.xu u)⁻¹ * X.B.I.fmat (h * X.xu u)⁻¹ := rfl
  ext y
  simp only [latS, Set.mem_setOf_eq]
  rw [he, hm, ← Matrix.mulVec_mulVec]
  exact (hs _).symm

theorem dimFormC_of_three (hT : Transport) (hB : StabBound) (hI : IndexGe) : Formalism.L2.SG.KappaOffDiagonal.DimFormC :=
  dimFormC_of_steps orbitCount hT kuStab hB hI

end PI.UnitaryDimensionFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DualBetaReferenceCongruence
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section LeviMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem resT_of_mem (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E) :
    resT TR v z = TR.res v ⟨z, hz⟩ := by
  unfold resT; rw [dite_eq_left hz]

theorem res_eq_zero_of_Z (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E)
    (hZ : ZMod' X.B.I X.B.g z) : TR.res v ⟨z, hz⟩ = 0 :=
  (TR.res_ker ⟨z, hz⟩).2 (Z_smul X.B.I X.B.g X.ew_int hZ) v

def PhiSub (x : X.B.I.Gf) (i : Fin D.R.k) : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {z | ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
    ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z)}
  add_mem' {z w} hz hw := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w) =
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) +
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w) := by
      simp only [Matrix.mulVec_add, hA_add_right, mul_add, Finset.sum_add_distrib]; ring
    rw [e]; exact Z_add X.B.I X.B.g hz hw
  zero_mem' := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ 0) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) 0)
    have h0 : ∀ u : VA X.B.I, hA X.B.I u 0 = 0 := fun u => (hL X.B.I u).map_zero
    simp only [Matrix.mulVec_zero, h0, mul_zero, Finset.sum_const_zero, sub_zero]
    exact Z_zero X.B.I X.B.g
  smul_mem' c z hz := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) := by
      simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]; exact Z_smul X.B.I X.B.g c.2 hz

theorem dual_beta_reference_congruence (i : Fin D.R.k) (a : Fin D.R.rS) : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.e0 a)) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 a).2.2.1

theorem leviM_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset)
    (hyb : ∀ j, X.B.I.fmat y *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw))
    (hxe : ∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v := by
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1

  have key : ∀ i, Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) ≤ PhiSub x i := by
    intro i
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro z (⟨a, rfl⟩ | ⟨m, rfl⟩)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.e0 a) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.e0 a))
        refine Z_sub X.B.I X.B.g ?_ (Z_sum X.B.I X.B.g _ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (dual_beta_reference_congruence l a))
        have hQ : Mo X.B.I X.B.g (Set.range X.e0) ≤ Qs X.B.I X.B.g (X.bwd i) :=
          sup_le (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact dual_beta_reference_congruence i b)) (mL_Qs X.B.I X.B.g (hbwd i))
        exact hQ (hxe a)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m))
        have hw : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) = X.ew * hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) := by
          conv_lhs => rw [X.bw_w m, Matrix.mulVec_smul, hA_smul_right]
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m) =
            (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) *
              (hA X.B.I (X.bwd l) (X.bw m) - if l = m then X.ew else 0) := by
          simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          ring
        have e2 : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew = 0 := by
          rw [hw]
          have := X.ew_idem
          linear_combination (-(hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m))) * this
        rw [e, e2, zero_sub]
        have := Z_sum X.B.I X.B.g Finset.univ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (X.bw_dual l m)
        obtain ⟨t, ht, htt⟩ := this
        exact ⟨-t, neg_mem ht, by rw [htt]; ring⟩
    · rintro _ ⟨w, hw, rfl⟩
      show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w))
      refine ⟨hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w, ?_, ?_⟩
      · exact sub_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx hw)) (sum_mem fun l _ =>
          mul_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (hA_int X.B.I (hbwd l) hw))
      · simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
  ext i j
  have hxy : X.B.I.fmat (x * y) *ᵥ X.bw j = X.B.I.fmat x *ᵥ (X.B.I.fmat y *ᵥ X.bw j) := by
    rw [fmat_mul, Matrix.mulVec_mulVec]
  have hZ := key i (hyb j)
  simp only [PhiSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hZ
  rw [← hxy] at hZ

  have hI1 : hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    hA_int X.B.I (hbwd i) (K_mv X.B.I (K_mul X.B.I hx hy) (hbw j))
  have hI2 : ∀ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))
  have hI3 : ∀ l, hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd l) (K_mv X.B.I hy (hbw j))
  have hIs : ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈
      IntAf X.B.I.F X.B.I.E := sum_mem fun l _ => mul_mem (hI2 l) (hI3 l)
  have hD := res_eq_zero_of_Z TR v (sub_mem hI1 hIs) hZ
  simp only [leviM, Matrix.mul_apply]
  rw [resT_of_mem TR v hI1]
  simp only [resT_of_mem TR v (hI2 _), resT_of_mem TR v (hI3 _)]
  have e3 : (⟨hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j), hI1⟩ : IntAf X.B.I.F X.B.I.E) =
      ⟨_, sub_mem hI1 hIs⟩ + ∑ l, (⟨_, hI2 l⟩ : IntAf X.B.I.F X.B.I.E) * ⟨_, hI3 l⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e3, map_add (f := _), hD, zero_add, map_sum]
  simp only [map_mul]

end LeviMul

end PI.UnitaryDimensionFormula.NormCutK
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Transp
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem tr_repr_eq (y : (VS D).V) (i : Fin X.B.I.n) : X.bas.repr y i = X.ιE (X.crd y i) := by
  exact (X.ιE.apply_symm_apply (X.bas.repr y i)).symm

theorem tr_crd_injective : Function.Injective X.crd := by
  intro a b h
  apply X.bas.repr.injective
  ext i
  rw [tr_repr_eq X a i, tr_repr_eq X b i, h]

def trLin (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  Matrix.toLin X.bas X.bas (M.map X.ιE)

theorem tr_crd_lin (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (trLin X M y) = M *ᵥ X.crd y := by
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (Matrix.toLin X.bas X.bas (M.map X.ιE)) y
  rw [LinearMap.toMatrix_toLin] at h
  funext i
  apply X.ιE.injective
  rw [← tr_repr_eq]
  show X.bas.repr (Matrix.toLin X.bas X.bas (M.map X.ιE) y) i = _
  rw [← h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, tr_repr_eq]

theorem tr_lin_mul (M N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    (trLin X M).comp (trLin X N) = trLin X (M * N) := by
  have hm : (M * N).map X.ιE = M.map X.ιE * N.map X.ιE := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum, map_mul]
  unfold trLin
  rw [hm, Matrix.toLin_mul X.bas X.bas X.bas]

theorem tr_lin_one : trLin X 1 = LinearMap.id := by
  unfold trLin
  rw [Matrix.map_one _ (map_zero X.ιE) (map_one X.ιE), Matrix.toLin_one]

def trEquiv (M : GL (Fin X.B.I.n) X.B.I.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (trLin X (M : Matrix _ _ _)) (trLin X ((M⁻¹ : GL _ _) : Matrix _ _ _))
    (by rw [tr_lin_mul, Units.mul_inv, tr_lin_one])
    (by rw [tr_lin_mul, Units.inv_mul, tr_lin_one])

theorem tr_crd (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (trEquiv X M y) = (M : Matrix _ _ _) *ᵥ X.crd y := tr_crd_lin X _ y

theorem tr_af_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
  haveI : Nonempty (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := ⟨v⟩
  first
    | infer_instance
    | exact (RestrictedProduct.evalRingHom _ v).domain_nontrivial
    | exact ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x => x.1 v) h)⟩⟩

attribute [local instance] tr_af_nontrivial

theorem tr_star (a : X.B.I.E) : star (X.ιE a) = X.ιE (star a) :=
  (Formalism.BasicNotions.bridge_star_holds D.R D.host _).trans (X.ιE_conj a).symm

theorem tr_hT (x y : (VS D).V) :
    (VS D).hT x y = X.ιE (star (X.crd x) ⬝ᵥ (X.B.I.J *ᵥ X.crd y)) := by
  conv_lhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, tr_repr_eq, tr_star, ← X.J_eq, dotProduct, Matrix.mulVec,
    Pi.star_apply, map_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem tr_isom (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    trEquiv X M ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  have hM' : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hM
  have hH : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ =
      Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) := by
    ext i j
    rfl
  show ∀ a b, (VS D).hT (trEquiv X M a) (trEquiv X M b) = (VS D).hT a b
  intro a b
  rw [tr_hT, tr_hT, tr_crd, tr_crd]
  congr 1
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hH, hM']

theorem transport_holds : Transport := by
  intro D X u γ
  have hG : (γ : X.B.I.GA) ∈ X.B.I.GFset := (Subgroup.mem_inf.1 γ.2).1
  obtain ⟨M, hM, -, hf⟩ := hG
  have hH : ∀ y ∈ fixSet X u, X.B.I.fmat (iotaF X u γ : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y :=
    (iotaF X u γ).2
  have hcoe : ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl
  have hinc : ∀ v, X.B.I.fmat (γ : X.B.I.GA).2 *ᵥ incl X.B.I v =
      incl X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ v) := by
    intro v
    rw [hf]
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  have hfixc : ∀ y ∈ fixSet X u, (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y = y := by
    intro y hy
    have h1 := hH y hy
    rw [hcoe, hinc] at h1
    funext i
    exact Formalism.UG.P.inclE_injective _ _ _ (congrFun h1 i)
  have hfix : ∀ y, X.crd y ∈ fixSet X u → trEquiv X M y = y := by
    intro y hy
    apply tr_crd_injective X
    rw [tr_crd, hfixc _ hy]
  refine ⟨trEquiv X M, ⟨tr_isom X M hM, fun j => ?_, ?_⟩, fun h => ?_⟩
  · show Submodule.map _ (Submodule.span _ _) = Submodule.span _ _
    rw [Submodule.map_span, Set.image_image, X.Fu_e]
    congr 1
    apply Set.image_congr
    intro a _
    exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
  · rw [X.flagZVector]
    exact hfix _ (Or.inr rfl)
  · ext y
    have key : X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) =
        incl X.B.I (X.crd ((trEquiv X M).symm y)) := by
      have e1 : incl X.B.I (X.crd y) =
          X.B.I.fmat (iotaF X u γ : X.B.I.Gf) *ᵥ incl X.B.I (X.crd ((trEquiv X M).symm y)) := by
        rw [hcoe, hinc, ← tr_crd, LinearEquiv.apply_symm_apply]
      rw [e1, Matrix.mulVec_mulVec]
      have e2 : X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ * X.B.I.fmat (iotaF X u γ : X.B.I.Gf) =
          X.B.I.fmat (((iotaF X u γ : X.B.I.Gf))⁻¹ * (iotaF X u γ : X.B.I.Gf)) := rfl
      rw [e2, inv_mul_cancel]
      exact Matrix.one_mulVec _
    have e : ((iotaF X u γ : X.B.I.Gf) * h * X.xu u)⁻¹ = (h * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf)⁻¹ := by
      group
    rw [LinearEquiv.image_eq_preimage_symm]
    simp only [latS, Set.mem_ofPred_eq, Set.mem_preimage]
    rw [e]
    have ef : X.B.I.fmat ((h * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf)⁻¹) =
        X.B.I.fmat (h * X.xu u)⁻¹ * X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ := rfl
    rw [ef, ← Matrix.mulVec_mulVec, key]

end PI.UnitaryDimensionFormula
end
end

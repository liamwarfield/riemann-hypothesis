module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineCharJumpOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.ConjugationSwap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRing
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwists
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwists
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.CrysCharJumps

open Classical

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l)

def HasJumps (χ : ↥(GK K) →* (↥(OL LL))ˣ) (f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ) : Prop :=
  Continuous (fun g => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ g : (↥LL.1)ˣ) : ↥LL.1)) ∧
    IsCrys (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) ∧
    ∀ τ b, multV (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) τ b = if b = f τ then 1 else 0

variable {P K LL}

theorem charL_val (χ : ↥(GK K) →* (↥(OL LL))ˣ) (g : ↥(GK K)) :
    ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ g : (↥LL.1)ˣ) : ↥LL.1) =
      algebraMap ↥(OL LL) ↥LL.1 ((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) := rfl

theorem isJumpV_of_multV_ne {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ) (h : multV (P.PD K) ρ τ b ≠ 0) :
    IsJumpV (P.PD K) ρ τ b := by
  intro he
  apply h
  unfold multV
  rw [he]
  simp

theorem hasJumps_one (hT : LocTied l P AI) : HasJumps P K LL 1 0 := by
  have hc : Continuous (fun g => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (1 : ↥(GK K) →* (↥(OL LL))ˣ) g : (↥LL.1)ˣ) : ↥LL.1)) := by
    simp only [charL_val, MonoidHom.one_apply, Units.val_one, map_one]
    exact continuous_const
  obtain ⟨h1, h2⟩ := GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero l P AI hT K LL (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) 1) hc
    (fun g _ => by ext; simp [charL_val])
  exact ⟨hc, h1, fun τ b => by rw [h2]; rfl⟩

theorem hasJumps_mul (hT : LocTied l P AI) {χ ψ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f g : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) (hψ : HasJumps P K LL ψ g) :
    HasJumps P K LL (χ * ψ) (f + g) := by
  have htw : IsTwistRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)
      (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ)) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ))) := by
    refine ⟨LinearEquiv.refl _ _, fun x y => ?_⟩
    simp [charRep, charL_val, mul_smul]
  obtain ⟨hc, hm⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l P AI hT K LL ↥LL.1
    (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ)) ↥LL.1
    (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ))) (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ) htw hχ.2.1 hψ.2.1
  refine ⟨?_, hc, fun τ b => ?_⟩
  · have : (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ) x : (↥LL.1)ˣ) : ↥LL.1)) =
        fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ x : (↥LL.1)ˣ) : ↥LL.1) *
          ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ x : (↥LL.1)ˣ) : ↥LL.1) := by
      funext x
      simp [charL_val]
    rw [this]
    exact hχ.1.mul hψ.1
  · have hj : IsJumpV (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) τ (f τ) :=
      isJumpV_of_multV_ne _ τ (f τ) (by rw [hχ.2.2]; simp)
    have := hm τ (b - f τ) (f τ) hj
    rw [sub_add_cancel] at this
    rw [this, hψ.2.2]
    simp only [Pi.add_apply]
    split_ifs <;> omega

theorem hasJumps_inv (hT : LocTied l P AI) {χ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) :
    HasJumps P K LL χ⁻¹ (-f) := by
  have he : Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ⁻¹ = (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)⁻¹ := by
    refine MonoidHom.ext fun x => ?_
    simp only [Formalism.MainNotions.tableLineDegreeTwo.charL, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isCrys_inv_and_hodgeTate_jumps_neg l P AI hT K LL (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ) f hχ.2.1 hχ.2.2
  refine ⟨?_, he ▸ h1, fun τ b => by rw [he, h2]; rfl⟩
  have : (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ⁻¹ x : (↥LL.1)ˣ) : ↥LL.1)) =
      (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ x : (↥LL.1)ˣ) : ↥LL.1)) ∘ (fun x => x⁻¹) := by
    funext x
    simp only [Function.comp_apply, charL_val, MonoidHom.inv_apply, map_inv]
  rw [this]
  exact hχ.1.comp continuous_inv

theorem hasJumps_zpow (hT : LocTied l P AI) {χ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) (k : ℤ) :
    HasJumps P K LL (χ ^ k) (k • f) := by
  induction k using Int.induction_on with
  | zero =>
    rw [zpow_zero, zero_smul]
    exact hasJumps_one AI hT
  | succ k ih =>
    rw [zpow_add_one, add_smul, one_smul]
    exact hasJumps_mul AI hT ih hχ
  | pred k ih =>
    rw [zpow_sub_one, sub_smul, one_smul, sub_eq_add_neg]
    exact hasJumps_mul AI hT ih (hasJumps_inv AI hT hχ)

theorem hasJumps_prod (hT : LocTied l P AI)
    (ψ : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → (↥(GK K) →* (↥(OL LL))ˣ))
    (hψ : ∀ τ₀, HasJumps P K LL (ψ τ₀) (fun τ => if τ = τ₀ then 1 else 0))
    (c : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ) (s : Finset (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) :
    HasJumps P K LL (∏ τ ∈ s, ψ τ ^ c τ) (fun τ => if τ ∈ s then c τ else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    convert hasJumps_one AI hT using 1
    funext τ
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    convert hasJumps_mul AI hT (hasJumps_zpow AI hT (hψ a) (c a)) ih using 1
    funext τ
    by_cases h : τ = a
    · subst h
      simp [ha]
    · simp [h]

end GlobalTheory.CrysCharJumps


open GlobalTheory.CrysCharJumps Classical in
theorem GlobalTheory.CrysCharJumps.adm20_of_fonOf :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.tableLineDegreeTwo.adm20 D HW F := by
  intro D HW F l _ K LL hA
  refine ⟨fun a => ?_, ?_⟩
  · classical
    choose ψ hψ using fun τ₀ => GlobalTheory.T.exists_crystalline_char_jump_one_alt l (D.loc l) (D.locA l) (D.locT l) K LL hA τ₀
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    haveI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    let c : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ := fun τ =>
      if h : ∃ i, Formalism.MainNotions.tableLineDegreeTwo.Over ((HW l).W K 1 LL hA.2.2).emb i τ then a h.choose else 0
    have hp := hasJumps_prod (D.locA l) (D.locT l) ψ (fun τ₀ => hψ τ₀) c Finset.univ
    refine ⟨∏ τ, ψ τ ^ c τ, hp.1, hp.2.1, fun i τ hi b => ?_⟩
    rw [hp.2.2]
    have hex : ∃ i, Formalism.MainNotions.tableLineDegreeTwo.Over ((HW l).W K 1 LL hA.2.2).emb i τ := ⟨i, hi⟩
    have hc : c τ = a i := by
      simp only [c, dif_pos hex]
      congr 1
      apply ((HW l).W K 1 LL hA.2.2).emb_bij.1
      have h1 := hex.choose_spec
      unfold Formalism.MainNotions.tableLineDegreeTwo.Over at h1 hi
      exact h1.symm.trans hi
    simp [hc]
  · intro V _ _ _ _ _ _ _ ρ ρ' μ hρc hρ hμc hμI hρ'
    obtain ⟨hμcr, hμm⟩ := GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero l (D.loc l) (D.locA l) (D.locT l) K LL μ hμc hμI
    have htw : IsTwistRep μ ρ ρ' := ⟨LinearEquiv.refl _ _, fun g x => by simp [hρ' g]⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) (D.locT l) K LL
      V ρ V ρ' μ htw hμcr hρ
    refine ⟨h1, fun τ x => ?_⟩
    have hj : IsJumpV ((D.loc l).PD K) (charRep μ) τ 0 :=
      isJumpV_of_multV_ne _ τ 0 (by rw [hμm]; simp)
    simpa using h2 τ x 0 hj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwistsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.tableLineDegreeTwo.adm20 D HW F := by
  first | exact @GlobalTheory.CrysCharJumps.adm20_of_fonOf | exact GlobalTheory.CrysCharJumps.adm20_of_fonOf | (intros; apply GlobalTheory.CrysCharJumps.adm20_of_fonOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.ChiExtend

theorem placesOver_finite' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem maximalIdeal_le_comap {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) {O₀ O₁ : Type}
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[p] O₀] [Module.Finite ℤ_[p] O₀]
    [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra ℤ_[q] O₁] [Module.Finite ℤ_[q] O₁]
    (φ : O₀ →+* O₁) (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') :
    IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁) := by
  subst h
  have hc : φ.comp (algebraMap ℤ_[p] O₀) = algebraMap ℤ_[p] O₁ := by
    ext z
    exact hφ z z HEq.rfl
  haveI : (Ideal.comap φ (IsLocalRing.maximalIdeal O₁)).IsPrime := Ideal.comap_isPrime _ _
  have h1 : (Ideal.comap (algebraMap ℤ_[p] O₀) (Ideal.comap φ (IsLocalRing.maximalIdeal O₁))).IsMaximal := by
    rw [Ideal.comap_comap, hc]
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[p])
      (IsLocalRing.maximalIdeal O₁)
  have h2 := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := ℤ_[p]) (Ideal.comap φ (IsLocalRing.maximalIdeal O₁)) h1
  rw [IsLocalRing.eq_maximalIdeal h2]

theorem continuous_of_le_comap {O₀ O₁ : Type} [CommRing O₀] [IsLocalRing O₀] [TopologicalSpace O₀]
    [IsTopologicalRing O₀] [CommRing O₁] [IsLocalRing O₁] [TopologicalSpace O₁] [IsTopologicalRing O₁]
    (h₀ : IsAdic (IsLocalRing.maximalIdeal O₀)) (h₁ : IsAdic (IsLocalRing.maximalIdeal O₁))
    (φ : O₀ →+* O₁) (hφ : IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁)) :
    Continuous φ := by
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 h₁).2 s hs
  have ho := (isAdic_iff.1 h₀).1 n
  refine Filter.mem_map.2 <| Filter.mem_of_superset (ho.mem_nhds (Ideal.zero_mem _)) fun x hx => hn ?_
  exact (Ideal.pow_right_mono hφ n |>.trans (Ideal.le_comap_pow φ n)) hx

theorem cyc_heq (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q)
    (σ : G F Ω) : HEq ((cycZ F Ω p σ : ℤ_[p]ˣ) : ℤ_[p]) ((cycZ F Ω q σ : ℤ_[q]ˣ) : ℤ_[q]) := by
  subst h
  rfl

end GlobalTheory.ChiExtend

namespace GlobalTheory.ChiExtend

theorem iotaO_injective {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    Function.Injective (iotaO N A i) := by
  show Function.Injective (((A.iotaQC i).toRingHom.comp (A.iotaQ i)).comp (algebraMap (N.O i) (FractionRing (N.O i))))
  simp only [RingHom.coe_comp]
  exact (A.iotaQC i).injective.comp ((A.iotaQ i).injective.comp (IsFractionRing.injective _ _))

theorem eq_of_dense {X O : Type*} [TopologicalSpace X] [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (h : IsAdic (IsLocalRing.maximalIdeal O)) (hH : IsHausdorff (IsLocalRing.maximalIdeal O) O)
    {f g : X → O} (hf : Continuous f) (hg : Continuous g) {s : Set X} (hs : Dense s) (he : ∀ x ∈ s, f x = g x) :
    f = g := by
  funext x
  rw [← sub_eq_zero]
  apply hH.haus' (f x - g x)
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  have hcl : IsClosed ((fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O)) := by
    refine IsClosed.preimage (hf.sub hg) ?_
    exact AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ n).toAddSubgroup
      ((isAdic_iff.1 h).1 n)
  have hsub : s ⊆ (fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
    intro y hy
    simp only [Set.mem_preimage, he y hy, sub_self, SetLike.mem_coe]
    exact Ideal.zero_mem _
  have := closure_minimal hsub hcl
  rw [hs.closure_eq] at this
  exact this (Set.mem_univ x)

end GlobalTheory.ChiExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.IrrQuot

theorem exists_irreducible_smooth_quotient : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → Nontrivial V →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y),
      IsSmooth τ ∧ τ.IsIrreducible ∧ ∃ q : ρ.IntertwiningMap τ, Function.Surjective q := by
  intro G V _ _ _ _ _ ρ hsm hfl hnt
  haveI : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨M, hM, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  let W : Submodule ℂ V := M.toSubmodule
  have hW : ∀ g : G, W ≤ W.comap (ρ g) := fun g v hv => M.apply_mem_toSubmodule g hv
  let τ : Representation ℂ G (V ⧸ W) := ρ.quotient W hW
  have hτ : ∀ (g : G) (v : V), τ g (W.mkQ v) = W.mkQ (ρ g v) := fun g v => rfl
  let q : ρ.IntertwiningMap τ := ⟨W.mkQ, fun g => by ext v; rfl⟩
  have hq : Function.Surjective q := Submodule.mkQ_surjective W
  refine ⟨V ⧸ W, inferInstance, inferInstance, τ, ?_, ?_, q, hq⟩
  ·
    intro x
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
    let stab : (u : Type) → [AddCommGroup u] → [Module ℂ u] → (σ : Representation ℂ G u) → u → Subgroup G :=
      fun u _ _ σ y =>
        { carrier := {g | σ g y = y}
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq] at ha hb ⊢
            rw [map_mul, Module.End.mul_apply, hb, ha]
          one_mem' := by simp
          inv_mem' := by
            intro a ha
            simp only [Set.mem_setOf_eq] at ha ⊢
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hle : stab V ρ v ≤ stab (V ⧸ W) τ (W.mkQ v) := by
      intro g hg
      change τ g (W.mkQ v) = W.mkQ v
      rw [hτ]
      exact congrArg W.mkQ hg
    exact Subgroup.isOpen_mono hle (hsm v)
  ·
    have hMtop : M ≠ ⊤ := hM.1
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
    · intro h
      apply hMtop
      apply Subrepresentation.toSubmodule_injective
      apply eq_top_iff.2
      intro v _
      have hmem : W.mkQ v ∈ (⊤ : Subrepresentation τ).toSubmodule := Submodule.mem_top
      rw [← h] at hmem
      exact (Submodule.Quotient.mk_eq_zero W).1 ((Submodule.mem_bot ℂ).1 hmem)
    · intro S
      let T : Subrepresentation ρ := ⟨S.toSubmodule.comap W.mkQ, fun g v hv => by
        change W.mkQ (ρ g v) ∈ S.toSubmodule
        rw [← hτ]
        exact S.apply_mem_toSubmodule g hv⟩
      have hMT : M ≤ T := by
        intro v hv
        change W.mkQ v ∈ S.toSubmodule
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hv]
        exact S.toSubmodule.zero_mem
      rcases hM.le_iff.1 hMT with h | h
      · right
        apply Subrepresentation.toSubmodule_injective
        apply eq_top_iff.2
        intro x _
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
        have hvT : v ∈ T.toSubmodule := by rw [h]; exact Submodule.mem_top
        exact hvT
      · left
        apply Subrepresentation.toSubmodule_injective
        apply eq_bot_iff.2
        intro x hx
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
        have hvT : v ∈ T.toSubmodule := hx
        rw [h] at hvT
        exact (Submodule.mem_bot ℂ).2 (by rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero W).2 hvT)

end GlobalTheory.SmGL.IrrQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatib
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNeg
open NumberField

namespace GlobalTheory

theorem hwAt_conj_swap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) :=
  PI.UnitaryGroupMassFormula.HwConjInf.conjugation_swap

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNegStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) := by
  first | exact @GlobalTheory.hwAt_conj_swap | exact GlobalTheory.hwAt_conj_swap | (intros; apply GlobalTheory.hwAt_conj_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatib
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

noncomputable section

namespace GlobalTheory.WeightParamTie

open _root_.Formalism.L2

theorem paramV_half (R : Ranks) (h : HCParam R) (j : Fin R.m) :
    NG.paramV R h j (1 / 2) = (param h j).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) := by
  simp only [NG.paramV, param, run, Multiset.map_add (f := _), Multiset.map_map]
  congr 1
  · congr 1
    · refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]; push_cast; ring
    · refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]; push_cast; ring
  · refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply]; push_cast; ring

theorem infOf_neg_rev (n : ℕ) (lam : Fin n → ℤ) :
    NG.infOf (fun k => -lam (Fin.rev k)) = (NG.infOf lam).map Neg.neg := by
  have hu : (Finset.univ : Finset (Fin n)).val = Finset.univ.val.map Fin.rev := by
    conv_lhs => rw [← Finset.univ_map_equiv_to_embedding Fin.revPerm]
    rfl
  unfold NG.infOf
  conv_lhs => rw [hu]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Fin.rev_rev, Fin.val_rev]
  have hk : (k : ℕ) + 1 ≤ n := k.2
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem weightParam_of_levelTied : ∀ (D : D7) (M : Formalism.L2.MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E),
    Formalism.L2.LevelTied D M tup → (∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)}) →
    (∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ),
      (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam) → WeightParam D := by
  intro D M tup hL hEta hLoc i ρ
  set a := GlobalTheory.WtDual.dualWt (M.loc i).wt with ha
  have hd : (M.loc i).wt.IsDual a := GlobalTheory.WtDual.isDual_dualWt _
  obtain ⟨⟨lam, hlam, -⟩, -⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (embT D ρ)
  obtain ⟨⟨lam', hlam', -⟩, -⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (ComplexEmbedding.conjugate (embT D ρ))
  have huniq := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (embT D ρ)).1
  have hsw := GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg _ _ a (embT D ρ) lam' hlam'
  have heq : lam = fun k => -lam' (Fin.rev k) := huniq.unique hlam hsw
  have hlam'eq : lam' = fun k => -lam (Fin.rev k) := by
    funext k; rw [heq]; simp [Fin.rev_rev]
  have key : ∀ (k : ℕ) (hk : k = D.nd.j i) (h1 : 1 ≤ k) (h2 : k ≤ D.R.m),
      (M (D.nd.mu i) k h1 h2).wt = (M.loc i).wt := by
    intro k hk h1 h2; subst hk; rfl
  have hj : (liftIdx D i).1 + 1 = D.nd.j i := by
    have := D.nd.j_range i
    simp only [liftIdx]
    omega
  have hwt := hL.wt (D.nd.mu i) (liftIdx D i) ρ (1 / 2) a lam (hEta ρ)
    (by rw [key _ hj]; exact hd) hlam
  have hinf : D.naut.infWt i (embT D ρ) = (PP D i ρ).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) := by
    rw [hLoc i a _ lam hd hlam, hwt, paramV_half]
    rfl
  have e0 : embOver D ρ false = embT D ρ := rfl
  have e1 : embOver D ρ true = ComplexEmbedding.conjugate (embT D ρ) := by
    ext x
    rw [GlobalTheory.JumpDictionaryFoundation.embOver_true_apply, ComplexEmbedding.conjugate_coe_eq]
    rfl
  refine ⟨by rw [e0, hinf], ?_⟩
  rw [e1, hLoc i a _ lam' hd hlam', hlam'eq, infOf_neg_rev, ← hLoc i a _ lam hd hlam, hinf, Multiset.map_map]
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

end GlobalTheory.WeightParamTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatibStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible : ∀ (D : D7) (M : Formalism.L2.MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E), Formalism.L2.LevelTied D M tup → (∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)}) → (∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam) → WeightParam D := by
  first | exact @GlobalTheory.WeightParamTie.weightParam_of_levelTied | exact GlobalTheory.WeightParamTie.weightParam_of_levelTied | (intros; apply GlobalTheory.WeightParamTie.weightParam_of_levelTied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationality
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusGoodSplitPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusGoodSplitPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.FrobDense

theorem placesS_finite (D : D7) (l : ℕ) : (placesS D l).Finite := by
  have h0 := Formalism.L2.TwC.placesOver_finite' D.host.E (D.host.g 0) (D.host.g_prime 0).ne_zero
  have h1 := Formalism.L2.TwC.placesOver_finite' D.host.E (D.host.g 1) (D.host.g_prime 1).ne_zero
  have h2 := Formalism.L2.TwC.placesOver_finite' D.host.E (if l = D.host.pde then D.host.pde' else D.host.pde)
    (by split_ifs <;> first | exact D.host.pde'_prime.ne_zero | exact D.host.pde_prime.ne_zero)
  refine ((h0.union h1).union h2).subset ?_
  rintro v ⟨hv | hv | hv, -⟩
  · exact Or.inl (Or.inl hv)
  · exact Or.inl (Or.inr hv)
  · exact Or.inr hv

theorem frob_dense_goodSplit : ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)), l.Prime → GlobalTheory.RowTie.ChebSplit D.nd →
    Dense {σ : G D.host.E D.nd.Om | ∃ v : PlE D.host,
      (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ} := by
  intro D l Q hl hC
  have hfin : (placesOver D.host.E l ∪ placesS D l ∪ (Q : Set (PlE D.host))).Finite :=
    ((Formalism.L2.TwC.placesOver_finite' D.host.E l hl.ne_zero).union (placesS_finite D l)).union Q.finite_toSet
  refine (hC hfin.toFinset).mono ?_
  rintro σ ⟨w, hwS, hsp, B, hB, hF⟩
  have hw : w ∉ placesOver D.host.E l ∪ placesS D l ∪ (Q : Set (PlE D.host)) := by
    simpa using hwS
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hw
  exact ⟨w, ⟨hsp, hw.1.1, hw.1.2, hw.2⟩, B, hB, hF⟩

end GlobalTheory.FrobDense
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusGoodSplitPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_frobenius_goodSplitPlaces : ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)), l.Prime → GlobalTheory.RowTie.ChebSplit D.nd →
    Dense {σ : G D.host.E D.nd.Om | ∃ v : PlE D.host,
      (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ} := by
  first | exact @GlobalTheory.FrobDense.frob_dense_goodSplit | exact GlobalTheory.FrobDense.frob_dense_goodSplit | (intros; apply GlobalTheory.FrobDense.frob_dense_goodSplit <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LargeO

def sysPol (n : ℕ) {E : Type} [Field E] [NumberField E] (c : HeightOneSpectrum (𝓞 E) → ℕ → ℂ)
    (v : HeightOneSpectrum (𝓞 E)) : ℂ[X] :=
  X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((normV v : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c v k) * X ^ (n - k)

def BigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (Sf : Finset ℂ) : Prop :=
  ∀ c ∈ Es, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ Sf, ι.symm z ∈ K) →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar l),
      Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l))) → IsSSRep ρ →
      (∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) →
        ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B v →
          IsFrob (F := D.host.E) B (normV v) σ →
          ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)).charpoly.map ι.toRingHom = sysPol D.R.nV c v) →
      ∃ Pm : GL (Fin D.R.nV) (Qbar l), ∀ g s t,
        ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)) s t ∈ K

theorem bigOk_mono {D : D7} {l : ℕ} [Fact l.Prime] {Q : Finset (PlE D.host)} {Es : Set (PlE D.host → ℕ → ℂ)}
    {ι : Qbar l ≃+* ℂ} {Sf Sf' : Finset ℂ} (h : BigOk D l Q Es ι Sf) (hs : Sf ⊆ Sf') : BigOk D l Q Es ι Sf' :=
  fun c hc K hK => h c hc K fun z hz => hK z (hs hz)

theorem bigOk_cast {D : D7} {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (e : p = q) {Q : Finset (PlE D.host)}
    {Es : Set (PlE D.host → ℕ → ℂ)} {ι : Qbar p ≃+* ℂ} {Sf : Finset ℂ} (h : BigOk D p Q Es ι Sf) :
    BigOk D q Q Es (qCast e ι) Sf := by
  subst e; exact h

theorem exists_bigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (hE : Es.Finite) (hch : GlobalTheory.RowTie.ChebSplit D.nd) : ∃ Sf, BigOk D l Q Es ι Sf := by
  classical
  let Good : PlE D.host → Prop := fun v =>
    IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q
  let U : Set (G D.host.E D.nd.Om) := {σ | ∃ v, Good v ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ}
  have hU : Dense U := GlobalTheory.T.dense_frobenius_goodSplitPlaces D l Q (Fact.out) hch
  let p : (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X] := fun c σ =>
    if h : σ ∈ U then sysPol D.R.nV c (Classical.choose h) else 0
  have hS := fun c => GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys l ι D.host.E D.nd.Om D.R.nV U (p c) hU
  choose Sc hSc using hS
  refine ⟨hE.toFinset.biUnion Sc, ?_⟩
  intro c hc K hK ρ hcont hss hchar
  refine hSc c K (fun z hz => hK z (Finset.mem_biUnion.2 ⟨c, hE.mem_toFinset.2 hc, hz⟩)) ρ hcont hss ?_
  intro σ hσ
  simp only [p, dif_pos hσ]
  obtain ⟨hg, B, hB, hF⟩ := Classical.choose_spec hσ
  exact hchar _ hg B σ hB hF

theorem charpoly_pt : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))),
    SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (D.nd.l i) ∧
      v ∉ placesS D (D.nd.l i) ∧ v ∉ D.nd.Q i) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly.map (D.naut.iotaQC i).toRingHom =
        sysPol D.R.nV (ptSys D i x) v := by
  intro D i x ρ hρ v hv B σ hB hF
  have hso : SplitOut D.nd i v := ⟨hv.1, hv.2.1, fun h => hv.2.2.1 ((D.nd.S_def i v).1 h), hv.2.2.2⟩
  rw [hρ.2.2 v hso B σ hB hF, Polynomial.map_map]
  have hcomp : (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) = iotaOC D i := rfl
  rw [hcomp]
  unfold heckePol sysPol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  have hg : GenAt D (D.nd.l i) (D.nd.Q i) v k := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hk1, hk2⟩
  simp only [ptSys, if_pos hg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul,
    map_pow, map_neg, map_one, map_natCast, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_natCast]

theorem model_of_conj : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
    (a : ℕ) (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (P : GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ →
    (∀ g s t, ∃ x, A.iotaQ i x = ((P⁻¹ * ρ g * P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) →
    ∃ (r : G H.E N.Om →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))),
      ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ P hc hP
  let ρ' : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)) := (MulAut.conj P⁻¹).toMonoidHom.comp ρ
  have hρ' : ∀ g, ρ' g = P⁻¹ * ρ g * P := fun g => by
    simp [ρ', MulAut.conj_apply]
  have hc' : SumRepresentations.At.ContQ N i ρ' := by
    unfold SumRepresentations.At.ContQ at hc ⊢
    have e : (fun g => ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) =
        fun g => ((P⁻¹ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) * ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) *
          ((P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) := by
      funext g; rw [hρ']; rfl
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  obtain ⟨r, Pm, hr⟩ := GlobalTheory.T.exists_integral_model_rep_coeffRing N A i a ρ' hc' (fun g s t => by rw [hρ']; exact hP g s t)
  refine ⟨r, P * Pm, fun g => ?_⟩
  rw [hr g, hρ', mul_inv_rev]
  group

end GlobalTheory.LargeO
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfIsLocCompGL
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open scoped ContDiff

namespace GlobalTheory.DiscSMO

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a c N : ℕ} {n : Fin c → ℕ}
  {π π' : ∀ i, CuspSub E (n i)}


def prodForm (φ : ∀ i, (π i).V) : (∀ i, GA E (n i)) → ℂ := fun m => ∏ i, (φ i).1.1 (m i)

structure IsTensorOf (T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V) (Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)) : Prop where
  comm : ∀ i o φ, T i ((π i).op o φ) = (π' i).op o (T i φ)
  prod : ∀ φ, Θ (prodForm φ) = prodForm fun i => T i (φ i)

namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}

end IsTensorOf

variable {h : ∑ i, n i = N}




namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}

end IsTensorOf

theorem mem_Sm_of_one {f : GA E a → ℂ} (hf : ∀ g, ContDiffAt ℝ ∞ (chart f g) (oneL E a)) : f ∈ Sm E a := by
  rintro g x ⟨y, hy⟩
  obtain rfl : x = toL y.val := hy.symm
  have e : chart f g = chart f (g * infGL E a y) ∘ lmul (toL (y⁻¹).val) := by
    rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : lmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.inv_mul
  rw [e]
  refine (ContDiffAt.comp _ ?_ (lmul (toL (y⁻¹).val)).contDiff.contDiffAt).contDiffWithinAt
  rw [e1]
  exact hf _

theorem contDiffAt_chart_mul {f : GA E a → ℂ} {g : GA E a} {y : GL (Fin a) (Cinf E)}
    (hf : ContDiffAt ℝ ∞ (chart (fun x => f (x * infGL E a y)) g) (oneL E a)) :
    ContDiffAt ℝ ∞ (chart f (g * infGL E a y)) (oneL E a) := by
  have e : chart f g = chart (fun x => f (x * infGL E a y)) g ∘ rmul (toL (y⁻¹).val) := by
    rw [← chart_rt_inf]
    simp only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have e1 : rmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.mul_inv
  have e2 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  rw [chart_mul, e]
  refine ContDiffAt.comp _ ?_ (lmul (toL y.val)).contDiff.contDiffAt
  rw [e2]
  refine ContDiffAt.comp _ ?_ (rmul (toL (y⁻¹).val)).contDiff.contDiffAt
  rw [e1]
  exact hf


namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}


end IsTensorOf


end GlobalTheory.DiscSMO

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationUnitsMapEqOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.GLp.Supp

open GlobalTheory.SmGL GlobalTheory.PRep ValuativeRel

theorem valuation_units_map_eq_one {g : ℕ} [Fact g.Prime] (u : ℤ_[g]ˣ) :
    valuation ℚ_[g] ((Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u : ℚ_[g]ˣ) : ℚ_[g]) = 1 := by
  have hn : ‖((u : ℤ_[g]) : ℚ_[g])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.isUnit_iff.1 u.isUnit
  have e : ((Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u : ℚ_[g]ˣ) : ℚ_[g]) = ((u : ℤ_[g]) : ℚ_[g]) := rfl
  rw [e]
  refine le_antisymm (not_lt.1 fun hlt => ?_) (not_lt.1 fun hlt => ?_)
  · have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 ((u : ℤ_[g]) : ℚ_[g])).1 (by simpa using hlt)
    simp [hn] at this
  · have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff g ((u : ℤ_[g]) : ℚ_[g]) 1).1 (by simpa using hlt)
    simp [hn] at this

theorem mapsToProd_of_jac₂ : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ) (h : a + b = n) (V W W' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (φ : (GlobalTheory.SmGL.jac₂ (GlobalTheory.SmGL.stdSum h) π).IntertwiningMap (GlobalTheory.SmGL.extTensor σ ρ)), φ ≠ 0 →
    Supp.MapsToProd π σ ρ := by

  intro g _ a b n h V W W' _ _ _ _ _ _ π σ ρ φ hφ
  refine ⟨h.symm, absPow ℚ_[g] ((b : ℂ) / 2), absPow ℚ_[g] (-(a : ℂ) / 2),
    φ.toLinearMap ∘ₗ (twKer π (unipRad ℚ_[g] (two (stdSum h))) 1).mkQ, fun u => isUnram_absPow ℚ_[g] _ _ (valuation_units_map_eq_one u),
    fun u => isUnram_absPow ℚ_[g] _ _ (valuation_units_map_eq_one u), ?_, ?_⟩
  · intro hΛ
    apply hφ
    ext x
    exact LinearMap.congr_fun hΛ x
  · intro p x y h0 hx hy v
    have hp : p ∈ parab ℚ_[g] (two (stdSum h)) := by
      rw [mem_parab_iff]
      rintro (_|_) (_|_) i j hlt
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · apply h0
        · show ((stdSum h (Sum.inl j) : Fin n) : ℕ) < a
          rw [stdSum_inl]; exact j.isLt
        · show a ≤ ((stdSum h (Sum.inr i) : Fin n) : ℕ)
          rw [stdSum_inr]; omega
      · exact absurd hlt (by decide)
    have hl : leviProj ℚ_[g] (two (stdSum h)) ⟨p, hp⟩ = leviTwo ℚ_[g] (Fin a) (Fin b) (x, y) := by
      funext c
      cases c
      · refine Units.ext (Matrix.ext fun i j => ?_)
        rw [leviProj_apply]
        show _ = (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j
        have hi : (i : ℕ) < n := by omega
        have hj : (j : ℕ) < n := by omega
        rw [hx]
        simp only [Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
        rfl
      · refine Units.ext (Matrix.ext fun i j => ?_)
        rw [leviProj_apply]
        show _ = (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j
        have hi : a + (i : ℕ) < n := by omega
        have hj : a + (j : ℕ) < n := by omega
        rw [hy]
        simp only [Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
        rfl
    obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip ℚ_[g] (two (stdSum h)) ⟨p, hp⟩
    rw [hl] at hpu
    have hpu' : p = leviEmb ℚ_[g] (two (stdSum h)) (leviTwo ℚ_[g] (Fin a) (Fin b) (x, y)) * u := hpu
    have hmk : (Submodule.Quotient.mk (π u v) : Jacquet π (unipRad ℚ_[g] (two (stdSum h)))) = Submodule.Quotient.mk v := by
      rw [Submodule.Quotient.eq]
      refine Submodule.subset_span ⟨⟨u, hu⟩, v, ?_⟩
      simp
    have key : ∀ (M : Levi ℚ_[g] (Two (Fin a) (Fin b))) (w : V),
        (Submodule.Quotient.mk (π (leviEmb ℚ_[g] (two (stdSum h)) M) w) : Jacquet π (unipRad ℚ_[g] (two (stdSum h)))) =
          (deltaHalf ℚ_[g] (Two (Fin a) (Fin b)) M : ℂ) • GlobalTheory.SmGL.jac (two (stdSum h)) π M (Submodule.Quotient.mk w) := by
      intro M w
      rw [jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
    have hint := Representation.IntertwiningMap.isIntertwining _ _ φ (x, y) (Submodule.Quotient.mk v : Jacquet π (unipRad ℚ_[g] (two (stdSum h))))
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [hpu', map_mul, Module.End.mul_apply, key, hmk, map_smul]
    change _ • φ (jac₂ (stdSum h) π (x, y) (Submodule.Quotient.mk v)) = _
    rw [hint, deltaHalf_two]
    simp only [Fintype.card_fin]
    rfl

end GlobalTheory.GLp.Supp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuppFLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open _root_.Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SuppLocal

theorem suppF_local : ∀ (D : D7) (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (k : GA D V),
    IsPrimeIdem P e f → SuppF V f k → k ∈ GfC V ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ≠ P.under (𝓞 D.host.F) →
      GlobalTheory.FinZeta.projV V v k = 1 := by
  intro D V P e f k h hk
  obtain ⟨x, rfl⟩ := (GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem V h rfl k).1 hk
  exact ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC V _ x, fun v hv => GlobalTheory.AdelicU.proj_emb_ne _ _ hv x⟩

end GlobalTheory.SuppLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfJacquetMin
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacMinCusp

open GlobalTheory.SmGL.CuspMax Matrix
open scoped TensorProduct

theorem blk_two_stdSum {a b n : ℕ} (h : a + b = n) (i : Fin n) :
    blk (two (stdSum h)) i = decide (a ≤ (i : ℕ)) := by
  obtain ⟨x, rfl⟩ := (stdSum h).surjective i
  rcases x with x | x
  · rw [← two_false, blk_apply]; simp [x.2]
  · rw [← two_true, blk_apply]; simp

theorem blk_two_stdSum_lt {a b n : ℕ} (h : a + b = n) (i j : Fin n) :
    blk (two (stdSum h)) i < blk (two (stdSum h)) j ↔ (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : a ≤ (i : ℕ) <;> by_cases h2 : a ≤ (j : ℕ) <;> simp [h1, h2] <;> omega

theorem mem_unipRad_two_iff {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) {g : GL (Fin n) R} :
    g ∈ unipRad R (two (stdSum h)) ↔ ∀ i j : Fin n, ¬ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) →
      (g : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [mem_unipRad_iff_entries]
  simp only [blk_two_stdSum_lt]

end GlobalTheory.JacMinCusp
end

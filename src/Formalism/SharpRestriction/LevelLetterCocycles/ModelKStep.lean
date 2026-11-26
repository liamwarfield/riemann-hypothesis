module

public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.LevelLetterCocycles.MatOfEquiv
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalShareBounds

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def ExpL (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (ζ : LL) (x : LA W T π' c)
    (f : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  (∃ m₀ : ℤ, ∀ i < m₀, f i = 0) ∧ ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y ∧
    ∀ i, serMul (W.lev c ζ (Eπ ^ h')) f i = expS W T c ζ (fun j => (a j : LetA O n)) y i

abbrev QL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Type :=
  ↥(LamLA W T π' Eπ h' c ⊤) ⧸ (piNL W T Pt π' Eπ h' c 1).comap (LamLA W T π' Eπ h' c ⊤).subtype

def ModelL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M : ℕ) (c : ZMod n) : Prop :=
  NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ ∧
  (∀ x ∈ NL W T Pt π' Eπ h' c, γLA W T π' c x ∈ NL W T Pt π' Eπ h' c) ∧
  (∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c) ∧
  (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (Eπ ^ h')) ≤ NL W T Pt π' Eπ h' c ∧
  (∀ x ∈ LamLA W T π' Eπ h' c ⊤, ∀ k : ℕ, ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c →
    x ∈ NL W T Pt π' Eπ h' c) ∧
  JLA W T π' Eπ h' M c ≤ piNL W T Pt π' Eπ h' c M ∧
  ∀ x ∈ LamLA W T π' Eπ h' c ⊤, γLA W T π' c x - x ∈ NL W T Pt π' Eπ h' c →
    ∀ τ ζ, Pt c ζ τ → ∀ f, ExpL W T π' Eπ h' c ζ x f → ∀ i : ℤ, i ≠ 0 →
      f i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-i)

def ModelQ (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Prop :=
  Module.Finite O (QL W T Pt π' Eπ h' c) ∧
    ∀ (a : O) (q : QL W T Pt π' Eπ h' c), a ≠ 0 → a • q = 0 → q = 0

def ModelK {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (π' : LetA O n) (ρ : ℕ) (c : ZMod n) : Prop :=
  ∀ y ∈ NcS W T₂ (c - 1), ∃ x ∈ NcS W T₁ (c - 1), W.map F x - ((PD.p : ℕ) : O) ^ ρ • y ∈ PiNS W T₂ π' 1

end Local

section Record

def modelLR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, ModelL ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c

def modelQR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, ModelQ ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def modelKR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T₁.ρ →
      IsCrys ((D.loc l).PD K) T₂.ρ → F.Onto → (∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')) → ∀ c, ModelK ((HW l).W K 1 LL hG) F π' (rhoA l (eK K) h') c

end Record

def ModelLStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW

def ModelQStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelQR D HW

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section CoreW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem cancel_unit_mul_uniformizer_pow {w : (LetA O n)ˣ} {k : ℕ} {a b : LetA O n}
    (h : (w : LetA O n) * letπ ^ k * a = (w : LetA O n) * letπ ^ k * b) : a = b := by
  unfold letπ at h
  have h' : (fun _ => PowerSeries.X) ^ k * a = (fun _ => PowerSeries.X) ^ k * b := by
    have := congrArg (fun x => (↑w⁻¹ : LetA O n) * x) h
    simpa [← mul_assoc, Units.inv_mul] using this
  funext i
  have hi := congrFun h' i
  simp only [Pi.mul_apply, Pi.pow_apply] at hi
  ext m
  have hm := congrArg (PowerSeries.coeff (m + k)) hi
  rwa [mul_comm, PowerSeries.coeff_mul_X_pow, mul_comm, PowerSeries.coeff_mul_X_pow] at hm

theorem pi0Core_of (W : LocWach PD LL O v n) (w : (LetA O n)ˣ) (k : ℕ) (h1 : W.π₀ ∈ W.AΔ)
    (h3 : W.π₀ = (w : LetA O n) * letπ ^ k) : Pi0LatticeCondition W := by
  intro g
  obtain ⟨t, ht⟩ := Formalism.MainNotions.LiftingTheory.gamma_X_eq W g
  obtain ⟨Uc, hUc⟩ : ∃ Uc : LetA O n,
      Uc = fun _ => PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t := ⟨_, rfl⟩
  have hπ : W.γA g letπ = letπ * Uc := by
    funext i
    rw [hUc]
    show W.γ₀ g PowerSeries.X = PowerSeries.X * (PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t)
    exact ht
  obtain ⟨u, hu⟩ : ∃ u : LetA O n, u = (↑w⁻¹ : LetA O n) * W.γA g (w : LetA O n) * Uc ^ k :=
    ⟨_, rfl⟩
  have heq : W.γA g W.π₀ = W.π₀ * u := by
    rw [h3, map_mul, map_pow, hπ, hu,
      show (↑w : LetA O n) * letπ ^ k * (↑w⁻¹ * W.γA g ↑w * Uc ^ k) =
        (↑w * ↑w⁻¹) * (W.γA g ↑w * (letπ * Uc) ^ k) by ring,
      Units.mul_inv, one_mul]
  refine ⟨u, ?_, heq⟩
  have hmem : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := h1
  show ∀ δ ∈ W.DelF, W.γA δ u = u
  intro δ hδ
  have e1 : W.γA δ (W.γA g W.π₀) = W.γA g W.π₀ := by
    rw [Formalism.MainNotions.LiftingTheory.gammaA_comm W δ g, hmem δ hδ]
  rw [heq, map_mul, hmem δ hδ, h3] at e1
  exact cancel_unit_mul_uniformizer_pow e1

end CoreW

theorem finrank_K0_eq_one_of_le_Kur {l : ℕ} [Fact l.Prime] {K : FinExt l} (hK : K.1 ≤ MaximalUnramifiedExtension l) :
    Module.finrank ↥(K0 K) ↥K.1 = 1 := by
  unfold K0
  rw [finrank_eq_one_iff_of_nonzero' (1 : ↥K.1) one_ne_zero]
  intro x
  refine ⟨⟨(x : Om l), IntermediateField.mem_inf.mpr ⟨x.2, hK x.2⟩⟩, ?_⟩
  first
    | exact Subtype.ext (mul_one _)
    | exact Subtype.ext (by simp)
    | rfl

theorem ring_condition_uniformizer_polynomial (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL h.2.2) 1 (((D.loc l).PD K).p - 1) ((HW l).W K 1 LL h.2.2).π₀
      (fun _ => Polynomial.X + Polynomial.C ((((D.loc l).PD K).p : ℕ) : ↥(OL LL))) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h9W := h9 l K 1 LL h.2.2
  have hp := h9W _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL h.2.2))
  refine ((hp ?_ ?_).2.2 ?_).1
  · exact (HW l).W_s K 1 LL h.2.2
  · rw [(D.loc l).PD_p K]
    exact h.2.1
  · exact finrank_K0_eq_one_of_le_Kur h.1

theorem gamma_uniformizer_divisible_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : UniformiserGammaTheorem D HW F := by
  intro h9 l _ K LL h _
  obtain ⟨h1, -, ⟨w, hw⟩, -⟩ := ring_condition_uniformizer_polynomial D HW F h9 l K LL h
  exact pi0Core_of _ w _ h1 hw

end Formalism.MainNotions.UnusedSlot80
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.UnusedSlot80.BCW

variable {l : ℕ} [Fact l.Prime]

theorem OL_le {LL LL' : FinExt l} (hLL : LL.1 ≤ LL'.1) (x : ↥(OL LL)) :
    IntermediateField.inclusion hLL (x : ↥LL.1) ∈ OL LL' := by
  obtain ⟨p, hp, hx⟩ := x.2
  exact ⟨p, hp, by
    have := congrArg (IntermediateField.inclusion hLL) hx
    rw [map_zero] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
    rfl⟩

def jO {LL LL' : FinExt l} (hLL : LL.1 ≤ LL'.1) : ↥(OL LL) →+* ↥(OL LL') where
  toFun x := ⟨IntermediateField.inclusion hLL (x : ↥LL.1), OL_le hLL x⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem isFrac_OL (LL : FinExt l) : IsFractionRing ↥(OL LL) ↥LL.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  exact IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)

end Formalism.MainNotions.UnusedSlot80.BCF
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LemCStep
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def LemC (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n) : Prop :=
  ∀ x (hx : x ∈ NcS W T (c - 1)), (∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true →
    x ∈ FilL W T Pt c τ (b τ)) → ∀ f, IsCoord W Pt π' Eπ h' S up b c f →
    f ⊗ₜ mkL W T π' c x hx ∈ InvL W T Pt π' Eπ h' c ⊤

end Local

section Record

end Record

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.StmtLocFOfCountsAll
noncomputable section

namespace Formalism.MainNotions.N.LocalShareBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Polynomial Filter Topology

theorem sum_pi_single {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] (S0 : Finset α)
    (w : ι → α → ℝ) (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a ∈ S0, w i a ≤ 1) (v : ι) (P : α → Prop)
    [DecidablePred P] :
    ∑ t ∈ Fintype.piFinset (fun _ : ι => S0), (if P (t v) then ∏ i, w i (t i) else 0) ≤
      ∑ a ∈ S0.filter P, w v a := by
  set h : ι → α → ℝ := fun i a => if i = v then (if P a then w i a else 0) else w i a with hh
  have hpt : ∀ t : ι → α, (if P (t v) then ∏ i, w i (t i) else 0) = ∏ i, h i (t i) := by
    intro t
    by_cases hp : P (t v)
    · rw [if_pos hp]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i = v
      · subst hi; simp [hh, hp]
      · simp [hh, hi]
    · rw [if_neg hp]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hh, hp])
  rw [Finset.sum_congr rfl fun t _ => hpt t, ← Finset.prod_univ_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  have hv : ∑ a ∈ S0, h v a = ∑ a ∈ S0.filter P, w v a := by
    rw [Finset.sum_filter]; simp [hh]
  have hX : 0 ≤ ∑ a ∈ S0.filter P, w v a := Finset.sum_nonneg fun a _ => hw0 v a
  have hY : ∏ i ∈ Finset.univ.erase v, ∑ a ∈ S0, h i a ≤ 1 := by
    refine Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun a _ => ?_) fun i hi => ?_
    · simp only [hh]; split_ifs <;> first | exact hw0 _ _ | exact le_rfl
    · have hne : i ≠ v := Finset.ne_of_mem_erase hi
      simp only [hh, if_neg hne]
      exact hw1 i
  rw [hv]
  calc (∑ a ∈ S0.filter P, w v a) * ∏ i ∈ Finset.univ.erase v, ∑ a ∈ S0, h i a
      ≤ (∑ a ∈ S0.filter P, w v a) * 1 := mul_le_mul_of_nonneg_left hY hX
    _ = ∑ a ∈ S0.filter P, w v a := mul_one _

variable (D : D7)

variable {D}


end Formalism.MainNotions.N.LocalShareBounds
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ClassMapStep
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def InvLiftStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → invLiftR D HW

def ClassMapStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → classMapR D HW

def FrameStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → frameR D HW

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def B1 (l h η S : ℕ) : ℝ :=
  (2 * (aN l (h + η) : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) + lam l (h + η)

def B2 (l h η : ℕ) : ℝ := 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + 2

theorem bound_sum_eq (l h η S : ℕ) : B1 l h η S + B2 l h η = cocyclesToWachVectorsExponent l h η S := by
  unfold B1 B2 cocyclesToWachVectorsExponent; ring

def uOf (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N s₁ : ℕ) {FF : Type} [AddCommGroup FF]
    [Module O FF] (μ ms : ZMod n → FF →ₗ[O] W.DD T) (c : ZMod n) (f : FF) : W.DD T :=
  ((PD.p : ℕ) : O) ^ N • ms c f - ((PD.p : ℕ) : O) ^ s₁ • μ c f

def Step1Out [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d a N s₁ : ℕ) {FF : Type}
    [AddCommGroup FF] [Module O FF] (z : FF →ₗ[O] W.DD T) (μ : ZMod n → FF →ₗ[O] W.DD T)
    (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T) : Prop :=
  ∀ c ∈ evens n d, ∀ f : FF,
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (ms c f) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1
      (((PD.p : ℕ) : O) ^ s₁ • ((letE c : LetA O n) • z f) + (W.γ T (ms c f) - ms c f)) ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ a • uOf W T N s₁ μ ms c f ∈ W.N T ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (W.γ T (uOf W T N s₁ μ ms c f) - uOf W T N s₁ μ ms c f) ∧
    (f ∈ F₁ → uOf W T N s₁ μ ms c f ∈ W.N T)

def Step1 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ s₁ : ℕ, (s₁ : ℝ) ≤ B1 PD.p (hpar n b S) η S ∧
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∃ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) ⊤ F₁
          (evens n d).card 0 ∧
        (m = 0 → F₁ = ⊤) ∧
        Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms

def Step2 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ sg : ℕ, (sg : ℝ) ≤ B2 PD.p (hpar n b S) η ∧
    ∀ (s₁ : ℕ) (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∀ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
      Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms →
      ∃ (F₂ : Submodule O FF) (w : ZMod n → ↥F₂ →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) F₁ F₂
          (evens n d).card 0 ∧
        (m = 0 → F₂ = F₁) ∧
        (∀ c ∈ evens n d, ∀ f : ↥F₂, QPowSmulMemPullback W T₂ c η (w c f)) ∧
        ∀ f : ↥F₂, ∃ κ : ZMod n → G → T₂.V,
          (∀ c ∈ evens n d, RhoCoc W T₂ c (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (hpar n b S)) η
            (sigC PD.p (hpar n b S) η) (w c f) (κ c)) ∧
          (((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) - (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L ∨
            ((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) + (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L)

theorem cocyclesToWachVectorsBound_of_extTool [NeZero n] (W : LocWach PD LL O v n) (hE : Sh.ExtTool W) (h1 : Step1 W)
    (h2 : Step2 W) : CocyclesToWachVectorsBound W := by
  intro d T₁ T₂ F b S η m hS
  obtain ⟨s₁, hs₁, H1⟩ := h1 d T₁ T₂ F b S η m hS
  obtain ⟨sg, hsg, H2⟩ := h2 d T₁ T₂ F b S η m hS
  refine ⟨s₁ + sg, ?_, ?_⟩
  · have := bound_sum_eq PD.p (hpar n b S) η S
    push_cast
    linarith
  · intro FF _ _ _ _ g
    obtain ⟨N, y, z, μ, ν, hX⟩ := hE d T₁ T₂ F b S η m hS FF g
    obtain ⟨F₁, ms, hc1, hm1, ho⟩ := H1 FF g N y z μ ν hX
    obtain ⟨F₂, w, hc2, hm2, h36, hid⟩ := H2 s₁ FF g N y z μ ν hX F₁ ms ho
    refine ⟨F₂, w, ?_, ?_, h36, hid⟩
    · have hn : Even n := hS.2.2.1
      have := two_mul_card_evens_le hn d
      exact (hc1.trans hc2).mono (by omega) le_rfl
    · intro h0
      rw [hm2 h0, hm1 h0]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FirstFrameStepImplication
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def KapPiStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → kapPiR D HW

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.UniformizerMemDeltaInvariants
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

section Setup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem qp_mem (hπ : W.π₀ ∈ W.AΔ) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
  show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
  exact add_mem hπ (Subalgebra.natCast_mem _ _)

def QhP (i : ZMod n) (h : ℕ) : Submodule O (W.DD T) :=
  (PhiPullΔ W T i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))

private lemma exists_pow_eq_one_mul {Γ : Type} [CommGroup Γ] {a b : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1)
    (hb : ∃ k : ℕ, 0 < k ∧ b ^ k = 1) : ∃ k : ℕ, 0 < k ∧ (a * b) ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  obtain ⟨m, hm, hbm⟩ := hb
  refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbm, one_pow]

private lemma exists_pow_eq_one_inv {Γ : Type} [CommGroup Γ] {a : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1) :
    ∃ k : ℕ, 0 < k ∧ a⁻¹ ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

theorem uniformizer_mem_delta_invariants : W.π₀ ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀
  intro δ hδ
  have hδt := (W.DelF_def δ).1 hδ
  funext i
  show W.γ₀ δ W.π₀₁ = W.π₀₁
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.BasicNotions.LocWach.π₀₁, map_add (f := _), map_sub, map_one, map_natCast, map_sum]
  congr 1
  refine Finset.sum_equiv (Equiv.mulLeft δ) ?_ ?_
  · intro g
    simp only [Equiv.coe_mulLeft]
    rw [W.DelF_def g, W.DelF_def (δ * g)]
    constructor
    · exact fun hg => exists_pow_eq_one_mul hδt hg
    · intro hg
      have h2 := exists_pow_eq_one_mul (exists_pow_eq_one_inv hδt) hg
      rwa [inv_mul_cancel_left] at h2
  · intro g _
    simp only [Equiv.coe_mulLeft, map_mul, AlgHom.mul_apply]

end Setup

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def NinQbP [NeZero n] : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      x ∈ (PhiPullΔ W T₂ i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingInput
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def SecondPropositionHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → u2R D HW

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.TwGuard
noncomputable section

namespace Formalism.MainNotions

open NumberField IsDedekindDomain Formalism.BasicNotions

theorem vAdd_pos_iff_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : a ≠ 0) : 0 < vAdd la (a : K) ↔ a ∈ la.asIdeal := by
  have h0 : la.valuation K (a : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast ha
  have hle := la.valuation_le_one (K := K) a
  have hlt : la.valuation K (algebraMap (𝓞 K) K a) < 1 ↔ a ∈ la.asIdeal := la.valuation_lt_one_iff_mem a
  unfold vAdd
  constructor
  · intro h
    by_contra hm
    have h1 : la.valuation K (a : K) = 1 := le_antisymm hle (not_lt.1 fun h' => hm (hlt.1 h'))
    rw [h1] at h
    simp at h
  · intro hm
    have h2 : la.valuation K (a : K) < 1 := hlt.2 hm
    have h3 := (WithZero.log_lt_log h0 one_ne_zero).2 h2
    simp at h3
    omega

end Formalism.MainNotions

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ZlWCbInjective
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem zl_WCb_injective : Function.Injective (algebraMap ℤ_[l] (WCb l)) := by
  change Function.Injective (zlW l (Cb l))
  unfold zlW
  rw [RingHom.coe_comp]
  exact (WittVector.map_injective _ (ZMod.castHom (dvd_refl l) (Cb l)).injective).comp
    (WittVector.equiv l).symm.injective

theorem zl_LL_injective (LL : FinExt l) : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, RingHom.coe_comp]
  exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])

instance tfLL (LL : FinExt l) : Module.IsTorsionFree ℤ_[l] ↥LL.1 :=
  Module.isTorsionFree_iff_algebraMap_injective.2 (zl_LL_injective LL)

theorem O_RW_injective (LL : FinExt l) : Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  have h := Algebra.TensorProduct.includeLeft_injective (R := ℤ_[l]) (A := ↥(OL LL)) (B := WCb l)
    (S := ↥(OL LL)) zl_WCb_injective
  convert h using 1
  funext x
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem oneT_inj_gen {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    Function.Injective (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) := by
  haveI : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  haveI : Module.Flat ↥(OL LL) ↥T.L.T := Module.Flat.of_free
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap ↥(OL LL) (RW LL)) (O_RW_injective LL)
  have h2 := h1.comp (TensorProduct.lid ↥(OL LL) ↥T.L.T).symm.injective
  convert h2 using 1
  funext t
  simp [Algebra.TensorProduct.one_def]

theorem oneInj_sit (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) : OneInj (sit LT HW l AI K s LL h) :=
  fun T => oneT_inj_gen (G := ↥(GK K)) LL T

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CompleteOfPow
noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.OL

open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

theorem complete_of_pow {R : Type*} [CommRing R] (J : Ideal R) {n : ℕ} (hn : 0 < n)
    (h : IsAdicComplete (J ^ n) R) : IsAdicComplete J R := by
  let : WithIdeal R := ⟨J⟩
  have hJ : IsAdic J := rfl
  have hJn : IsAdic (J ^ n) := is_ideal_adic_pow hJ hn
  rw [hJ.isAdicComplete_iff]
  exact hJn.isAdicComplete_iff.mp h

variable {l : ℕ} [Fact l.Prime]

theorem l_ne_zero (LL : FinExt l) : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
  intro h
  have h2 := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h
  simp only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

theorem l_not_unit (P : LocPrime l) (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  have h0 := Formalism.MainNotions.LiftingTheory.zl_v_unit P LL hu.unit
  have h1 := Formalism.MainNotions.LiftingTheory.zl_v_pow P LL 1
  rw [IsUnit.unit_spec, map_natCast] at h0
  rw [pow_one, h0] at h1
  exact absurd h1 (by simp)

theorem l_mem_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
  let := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 (l_not_unit P LL))

theorem OL_dvr (P : LocPrime l) (LL : FinExt l) : IsDiscreteValuationRing ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hded : IsDedekindDomain ↥(OL LL) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have hnf : ¬ IsField ↥(OL LL) := fun hf => by
    have hm := l_mem_max P LL
    rw [isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hm
    exact l_ne_zero LL hm
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 3).mpr hded

theorem OL_complete_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    IsAdicComplete (maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have := OL_dvr P LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hl0 : Ideal.span {((l : ℕ) : ↥(OL LL))} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact l_ne_zero LL
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hl0 hϖ
  have hC := Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  rw [he, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at hC
  refine complete_of_pow _ (n := e) (Nat.pos_of_ne_zero ?_) hC
  rintro rfl
  rw [pow_zero, Ideal.one_eq_top] at hC
  exact not_subsingleton _ hC.subsingleton

end Formalism.MainNotions.CrystallineLiftingInputs.OL
end
end

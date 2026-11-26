module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ClassMapPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3downPfFildRConst
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.WLocal
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDict

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
noncomputable section

namespace Formalism.MainNotions.N.Ln34.DescentValuation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct
open Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.UnivLinkPf

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u3downPf_map_NcS {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (h1 : IsCrys PD T₁.ρ)
    (h2 : IsCrys PD T₂.ρ) (c : ZMod n) {x : W.DD T₁} (hx : x ∈ NcS W T₁ c) : W.map F x ∈ NcS W T₂ c := by
  rw [mem_NcS] at hx ⊢
  exact ⟨W.map_N F h1 h2 x hx.1, univLinkPf_map_DelS W F hx.2.1, by rw [← map_letA_smul, hx.2.2]⟩

theorem u3downPf_mkL_eq (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) {x z : W.DD T}
    (hx : x ∈ NcS W T (c - 1)) (hz : z ∈ NcS W T (c - 1)) (r : O) (h : z - r • x ∈ PiNS W T π' 1) :
    mkL W T π' c z hz = r • mkL W T π' c x hx := by
  unfold mkL
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
  simpa using h

theorem u3downPf_core {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M σ S ρ : ℕ}
    {up : (K →ₐ[Qp] LL) → Bool} {b : (K →ₐ[Qp] LL) → ℕ} {c : ZMod n}
    {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hc1 : IsCrys PD T₁.ρ) (hc2 : IsCrys PD T₂.ρ)
    (hj1 : ∀ τ, JumpsInV PD T₁.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hj2 : ∀ τ, JumpsInV PD T₂.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hMF1 : ModelF W T₁ Pt π' Eπ h' M c α β) (hMF2 : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M)
    (hK : ModelK W F π' ρ c)
    (hC1 : ∀ x (hx : x ∈ NcS W T₁ (c - 1)) f, IsCoord W Pt π' Eπ h' S up b c f →
      f ⊗ₜ mkL W T₁ π' c x hx ∈ InvL W T₁ Pt π' Eπ h' c ⊤)
    (hC2 : ∀ x (hx : x ∈ NcS W T₂ (c - 1)) f, IsCoord W Pt π' Eπ h' S up b c f →
      f ⊗ₜ mkL W T₂ π' c x hx ∈ InvL W T₂ Pt π' Eπ h' c ⊤) :
    ThirdPropositionSlot W F Pt π' Eπ h' M S up b c ρ α := by
  intro f hf x hx _ h1 y hy hα
  obtain ⟨x₁, hx₁, hdiff⟩ := hK x hx
  have hyI : y ∈ InvS W T₂ π' Eπ h' 1 c := hMF2.2.2.2.1 _ h1 y hy hα (hC2 x hx f hf)
  have hI1 := hC1 x₁ hx₁ f hf
  have hL1 : f ⊗ₜ mkL W T₁ π' c x₁ hx₁ ∈ LamLA W T₁ π' Eπ h' c ⊤ := (Submodule.mem_inf.1 hI1).1
  obtain ⟨w₁, hw₁⟩ := Submodule.Quotient.mk_surjective _ (α T₁ ⟨_, hL1⟩)
  have hw₁I : (w₁ : W.DD T₁) ∈ InvS W T₁ π' Eπ h' 1 c := hMF1.2.2.2.1 _ hL1 w₁ w₁.2 hw₁.symm hI1
  have hmx : W.map F x₁ ∈ NcS W T₂ (c - 1) := u3downPf_map_NcS W F hc1 hc2 (c - 1) hx₁
  have hL2 : f ⊗ₜ mkL W T₂ π' c (W.map F x₁) hmx ∈ LamLA W T₂ π' Eπ h' c ⊤ :=
    (Submodule.mem_inf.1 (hC2 _ hmx f hf)).1
  have hy₂ : W.map F (w₁ : W.DD T₁) ∈ LamPS W T₂ Eπ h' c := univLinkPf_map_LamPS W F hc1 hc2 Eπ h' c w₁.2
  have hnat := (hfr.2 T₁ T₂ F hc1 hc2 hj1 hj2).1 _ hL1 _ hL2 _ w₁.2 hy₂
    ⟨1, fun _ => f, fun _ => x₁, fun _ => hx₁, fun _ => hmx, by simp, by simp⟩ hw₁.symm
  have heq : mkL W T₂ π' c (W.map F x₁) hmx = ((PD.p : ℕ) : O) ^ ρ • mkL W T₂ π' c x hx :=
    u3downPf_mkL_eq W T₂ π' c hx hmx _ hdiff
  have hsub : (⟨_, hL2⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) = ((PD.p : ℕ) : O) ^ ρ • ⟨_, h1⟩ :=
    Subtype.ext (by simp [heq, TensorProduct.tmul_smul])
  rw [hsub, map_smul, hα] at hnat
  have hJ : Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ ρ • (⟨y, hy⟩ : ↥(LamPS W T₂ Eπ h' c)) - ⟨_, hy₂⟩) =
      (0 : QLamP W T₂ π' Eπ h' M c) := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hnat
  have hP := univLinkPf_PiNS_anti W T₂ π' hM (univLinkPf_JP W T₂ hMF2 hM _ hJ)
  refine ⟨hyI, w₁, hw₁I, ?_⟩
  simpa using hP

theorem u3downPf_jumps (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (u : Bool) (bt S η h' : ℕ)
    (hj : JumpsInV PD T.ρ τ (deep u bt S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bt) (hbS : bt + S ≤ h') :
    JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
  intro a ha
  have h := hj a ha
  unfold deep at h
  split_ifs at h <;> simp only [Set.mem_union, Set.mem_Icc] at h ⊢ <;> omega

end Local

section Record

theorem u3downPf_sK_pos {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL) :
    1 ≤ sK l K := by
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl1 : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have he : 0 < eK K := by
    rcases Nat.eq_zero_or_pos (eK K) with h | h
    · rw [h, zero_dvd_iff] at hd; omega
    · exact h
  exact Nat.div_pos (Nat.le_of_dvd hl1 hd) he

theorem u3downPf_modelK_of_wKill (D : D7) (HW : HWOf D.loc) (hW : wKillR D HW) : modelKR D HW := by
  intro l _ hl K LL hG π' E hp T₁ T₂ F h' _ hc1 hc2 hon hj1 c y hy
  obtain ⟨x, hx, hxy⟩ := hW l hl K LL hG π' E hp T₁ T₂ F h' hc1 hc2 hon hj1 (c - 1) y hy
  exact ⟨x, hx, by rw [hxy, sub_self]; exact Submodule.zero_mem _⟩

theorem u3downPf_lemC_rec (D : D7) (HW : HWOf D.loc) (Fo : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW Fo) (h1 : adm1 D HW Fo Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (S η h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (hc : IsCrys ((D.loc l).PD K) T.ρ)
    (hj : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η))
    (hηb : ∀ τ, η < b τ)
    (hdown : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c → up τ = false) :
    LemC ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' S up b c := by
  intro x hx _ f hf
  obtain ⟨-, -, ⟨w, hw⟩, -, ⟨w', hw'⟩, -⟩ := hp
  have hprim : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    intro τ ζ hpt
    rw [(D.loc l).PD_p K]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  have hdown' : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → up τ = false := fun τ ζ hpt =>
    hdown τ (u3upPf_pt_over D HW hG c ζ τ hpt)
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hgk : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [(D.loc l).PD_p K]; exact hl)
  refine u3downPf_lemC ((HW l).W K 1 LL hG) T _ π' _ h' S up b c ?_ ?_ hdown' ?_ ?_ ?_ ?_ ?_ x hx f hf
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  · have hq := Formalism.MainNotions.LiftingTheory.liftb_q_unit ((HW l).W K 1 LL hG)
    rw [hw', map_mul] at hq
    exact isUnit_of_mul_isUnit_right hq
  · intro τ ζ hpt
    exact u3downPf_cc_π' _ c ζ (hprim τ ζ hpt) π' _ w hw
  · intro τ ζ hpt
    exact u3downPf_lev_E _ c ζ (hprim τ ζ hpt) _ w' hw'
  · intro τ ζ hpt
    refine ⟨algebraMap ↥(OL LL) ↥LL.1 (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)),
      (((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero),
      fun a => ?_⟩
    have hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
        (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1)) := by
      rw [hgk, Nat.cast_one, Nat.cast_one, ((HW l).W K 1 LL hG).gam_gen, hs, Nat.cast_one]
    have h1' : IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ 1) := by rw [pow_one]; exact hprim τ ζ hpt
    have := ((Cm l).C K 1 LL hG).tie.lev_Γ ((HW l).W K 1 LL hG).gamK c ζ ζ 1 1 h1' hv (by rw [pow_one]) a
    exact this
  · intro x' hx' τ ζ hpt
    exact u3downPf_valAt_fil _ T c ζ τ (((h1 l K 1 LL hG).2.2.2.1 T hc).2 c ζ τ hpt).2.1 x' hx'
  · intro τ ζ hpt a hJ
    have h := hj τ a hJ
    have hd := hdown' τ ζ hpt
    have hb := hηb τ
    unfold deep at h
    rw [if_neg (by simp [hd])] at h
    simp only [Set.mem_union, Set.mem_Icc] at h
    omega

theorem u3downPf_link (hW : WStep) : DownSlotOfModels := by
  intro D HW Fo Cm CA CB CK hA hMF l _ hl K LL hG π' E hp T₁ T₂ F S η m h' up b c α β hfr hN hdown
  obtain ⟨hc1, hc2, hon, hj1, hj2, hηb, hbS, hh', -, -⟩ := hN
  have hJ1 : ∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h') := fun τ =>
    u3downPf_jumps T₁ τ (up τ) (b τ) S η h' (hj1 τ) (hηb τ) (hbS τ)
  have hJ2 : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := fun τ =>
    u3downPf_jumps T₂ τ (up τ) (b τ) S η h' (hj2 τ) (hηb τ) (hbS τ)
  have hM : 1 ≤ MK l K h' :=
    Formalism.MainNotions.N.Ln34.ClassMapPf.classMapPf_MK_pos K h' hh' (u3downPf_sK_pos hl K LL hG)
  have hF' := hMF l hl K LL hG π' E hp h' hh' c α β hfr
  have hK' := u3downPf_modelK_of_wKill D HW (hW D HW Fo Cm CA CB CK hA) l hl K LL hG π' E hp
    T₁ T₂ F h' hh' hc1 hc2 hon hJ1 c
  refine u3downPf_core ((HW l).W K 1 LL hG) F hfr hc1 hc2 hJ1 hJ2 (hF' T₁ hc1 hJ1) (hF' T₂ hc2 hJ2)
    hM hK' ?_ ?_
  · intro x hx f hf
    exact u3downPf_lemC_rec D HW Fo Cm hA.1 hl K LL hG π' E hp T₁ S η h' up b c hc1 hj1 hηb hdown x hx
      (fun τ hτ hup => by simp [hdown τ hτ] at hup) f hf
  · intro x hx f hf
    exact u3downPf_lemC_rec D HW Fo Cm hA.1 hl K LL hG π' E hp T₂ S η h' up b c hc2 hj2 hηb hdown x hx
      (fun τ hτ hup => by simp [hdown τ hτ] at hup) f hf

end Record

theorem down_of_models : Formalism.MainNotions.N.Ln34.DownSlotOfModels := u3downPf_link Formalism.MainNotions.N.Ln34.w_pf

end Formalism.MainNotions.N.Ln34.DescentValuation
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfC
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Exp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem FilC_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (a + 1) ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
  exact sup_le_sup_right (ExtPf.extPf_fildR_succ_le PD T.ρ τ a) _

theorem FilC_anti (τ : K →ₐ[Qp] LL) : Antitone fun a => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a :=
  antitone_int_of_succ_le (fun a => FilC_succ_le T τ a)

theorem FilC_mono_shift (τ : K →ₐ[Qp] LL) (b : ℤ) :
    Monotone fun i : ℤ => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (b - i) :=
  fun i j hij => FilC_anti T τ (by omega : b - j ≤ b - i)

theorem FilC_top (τ : K →ₐ[Qp] LL) (hj : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (b : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ b ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  rcases le_or_gt (-(h' : ℤ)) b with hb | hb
  · exact FilC_anti T τ hb
  · have key : ∀ d : ℕ, FildR PD T.ρ τ (-(h' : ℤ) - (d : ℤ)) = FildR PD T.ρ τ (-(h' : ℤ)) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        rw [← ih]
        have hnj : ¬ IsJumpV PD T.ρ τ (-(h' : ℤ) - ((d + 1 : ℕ) : ℤ)) := fun hJ => by
          have := (hj _ hJ).1
          push_cast at this
          omega
        unfold IsJumpV at hnj
        rw [not_not] at hnj
        have e : -(h' : ℤ) - ((d + 1 : ℕ) : ℤ) + 1 = -(h' : ℤ) - (d : ℤ) := by push_cast; ring
        rw [e] at hnj
        exact hnj.symm
    have := key ((-(h' : ℤ) - b).toNat)
    rw [show -(h' : ℤ) - (((-(h' : ℤ) - b).toNat : ℕ) : ℤ) = b by omega] at this
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
    rw [this]

include W in
theorem p_ne_zero : (PD.p : LL) ≠ 0 := by
  intro h
  have := W.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

theorem pow_vanish (g : PowerSeries LL) (hg : PowerSeries.constantCoeff g = 0) (m : ℕ)
    (a : PowerSeries LL) : ∀ j < m, PowerSeries.coeff j (g ^ m * a) = 0 := by
  intro j hj
  have hX : (PowerSeries.X : PowerSeries LL) ∣ g := PowerSeries.X_dvd_iff.mpr hg
  obtain ⟨h, hh⟩ := pow_dvd_pow_of_dvd hX m
  rw [hh, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem pow_vanish' (g : PowerSeries LL) (hg : PowerSeries.constantCoeff g = 0) (m : ℕ) :
    ∀ j < m, PowerSeries.coeff j (g ^ m) = 0 := by
  intro j hj
  simpa using pow_vanish g hg m 1 j hj

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem levN_fil (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (x : ↥(W.N T)) (k : ℤ) :
    W.levN T c ζ x k ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k) := by
  rw [← levN_letE]
  exact (hp4.2 c ζ τ hPt).2.1 x k

theorem ιDi_le_top (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hj : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  rw [← (hp4.2 c ζ τ hPt).1.2]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, k, hk, rfl⟩
  exact FilC_top T h' τ hj _ (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hk⟩ k)).2

theorem valAt_mem (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    {x : W.DD T} (hx : x ∈ W.N T) : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c := by
  classical
  unfold valAt
  split_ifs with h
  · exact Submodule.smul_mem _ _ ((hp4.2 c ζ τ hPt).1.1 ⟨x, hx⟩ _ (Nat.find_spec h) _).1
  · exact Submodule.zero_mem _

theorem expS_mem (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ) {m : ℕ}
    (a : Fin m → LetA O n) (y : Fin m → W.DD T) (hy : ∀ j, y j ∈ W.N T) (i : ℤ) :
    expS W T c ζ a y i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c := by
  unfold expS serC
  refine Submodule.sum_mem _ fun j _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (valAt_mem W T c hp4 hPt (hy j))
  · exact Submodule.zero_mem _

theorem levE_zero (hs : W.s = 1) {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (ζ : LL) (hζ : ζ ^ PD.p = 1) (hζ1 : ζ ≠ 1) :
    PowerSeries.constantCoeff (W.lev c ζ Eπ) = 0 := by
  have h0 := (levQ_pt W hs c ζ hζ hζ1).1
  have hw : PowerSeries.constantCoeff (W.lev c ζ w') * PowerSeries.constantCoeff (W.lev c ζ w) = 1 := by
    rw [← map_mul, ← map_mul, hww, map_one, map_one]
  rw [hQ, map_mul, map_mul] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · rw [h, mul_zero] at hw
    exact absurd hw zero_ne_one
  · exact h

end Exp

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPhi
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O} (Bs : FramepfBas W T)

theorem framepf_nBasis : ∃ β : Module.Basis (Fin Bs.r) (LetA O n) ↥(W.N T),
    ∀ k, (β k : W.DD T) = Bs.b k := by
  let b' : Fin Bs.r → ↥(W.N T) := fun k => ⟨Bs.b k, (Bs.mem k).1⟩
  have hli : LinearIndependent (LetA O n) b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : (0 : W.DD T) = ∑ k, g k • Bs.b k := by
      have := congrArg (fun z : ↥(W.N T) => (z : W.DD T)) hg
      simpa [b'] using this.symm
    obtain ⟨a, -, hu⟩ := Bs.uniq 0 (W.N T).zero_mem
    have e := (hu g h1).trans (hu 0 (by simp)).symm
    intro k
    exact congrFun e k
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range b') := by
    intro x _
    obtain ⟨a, ha, -⟩ := Bs.uniq x x.2
    have : x = ∑ k, a k • b' k := Subtype.ext (by simpa [b'] using ha)
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

theorem framepf_ddBasis (hT : IsCrys PD T.ρ) :
    ∃ β : Module.Basis (Fin Bs.r) W.EE (W.DD T), ∀ k, β k = Bs.b k := by
  obtain ⟨β, hβ⟩ := framepf_nBasis Bs
  refine ⟨(Algebra.TensorProduct.basis W.EE β).map (W.N_base T hT).equiv, fun k => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, IsBaseChange.equiv_tmul, one_smul,
    Submodule.subtype_apply, hβ]

theorem framepf_φpull_coord {y : W.DD T}
    (hy : y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T)))) :
    ∃ a : Fin Bs.r → LetA O n, y = ∑ k, a k • W.φD T (Bs.b k) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨a, ha, -⟩ := Bs.uniq z hz
    refine ⟨fun k => W.φA (a k), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ha, map_sum]
    exact Finset.sum_congr rfl fun k _ => Formalism.MainNotions.LiftingTheory.wmap_φD_smul W T _ _
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hy
    exact ⟨a + a', by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul s x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨fun k => s * a k, by simp [Finset.smul_sum, mul_smul]⟩

theorem framepf_phiBasis (hT : IsCrys PD T.ρ) :
    ∃ β : Module.Basis (Fin Bs.r) W.EE (W.DD T), ∀ k, β k = W.φD T (Bs.b k) := by
  obtain ⟨β, hβ⟩ := framepf_ddBasis Bs hT
  have hli : LinearIndependent W.EE fun k => W.φD T (Bs.b k) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have := Formalism.MainNotions.LiftingTheory.phii_basis W T hT β g (by simpa only [hβ] using hg)
    exact congrFun this k
  have hN : ∀ m ∈ W.N T, m ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)) := by
    intro m hm
    obtain ⟨k, hk⟩ := W.N_φinv T m hm
    obtain ⟨a, ha⟩ := framepf_φpull_coord Bs hk
    have h2 : W.Q ^ k • m ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)) := by
      have e : W.Q ^ k • m = ∑ j, a j • W.φD T (Bs.b j) := ha
      rw [e]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← algebraMap_smul W.EE]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    rw [← algebraMap_smul W.EE, map_pow] at h2
    obtain ⟨u, hu⟩ := (Formalism.MainNotions.LiftingTheory.liftb_Q_unit W).pow k
    rw [← hu] at h2
    have h3 := Submodule.smul_mem _ ((u⁻¹ : W.EEˣ) : W.EE) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3
  have hsp : ⊤ ≤ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)) := by
    intro y _
    exact (W.N_base T hT).inductionOn y
      (fun m => hN m m.2) (fun e y hy => Submodule.smul_mem _ e hy)
      (fun y₁ y₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

theorem framepf_phi_uniq (hT : IsCrys PD T.ρ) {a a' : Fin Bs.r → LetA O n}
    (h : ∑ k, a k • W.φD T (Bs.b k) = ∑ k, a' k • W.φD T (Bs.b k)) : a = a' := by
  obtain ⟨β, hβ⟩ := framepf_phiBasis Bs hT
  have h0 : ∑ k, algebraMap (LetA O n) W.EE (a k - a' k) • β k = 0 := by
    simp only [algebraMap_smul, hβ, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have h1 := Fintype.linearIndependent_iff.1 β.linearIndependent _ h0
  funext k
  exact sub_eq_zero.1 (W.EE_inj ((h1 k).trans (map_zero _).symm))

theorem framepf_phi_coordΔ (hT : IsCrys PD T.ρ) (c : ZMod n) {y : W.DD T}
    (hy : y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))))
    (hΔ : ∀ δ ∈ W.DelF, W.γD T δ y = y) (hc : (letE c : LetA O n) • y = y) :
    ∃ a : Fin Bs.r → LetA O n, (∀ k, a k ∈ W.AΔ) ∧ (∀ k, (letE c : LetA O n) * a k = a k) ∧
      y = ∑ k, a k • W.φD T (Bs.b k) := by
  obtain ⟨a, ha⟩ := framepf_φpull_coord Bs hy
  refine ⟨a, fun k δ hδ => ?_, fun k => ?_, ha⟩
  · have e : ∑ j, W.γA δ (a j) • W.φD T (Bs.b j) = ∑ j, a j • W.φD T (Bs.b j) := by
      rw [← ha, ← hΔ δ hδ]
      set_option synthInstance.maxHeartbeats 100000 in
        conv_rhs => rw [ha, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ← W.φγ_comm, (Bs.mem j).2 δ hδ]
    exact congrFun (framepf_phi_uniq Bs hT e) k
  · have e : ∑ j, ((letE c : LetA O n) * a j) • W.φD T (Bs.b j) = ∑ j, a j • W.φD T (Bs.b j) := by
      rw [← ha, ← hc]
      conv_rhs => rw [ha, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    exact congrFun (framepf_phi_uniq Bs hT e) k

theorem framepf_φspan_le (i : ZMod n) : Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T i) ≤
    Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) :=
  Submodule.span_mono (Set.image_mono fun _ hx => Formalism.MainNotions.LiftingTheory.wmap_Nl_le W T i hx)

theorem framepf_Pc_coord (hT : IsCrys PD T.ρ) (c : ZMod n) (y : W.DD T) (hy : y ∈ PcS W T c) :
    ∃ a : Fin Bs.r → LetA O n, (∀ k, a k ∈ W.AΔ) ∧ (∀ k, (letE c : LetA O n) * a k = a k) ∧
      y = ∑ k, a k • W.φD T (Bs.b k) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  exact framepf_phi_coordΔ Bs hT c (framepf_φspan_le (c - 1) h1) ((mem_DelS W T y).1 h2)
    ((mem_letS W T c y).1 h3)

theorem framepf_mem_Pc (c : ZMod n) (a : Fin Bs.r → LetA O n) (ha : ∀ k, a k ∈ W.AΔ)
    (hc : ∀ k, (letE c : LetA O n) * a k = a k) : ∑ k, a k • W.φD T (Bs.b k) ∈ PcS W T c := by
  refine Submodule.sum_mem _ fun k _ => ⟨⟨?_, ?_⟩, ?_⟩
  · show a k • W.φD T (Bs.b k) ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))
    rw [← hc k, mul_comm, mul_smul, ← φD_letE]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨Bs.b k, (Bs.mem k).1, rfl⟩, rfl⟩)
  · show a k • W.φD T (Bs.b k) ∈ DelS W T
    rw [mem_DelS]
    intro δ hδ
    rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ← W.φγ_comm, (Bs.mem k).2 δ hδ, ha k δ hδ]
  · show a k • W.φD T (Bs.b k) ∈ letS W T c
    rw [mem_letS, smul_smul, hc k]

end Local

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfL
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)


open Classical in
def framepf_gco (x : ↥(NcS W T (c - 1))) : Fin Bs.r → PowerSeries O :=
  if h : ∃ g : Fin Bs.r → PowerSeries O, (x : W.DD T) = ∑ k, framepf_ι π' (c - 1) (g k) • Bs.b k
  then Classical.choose h else 0

include hπ0 hR2 in
theorem framepf_gco_spec (x : ↥(NcS W T (c - 1))) :
    (x : W.DD T) = ∑ k, framepf_ι π' (c - 1) (framepf_gco Bs π' c x k) • Bs.b k := by
  have h := framepf_coord Bs π' (c - 1) hπ0 hR2 x.2
  unfold framepf_gco
  rw [dite_eq_left h]
  exact Classical.choose_spec h

include hπ0 hΔπ hR2 γ0 in
theorem framepf_gco_eq (x : ↥(NcS W T (c - 1))) (g : Fin Bs.r → PowerSeries O)
    (hg : (x : W.DD T) = ∑ k, framepf_ι π' (c - 1) (g k) • Bs.b k) : framepf_gco Bs π' c x = g :=
  framepf_coord_uniq Bs π' (c - 1) hπ0 hΔπ hR2 γ0
    ((framepf_gco_spec Bs π' c hπ0 hR2 x).symm.trans hg)

include hπ0 in
theorem framepf_ι_C_mul (o : O) (g : PowerSeries O) :
    framepf_ι π' (c - 1) (PowerSeries.C o * g) = algebraMap O (LetA O n) o * framepf_ι π' (c - 1) g := by
  rw [framepf_ι_mul π' (c - 1) (hπ0 _), framepf_ι_C π' (c - 1) (hπ0 _), mul_comm (letE (c - 1)),
    mul_assoc, framepf_letE_ι π' (c - 1) hπ0]

def framepf_coordL : ↥(NcS W T (c - 1)) →ₗ[O] (Fin Bs.r → O) where
  toFun x := fun k => PowerSeries.constantCoeff (framepf_gco Bs π' c x k)
  map_add' x y := by
    have e : framepf_gco Bs π' c (x + y) = framepf_gco Bs π' c x + framepf_gco Bs π' c y := by
      apply framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0
      rw [Submodule.coe_add, framepf_gco_spec Bs π' c hπ0 hR2 x, framepf_gco_spec Bs π' c hπ0 hR2 y,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.add_apply, framepf_ι_add π' (c - 1) (hπ0 _), add_smul]
    funext k
    rw [e, Pi.add_apply, map_add (f := _)]
    rfl
  map_smul' o x := by
    have e : framepf_gco Bs π' c (o • x) = fun k => PowerSeries.C o * framepf_gco Bs π' c x k := by
      apply framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0
      rw [Submodule.coe_smul, framepf_gco_spec Bs π' c hπ0 hR2 x, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [framepf_ι_C_mul π' c hπ0, mul_smul, algebraMap_smul]
    funext k
    rw [e, map_mul, PowerSeries.constantCoeff_C]
    rfl

theorem framepf_coordL_apply (x : ↥(NcS W T (c - 1))) (k : Fin Bs.r) :
    framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0 x k = PowerSeries.constantCoeff (framepf_gco Bs π' c x k) := rfl

variable (hu : IsUnit (algebraMap (LetA O n) W.EE π'))


include hπ0 hΔπ hR2 γ0 hu in
theorem framepf_coordL_ker (x : ↥(NcS W T (c - 1))) :
    framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0 x = 0 ↔ (x : W.DD T) ∈ PiNS W T π' 1 := by
  have hx := framepf_gco_spec Bs π' c hπ0 hR2 x
  have hxc := (mem_NcS W T (c - 1) x).1 x.2
  constructor
  · intro h0
    have hX : ∀ k, ∃ hk : PowerSeries O, framepf_gco Bs π' c x k = PowerSeries.X * hk := by
      intro k
      have := congrFun h0 k
      rw [framepf_coordL_apply] at this
      exact PowerSeries.X_dvd_iff.2 this
    choose hk hhk using hX
    rw [mem_PiNS]
    refine ⟨⟨∑ k, framepf_ι π' (c - 1) (hk k) • Bs.b k,
      Submodule.sum_mem _ fun k _ => (W.N T).smul_mem _ (Bs.mem k).1, ?_⟩, hxc.2.1⟩
    rw [pow_one, hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hhk k, smul_smul, framepf_ι_mul π' (c - 1) (hπ0 _), framepf_ι_X π' (c - 1) (hπ0 _),
      mul_comm (letE (c - 1)) π', mul_assoc, framepf_letE_ι π' (c - 1) hπ0]
  · intro h
    obtain ⟨⟨d, hdN, hd⟩, -⟩ := (mem_PiNS W T π' 1 _).1 h
    rw [pow_one] at hd
    have hdc : d ∈ NcS W T (c - 1) := by
      rw [mem_NcS]
      refine ⟨hdN, fun δ hδ => ?_, ?_⟩
      · rw [← sub_eq_zero]
        apply gradNPf_tf W T π' hu
        rw [smul_sub, ← hΔπ δ hδ, ← gradNPf_γD_smul, hΔπ δ hδ, hd, hxc.2.1 δ hδ, sub_self]
      · rw [← sub_eq_zero]
        apply gradNPf_tf W T π' hu
        rw [smul_sub, smul_smul, mul_comm, ← smul_smul, hd, hxc.2.2, sub_self]
    have hdd := framepf_gco_spec Bs π' c hπ0 hR2 ⟨d, hdc⟩
    have e : framepf_gco Bs π' c x = fun k => PowerSeries.X * framepf_gco Bs π' c ⟨d, hdc⟩ k := by
      apply framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0
      rw [← hd]
      conv_lhs => rw [show d = ((⟨d, hdc⟩ : ↥(NcS W T (c - 1))) : W.DD T) from rfl, hdd]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, framepf_ι_mul π' (c - 1) (hπ0 _), framepf_ι_X π' (c - 1) (hπ0 _),
        mul_comm (letE (c - 1)) π', mul_assoc, framepf_letE_ι π' (c - 1) hπ0]
    funext k
    rw [framepf_coordL_apply, e]
    simp

include hπ0 hΔπ hR2 γ0 in
theorem framepf_coordL_surj : Function.Surjective (framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0) := by
  intro o
  have hmem : ∑ k, framepf_ι π' (c - 1) (PowerSeries.C (o k)) • Bs.b k ∈ NcS W T (c - 1) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [framepf_ι_C π' (c - 1) (hπ0 _), mul_comm, mul_smul, algebraMap_smul]
    exact (NcS W T (c - 1)).smul_mem _ (framepf_letE_mem Bs (c - 1) k)
  refine ⟨⟨_, hmem⟩, ?_⟩
  have e := framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0 ⟨_, hmem⟩ (fun k => PowerSeries.C (o k)) rfl
  funext k
  rw [framepf_coordL_apply, e, PowerSeries.constantCoeff_C]

def framepf_Lbas : LcQ W T π' c ≃ₗ[O] (Fin Bs.r → O) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_ker,
      framepf_coordL_ker Bs π' c hπ0 hΔπ hR2 γ0 hu])).trans
    (LinearMap.quotKerEquivOfSurjective _ (framepf_coordL_surj Bs π' c hπ0 hΔπ hR2 γ0))

theorem framepf_Lbas_mk (x : ↥(NcS W T (c - 1))) :
    framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu (Submodule.Quotient.mk x) =
      framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0 x := rfl

def framepf_hh (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) : LcQ W T π' c →ₗ[O] W.DD T :=
  (Fintype.linearCombination O (fun k => framepf_vec Bs π' (c - 1) H k)).comp
    (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu).toLinearMap

end Local

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfHyp
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem framepf_hyp_cc_subst {O : Type} [CommRing O] (p F : PowerSeries O)
    (hp : PowerSeries.constantCoeff p = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst p F) = PowerSeries.constantCoeff F := by
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hp
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const F]
  rw [PowerSeries.subst_add hS, PowerSeries.subst_mul hS, PowerSeries.subst_X hS, PowerSeries.subst_C,
    map_add, map_mul, hp, zero_mul, zero_add]
  exact PowerSeries.constantCoeff_C _

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem framepf_hyp_bas (π'₀ : LetA O n) (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π'₀) : Nonempty (FramepfBas W T) := by
  obtain ⟨⟨r, b, hb, huniq, hdel⟩, -⟩ := hm
  exact ⟨⟨r, b, hb, huniq, fun x hx => hdel x hx⟩⟩

theorem framepf_hyp_local (e s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n) (E : ZMod n → Polynomial O)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (π'₀ : LetA O n) (w₀ : (LetA O n)ˣ)
    (hw₀ : π'₀ = (w₀ : LetA O n) * letπ ^ s') (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π'₀) (c : ZMod n) :
    (∀ j, PowerSeries.constantCoeff (π' j) = 0) ∧ (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
    (∀ a ∈ W.AΔ, ∃! f : ZMod n → PowerSeries O, ∀ j, a j = PowerSeries.subst (π' j) (f j)) ∧
    (∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0) ∧
    IsUnit (algebraMap (LetA O n) W.EE π') ∧
    (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) ∧
    ∃ Fs : PowerSeries O, W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs) ∧
      PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s' := by
  obtain ⟨f, t, hf, -, hEE, hπΔ, hγN⟩ := exists_gam_pi_factor W T e s' hs π' E hR π'₀ w₀ hw₀ hm.2
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hfΔ := gradNPf_fΔ W s' w π' f hw hπΔ hf
  obtain ⟨Fs, hFs, -⟩ := hR.2.1 f hfΔ
  have hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0 := by
    intro j
    have : π' j = (w : LetA O n) j * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 (c - 1))
  have hγc : W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs (c - 1)) := by
    have h : (W.γA W.gam π') (c - 1) = (π' * f) (c - 1) := congrFun hf (c - 1)
    rw [PowerSeries.subst_mul hS, PowerSeries.subst_X hS, ← hFs (c - 1)]
    exact h
  have hcc : PowerSeries.constantCoeff (Fs (c - 1)) = ((W.χΓ W.gam : Oˣ) : O) ^ s' := by
    rw [← framepf_hyp_cc_subst (π' (c - 1)) (Fs (c - 1)) (hπ0 (c - 1)), ← hFs (c - 1)]
    exact gradNPf_cc_f W s' w π' f hw hf (c - 1)
  exact ⟨hπ0, hπΔ, fun a ha => hR.2.1 a ha, fun δ _ => (W.γ₀_X δ).1, hEE, hγN, Fs (c - 1), hγc, hcc⟩

end Local


set_option maxHeartbeats 1000000 in
theorem frame_uniformiser_unit_multiple (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys ((D.loc l).PD K) T.ρ) :
    ∃ (π'₀ : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (w₀ : (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))ˣ),
      π'₀ = (w₀ : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) * letπ ^ sK l K ∧
        Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters ((HW l).W K 1 LL hG) T π'₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, hr₀, hm₀⟩, -⟩ := h9W T hT hs1 hp
  rw [hpl] at hr₀
  obtain ⟨w₀, hw₀⟩ := hr₀.2.2.1
  exact ⟨π'₀, w₀, hw₀, hm₀⟩

theorem ramification_quotient_pos (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL) :
    1 ≤ sK l K := by
  have hd : eK K ∣ l - 1 := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl1 : 0 < l - 1 := by have := hpf.out.two_le; omega
  have he0 : 0 < eK K := Nat.pos_of_dvd_of_pos hd hl1
  exact (Nat.one_le_div_iff he0).mpr (Nat.le_of_dvd hl1 hd)


set_option maxHeartbeats 1000000 in
theorem framepf_hyp_arith (D : D7) (HW : HWOf D.loc) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (h' : ℕ) (hs : 1 ≤ sK l K) :
    (∀ y : ℕ, 1 ≤ y → (((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K) ^ y ≠ 1) ∧
      ∃ aσ : ↥(OL LL), (l : ↥(OL LL)) ^ sigA l (sK l K) h' =
        aσ * ∏ y ∈ Finset.Ico 1 (MK l K h'), ((((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K) ^ y - 1) := by
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hlO : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL))) = 1 := by
    rw [map_natCast]
    exact hlv
  have hxv : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL hG).gam_gen
    rw [hs1, Nat.cast_one] at this
    exact this
  obtain ⟨u, hu, hxu⟩ := gradNPf_sub_one ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv
    (l : ↥(OL LL)) _ hlO hxv
  have hsl : ¬ l ∣ sK l K := by
    apply Nat.not_dvd_of_pos_of_lt hs
    have h2 := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hprod := fun N => gradNPf_prod ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hl hlv _
    u hu hxu (sK l K) (by omega) hsl N
  refine ⟨?_, ?_⟩
  · intro y hy h
    obtain ⟨a, ha⟩ := hprod y
    rw [Finset.prod_eq_zero (i := y) (Finset.mem_Ico.2 ⟨hy, by omega⟩) (by rw [h, sub_self]),
      mul_zero] at ha
    have h2 := congrArg (algebraMap ↥(OL LL) ↥LL.1) ha
    rw [map_pow, map_natCast, map_zero] at h2
    have h3 : (l : ↥LL.1) = 0 := (pow_eq_zero_iff (by omega)).mp h2
    rw [h3, AddValuation.map_zero] at hlv
    exact absurd hlv (by simp)
  · obtain ⟨a, ha⟩ := hprod (MK l K h' - 1)
    refine ⟨a, ?_⟩
    have hσ : sigA l (sK l K) h' = MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial := rfl
    have hI : Finset.Ico 1 (MK l K h' - 1 + 1) = Finset.Ico 1 (MK l K h') := by
      rcases Nat.eq_zero_or_pos (MK l K h') with h0 | h0
      · rw [h0]; simp
      · congr 1; omega
    rw [hσ, ← hI]
    exact ha


set_option maxHeartbeats 1000000 in
theorem framepf_hyps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (h' : ℕ) :
    Nonempty (FramepfBas ((HW l).W K 1 LL hG) T) ∧
    (∀ j, PowerSeries.constantCoeff (π' j) = 0) ∧
    (∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ π' = π') ∧
    (∀ a ∈ ((HW l).W K 1 LL hG).AΔ, ∃! f : ZMod (finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL),
      ∀ j, a j = PowerSeries.subst (π' j) (f j)) ∧
    (∀ δ ∈ ((HW l).W K 1 LL hG).DelF,
      PowerSeries.constantCoeff (((HW l).W K 1 LL hG).γ₀ δ PowerSeries.X) = 0) ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
    (∀ y ∈ ((HW l).W K 1 LL hG).NΔ T, ∃ d ∈ ((HW l).W K 1 LL hG).N T,
      ((HW l).W K 1 LL hG).γD T ((HW l).W K 1 LL hG).gam y - y = π' • d) ∧
    ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
    ∃ Fs : PowerSeries ↥(OL LL),
      ((HW l).W K 1 LL hG).γ₀ ((HW l).W K 1 LL hG).gam (π' (c - 1)) =
        PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs) ∧
      PowerSeries.constantCoeff Fs =
        ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K ∧
      (∀ y : ℕ, 1 ≤ y →
        (((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K) ^ y ≠ 1) ∧
      ∃ aσ : ↥(OL LL), (l : ↥(OL LL)) ^ sigA l (sK l K) h' =
        aσ * ∏ y ∈ Finset.Ico 1 (MK l K h'),
          ((((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ^ sK l K) ^ y - 1) := by
  obtain ⟨π'₀, w₀, hw₀, hm₀⟩ := frame_uniformiser_unit_multiple D HW F Cm h1 l hl K LL hG T hT
  have hs := ramification_quotient_pos l hl K LL hG
  obtain ⟨hπ0, hπΔ, hsub, hX0, hEE, hγN, Fs, hγc, hcc⟩ :=
    framepf_hyp_local _ T (eK K) (sK l K) hs π' E hR π'₀ w₀ hw₀ hm₀ c
  obtain ⟨hne, hpr⟩ := framepf_hyp_arith D HW l hl K LL hG h' hs
  exact ⟨framepf_hyp_bas _ T π'₀ hm₀, hπ0, hπΔ, hsub, hX0, hEE, hγN,
    ((HW l).W K 1 LL hG).gamK_eq_one ((HW l).W_s K 1 LL hG) (by rw [(D.loc l).PD_p K]; exact hl),
    Fs, hγc, hcc, hne, hpr⟩

end Formalism.MainNotions.N.Ln34

end
end

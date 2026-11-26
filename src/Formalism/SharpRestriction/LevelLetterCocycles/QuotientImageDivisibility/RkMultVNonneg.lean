module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkFilLetter
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

open Formalism.BasicNotions

def boxM {n : ℕ} (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ℕ :=
  if (i.val + d) % 2 = 0 then b i + S else η

def boxH {n : ℕ} (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ℕ :=
  if (i.val + d) % 2 = 0 then η else b i + S

section Out

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable [NeZero n] (W : LocWach PD LL O v n)

theorem rk_eta_lt {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ}
    {S η m : ℕ} (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n) : η < b i := by
  obtain ⟨-, hp, -, -, -, -, -, -, hA, -⟩ := hS
  have h1 := hA i
  have hp' : (1 : ℝ) < (PD.p : ℝ) := by exact_mod_cast (show 1 < PD.p by omega)
  have hl : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.lam PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.lam
    rcases Nat.eq_zero_or_pos (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) with h | h
    · rw [h]
      simp
    · have hx : (1 : ℝ) ≤ 2 * ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      have := Real.logb_nonneg hp' hx
      linarith
  have hf : 0 ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg (Nat.cast_nonneg _)
    linarith
  have haR : 3 ≤ Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.aR
    linarith
  have : (η : ℝ) < (b i : ℝ) := by linarith
  exact_mod_cast this

theorem rk_win_box (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) (hη : η < b i) :
    Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i ⊆ Set.Icc (-(boxM d b S η i : ℤ)) (boxH d b S η i : ℤ) := by
  intro a ha
  unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
  unfold boxM boxH
  split_ifs at ha ⊢ with h
  · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> push_cast at h1 h2 ⊢ <;> omega
    · constructor <;> push_cast at h1 h2 ⊢ <;> omega
  · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> push_cast at h1 h2 ⊢ <;> omega
    · constructor <;> push_cast at h1 h2 ⊢ <;> omega

variable {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}

theorem rk_jumpsLet₁ (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) :
    Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₁ (boxM d b S η) (boxH d b S η) := by
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hJ, -, -, -⟩ := hS'
  intro τ i hτ a ha
  exact rk_win_box d b S η i (rk_eta_lt W hS i) (hJ i τ hτ a ha)

theorem rk_jumps₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n)
    (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ i) :
    JumpsInV PD T₂.ρ τ (Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i) := by
  obtain ⟨h1, h2, hon⟩ := hS.2.2.2.2.2.1
  intro a ha
  exact hS.2.2.2.2.2.2.1 i τ hτ a (rk_jump_of W hS.1.1 hE hC hQ F h1 h2 hon τ i hτ a ha)

theorem rk_jumpsLet₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) :
    Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (boxM d b S η) (boxH d b S η) := by
  intro τ i hτ a ha
  exact rk_win_box d b S η i (rk_eta_lt W hS i) (rk_jumps₂ W hE hC hQ hS i τ hτ a ha)

theorem rk_fd_letter₂ (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n) :
    FiniteDimensional LL ↥(DcrisL PD T₂.ρ (W.emb i)) := by
  have hS' := hS
  obtain ⟨-, -, -, -, -, ⟨-, hC2, -⟩, -, -, -, -⟩ := hS'
  haveI := T₂.fdim
  haveI := PD.finK₀
  have hle : DcrisL PD T₂.ρ (W.emb i) ≤ Dcris PD T₂.ρ := by
    unfold Formalism.WeaklyAdmissibleFiltrations.DcrisL
    exact inf_le_left
  suffices h : FiniteDimensional LL ↥(Dcris PD T₂.ρ) from
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  rcases Nat.eq_zero_or_pos (finrank LL T₂.V) with h0 | h0
  · haveI : Subsingleton T₂.V := Module.finrank_zero_iff.mp h0
    infer_instance
  · apply Module.finite_of_finrank_pos
    unfold Formalism.WeaklyAdmissibleFiltrations.IsCrys at hC2
    rw [hC2]
    exact Nat.mul_pos Module.finrank_pos h0

theorem rk_multV_nonneg (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD T.ρ τ)]
    (a : ℤ) : 0 ≤ multV PD T.ρ τ a := by
  have hle : FildR PD T.ρ τ (a + 1) ≤ FildR PD T.ρ τ a := by
    unfold Formalism.WeaklyAdmissibleFiltrations.FildR
    refine inf_le_inf_left _ ?_
    intro x hx
    unfold Formalism.WeaklyAdmissibleFiltrations.FilV at hx ⊢
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => exact LinearMap.mem_range.mpr ⟨v ⊗ₜ ⟨(f : BdR), PD.Fil_anti a f.2⟩, by simp⟩
    | add y z hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hy hz
  have h0 : FildR PD T.ρ τ a ≤ DdRE PD T.ρ τ := by
    unfold Formalism.WeaklyAdmissibleFiltrations.FildR
    exact inf_le_left
  haveI hfin : FiniteDimensional LL ↥(FildR PD T.ρ τ a) :=
    Module.Finite.of_injective (Submodule.inclusion h0) (Submodule.inclusion_injective h0)
  have hr : finrank LL ↥(FildR PD T.ρ τ (a + 1)) ≤ finrank LL ↥(FildR PD T.ρ τ a) :=
    LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hle)
  unfold Formalism.WeaklyAdmissibleFiltrations.multV
  omega

theorem rk_corank₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n)
    (hi : (i.val + d) % 2 = 1) :
    (finrank LL ↥(DcrisL PD T₂.ρ (W.emb i)) : ℤ) -
      finrank LL ↥(FilCris PD T₂.ρ (b i : ℤ) ⊓ DcrisL PD T₂.ρ (W.emb i)) ≤ m := by
  classical
  have hK := hS.1.1
  have h2 := hS.2.2.2.2.2.1.2.1
  obtain ⟨τ, hτ⟩ := rk_lift hK (W.emb i)
  have hwin := rk_jumps₂ W hE hC hQ hS i τ hτ
  have hsum := hS.2.2.2.2.2.2.2.1 i τ hτ
  obtain ⟨-, hτ'⟩ := hQ hK T₂.V T₂.ρ h2
  obtain ⟨hfd, -, hF⟩ := hτ' τ
  haveI := hfd
  have hrk : ∀ a : ℤ, finrank LL ↥(FilCris PD T₂.ρ a ⊓ DcrisL PD T₂.ρ (W.emb i)) =
      finrank LL ↥(FildR PD T₂.ρ τ a) := fun a => by
    rw [hF a, hτ]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rk_ιV_inj PD) _)
  have hD : finrank LL ↥(DcrisL PD T₂.ρ (W.emb i)) = finrank LL ↥(DdRE PD T₂.ρ τ) := by
    rw [← rk_DcrisL_map W hK hQ T₂ h2 τ, hτ]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rk_ιV_inj PD) _)
  obtain ⟨lo, hlo⟩ := rk_fildR_lo PD T₂.ρ τ
  have hlo' : min lo (min (-(η : ℤ)) (b i : ℤ)) ≤ (b i : ℤ) := by omega
  have htel := rk_sum_multV PD T₂.ρ τ (min lo (min (-(η : ℤ)) (b i : ℤ))) (b i : ℤ) hlo'
  rw [hlo _ (min_le_left _ _)] at htel
  rw [hD, hrk, ← htel]
  have hodd : ¬ ((i.val + d) % 2 = 0) := by omega
  calc ∑ a ∈ Finset.Ico (min lo (min (-(η : ℤ)) (b i : ℤ))) (b i : ℤ), multV PD T₂.ρ τ a
      = ∑ a ∈ (Finset.Ico (min lo (min (-(η : ℤ)) (b i : ℤ))) (b i : ℤ)).filter
          (fun a => a ∈ Finset.Icc (-(η : ℤ)) η), multV PD T₂.ρ τ a := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro a ha hna
        apply rk_multV_of_not_jump
        intro hj
        have hw := hwin a hj
        simp only [Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS, hodd, if_false, Set.mem_union, Set.mem_Icc] at hw
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, not_and] at ha hna
        omega
    _ ≤ ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T₂.ρ τ a :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => (Finset.mem_filter.1 ha).2)
          (fun a _ _ => rk_multV_nonneg T₂ τ a)
    _ ≤ m := hsum

theorem rk_corankQ₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n)
    (hi : (i.val + d) % 2 = 1) :
    finrank LL ↥((DcrisL PD T₂.ρ (W.emb i)).map (FilCris PD T₂.ρ (b i : ℤ)).mkQ) ≤ m := by
  have h := rk_corank₂ W hE hC hQ hS i hi
  haveI := rk_fd_letter₂ W hS i
  set D := DcrisL PD T₂.ρ (W.emb i) with hD
  set Fl := FilCris PD T₂.ρ (b i : ℤ) with hFl
  have hrn := LinearMap.finrank_range_add_finrank_ker (Fl.mkQ ∘ₗ D.subtype)
  have hr : LinearMap.range (Fl.mkQ ∘ₗ D.subtype) = D.map Fl.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : finrank LL ↥(LinearMap.ker (Fl.mkQ ∘ₗ D.subtype)) = finrank LL ↥(Fl ⊓ D) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, ← inf_top_eq (Submodule.comap D.subtype Fl),
      ← Submodule.comap_subtype_self D, ← Submodule.comap_inf]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq
  rw [hr, hk] at hrn
  omega

theorem rk_corank_zero₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (hm : m = 0)
    (i : ZMod n) (hi : (i.val + d) % 2 = 1) :
    DcrisL PD T₂.ρ (W.emb i) ≤ FilCris PD T₂.ρ (b i : ℤ) := by
  have h := rk_corankQ₂ W hE hC hQ hS i hi
  subst hm
  haveI := rk_fd_letter₂ W hS i
  have hbot : (DcrisL PD T₂.ρ (W.emb i)).map (FilCris PD T₂.ρ (b i : ℤ)).mkQ = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  intro x hx
  have hmem : (FilCris PD T₂.ρ (b i : ℤ)).mkQ x ∈
      (DcrisL PD T₂.ρ (W.emb i)).map (FilCris PD T₂.ρ (b i : ℤ)).mkQ := Submodule.mem_map_of_mem hx
  rw [hbot] at hmem
  exact (Submodule.Quotient.mk_eq_zero _).mp ((Submodule.mem_bot LL).mp hmem)

end Out

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemZeroSubCoe
set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Module Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {O : Type} [CommRing O] {FF : Type} [AddCommGroup FF] [Module O FF]

def kerSub (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M] (w : ↥A →ₗ[O] M)
    (Y : Submodule O M) : Submodule O FF :=
  (Y.comap w).map A.subtype

theorem mem_kerSub (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (Y : Submodule O M) (x : FF) :
    x ∈ kerSub A w Y ↔ ∃ h : x ∈ A, w ⟨x, h⟩ ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using hy⟩
  · rintro ⟨h, hY⟩
    exact ⟨⟨x, h⟩, hY, rfl⟩

theorem kerSub_le (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (Y : Submodule O M) : kerSub A w Y ≤ A := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem mem_kerSub_coe (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (Y : Submodule O M) (x : ↥A) :
    (x : FF) ∈ kerSub A w Y ↔ w x ∈ Y := by
  rw [mem_kerSub]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem pstep_len (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (Y : Submodule O M) {lenO : ℕ∞} {m : ℕ} {c : ℝ} (L kO : ℕ)
    (hL : Module.length O (M ⧸ Y) ≤ (L : ℕ∞)) (hk : lenO = kO) (hc : (L : ℝ) ≤ c * kO) :
    PStep lenO m c A (kerSub A w Y) False := by
  refine ⟨kerSub_le A w Y, M ⧸ Y, inferInstance, inferInstance, Y.mkQ.comp w, fun x => ?_,
    fun h => h.elim, fun _ => ⟨L, kO, hL, hk, hc⟩⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_kerSub_coe]

theorem pstep_gen (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (X : Submodule O M) (s : Finset M) {lenO : ℕ∞} {m : ℕ} {c : ℝ}
    (hs : s.card ≤ m) (hw : ∀ a, w a ∈ X ⊔ Submodule.span O (s : Set M)) :
    PStep lenO m c A (kerSub A w X) True := by
  classical
  set Y := X ⊔ Submodule.span O (s : Set M) with hY
  set Xc : Submodule O ↥Y := X.comap Y.subtype
  refine ⟨kerSub_le A w X, ↥Y ⧸ Xc, inferInstance, inferInstance,
    Xc.mkQ.comp (w.codRestrict Y hw), fun x => ?_, fun _ => ?_, fun h => (h trivial).elim⟩
  · rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      mem_kerSub_coe]
    simp [Xc]
  · let ψ : ↥(Submodule.span O (s : Set M)) →ₗ[O] ↥Y ⧸ Xc :=
      Xc.mkQ.comp (Submodule.inclusion (le_sup_right : Submodule.span O (s : Set M) ≤ Y))
    let g : M → ↥Y ⧸ Xc := fun x =>
      if h : x ∈ Submodule.span O (s : Set M) then ψ ⟨x, h⟩ else 0
    refine ⟨s.image g, Finset.card_image_le.trans hs, ?_⟩
    have hrange : LinearMap.range ψ = ⊤ := by
      rw [eq_top_iff]
      rintro q -
      obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective Xc q
      obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      refine ⟨⟨z, hz⟩, ?_⟩
      simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simp only [Xc, Submodule.mem_comap, Submodule.subtype_apply]
      have : ((Submodule.inclusion (le_sup_right : Submodule.span O (s : Set M) ≤ Y) ⟨z, hz⟩ -
          ⟨x + z, hy⟩ : ↥Y) : M) = -x := by
        simp
      rw [this]
      exact X.neg_mem hx
    rw [eq_top_iff, ← hrange, LinearMap.range_eq_map, ← Submodule.span_span_coe_preimage,
      Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨⟨x, hxs⟩, hx, rfl⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨x, hx, ?_⟩)
    simp [g, hxs]

end Formalism.MainNotions.N.Pv.LocalLengthBound

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Module Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {O : Type} [CommRing O] {FF : Type} [AddCommGroup FF] [Module O FF]

def zeroSubA {LL : Type} [Field LL] [Algebra O LL] {U : Type} [AddCommGroup U] [Module LL U]
    (A : Submodule O FF) (φ : ↥A →+ U) (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) :
    Submodule O ↥A where
  carrier := {x | φ x = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq] at *; rw [map_add (f := _), ha, hb, add_zero]
  smul_mem' := fun c x hx => by simp only [Set.mem_setOf_eq] at *; rw [hφ, hx, smul_zero]

def zeroSub {LL : Type} [Field LL] [Algebra O LL] {U : Type} [AddCommGroup U] [Module LL U]
    (A : Submodule O FF) (φ : ↥A →+ U) (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) :
    Submodule O FF :=
  (zeroSubA A φ hφ).map A.subtype

theorem mem_zeroSub_coe {LL : Type} [Field LL] [Algebra O LL] {U : Type} [AddCommGroup U]
    [Module LL U] (A : Submodule O FF) (φ : ↥A →+ U)
    (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) (x : ↥A) :
    (x : FF) ∈ zeroSub A φ hφ ↔ φ x = 0 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem zeroSub_le {LL : Type} [Field LL] [Algebra O LL] {U : Type} [AddCommGroup U] [Module LL U]
    (A : Submodule O FF) (φ : ↥A →+ U)
    (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) : zeroSub A φ hφ ≤ A := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem pstep_rank [IsDomain O] [IsPrincipalIdealRing O] {LL : Type} [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [Module.Finite O FF] {U : Type} [AddCommGroup U] [Module LL U]
    (A : Submodule O FF) (φ : ↥A →+ U)
    (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) {lenO : ℕ∞} {m : ℕ} {c : ℝ}
    (hm : finrank LL ↥(Submodule.span LL (Set.range φ)) ≤ m) :
    PStep lenO m c A (zeroSub A φ hφ) True := by
  classical
  set K := zeroSubA A φ hφ with hK
  refine ⟨zeroSub_le A φ hφ, ↥A ⧸ K, inferInstance, inferInstance, K.mkQ, fun x => ?_, fun _ => ?_,
    fun h => (h trivial).elim⟩
  · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_zeroSub_coe]
    rfl

  haveI : IsNoetherian O FF := isNoetherian_of_isNoetherianRing_of_finite O FF
  haveI : Module.Finite O ↥A := Module.IsNoetherian.finite O ↥A
  haveI : Module.Finite O (↥A ⧸ K) := Module.Finite.quotient O K

  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  haveI : NoZeroSMulDivisors O (↥A ⧸ K) := by
    refine ⟨fun {a q} h => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [Submodule.Quotient.mk_eq_zero]
      change φ (a • x) = 0 at h
      change φ x = 0
      rw [hφ] at h
      have ha' : algebraMap O LL a ≠ 0 := fun h0 => ha (hinj (by rw [h0, map_zero]))
      exact (smul_eq_zero.1 h).resolve_left ha'
  haveI : Module.Free O (↥A ⧸ K) := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O (↥A ⧸ K)
  let bQ : Basis ι O (↥A ⧸ K) := Module.Free.chooseBasis O (↥A ⧸ K)

  have hrep : ∀ i, ∃ x : ↥A, K.mkQ x = bQ i := fun i => Submodule.Quotient.mk_surjective K (bQ i)
  choose xr hxr using hrep
  let u : ι → U := fun i => φ (xr i)
  have hu : LinearIndependent LL u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
      (Finset.univ.image g)
    have hint : ∀ j, ∃ a : O, algebraMap O LL a = (d : O) • g j := by
      intro j
      obtain ⟨a, ha⟩ := hd (g j) (Finset.mem_image_of_mem g (Finset.mem_univ j))
      exact ⟨a, ha⟩
    choose a ha using hint
    have hsum : φ (∑ j, a j • xr j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [hφ, ha]
      simp only [Algebra.smul_def, mul_smul]
      rw [← Finset.smul_sum]
      change algebraMap O LL (d : O) • ∑ j, g j • u j = 0
      rw [hg, smul_zero]
    have hQ : ∑ j, a j • bQ j = 0 := by
      have : K.mkQ (∑ j, a j • xr j) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simpa [hxr] using this
    have hai : a i = 0 := (Fintype.linearIndependent_iff.1 bQ.linearIndependent) a hQ i
    have hd0 : algebraMap O LL (d : O) ≠ 0 := by
      intro h0
      have : (d : O) = 0 := hinj (by rw [h0, map_zero])
      exact nonZeroDivisors.coe_ne_zero d this
    have := ha i
    rw [hai, map_zero, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hd0

  obtain ⟨gA, hgA⟩ := (Module.Finite.fg_top (R := O) (M := ↥A))
  have hspan : Submodule.span LL (Set.range φ) ≤ Submodule.span LL (φ '' (gA : Set ↥A)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span O (gA : Set ↥A) := by rw [hgA]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hφ]; exact Submodule.smul_mem _ _ hy
  haveI : FiniteDimensional LL ↥(Submodule.span LL (φ '' (gA : Set ↥A))) :=
    FiniteDimensional.span_of_finite LL (gA.finite_toSet.image φ)
  haveI : FiniteDimensional LL ↥(Submodule.span LL (Set.range φ)) :=
    Submodule.finiteDimensional_of_le hspan
  let u' : ι → ↥(Submodule.span LL (Set.range φ)) := fun i =>
    ⟨u i, Submodule.subset_span ⟨xr i, rfl⟩⟩
  have hu' : LinearIndependent LL u' :=
    LinearIndependent.of_comp (Submodule.span LL (Set.range φ)).subtype hu
  have hcard : Fintype.card ι ≤ m := (hu'.fintype_card_le_finrank).trans hm
  refine ⟨Finset.univ.image bQ, Finset.card_image_le.trans (by simpa using hcard), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact bQ.span_eq

end Formalism.MainNotions.N.Pv.LocalLengthBound

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {O : Type} [CommRing O] {FF : Type} [AddCommGroup FF] [Module O FF]

theorem pchain_of_gen {lenO : ℕ∞} {m : ℕ} {c : ℝ} {A B : Submodule O FF}
    (h : PStep lenO m c A B True) : PChain lenO m c A B 1 0 := by
  refine ⟨1, fun i => if i = 0 then A else B, {0}, by simp, by simp, by simp, by simp, by simp,
    fun i hi => ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  simpa using h

theorem pchain_of_len {lenO : ℕ∞} {m : ℕ} {c : ℝ} {A B : Submodule O FF}
    (h : PStep lenO m c A B False) : PChain lenO m c A B 0 1 := by
  refine ⟨1, fun i => if i = 0 then A else B, ∅, by simp, by simp, by simp, by simp, by simp,
    fun i hi => ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  simpa using h

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemmaDN0
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def LemmaDN0 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
    ∀ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ i,
      ((PD.p : O) ^ S) • x ∈ (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ i).map
          (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.PhiPullΔ W T₂ i).map
          ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.H2Bound
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def H2Bound [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → ∀ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
    ∃ e : ℕ, (e : ℝ) ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) +
        ((b (c - 1) + S : ℕ) : ℝ) - (b c : ℝ) / (PD.p : ℝ) +
        Formalism.MainNotions.RamifiedCoefficientChains.lam PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) + 3 ∧
      ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ (u : PowerSeries LL),
        W.lev c ζ W.q = X * u → constantCoeff u ≠ 0 →
      ∀ (w : W.DD T₂), Formalism.MainNotions.RamifiedCoefficientChains.S9.QPowSmulMemPullback W T₂ c η w →
      ∀ (K : ℕ) (hK : W.Q ^ K • w ∈ W.N T₂) (dd : ℤ → T₂.V ⊗[Qp] BdR), (∃ m₀, LB m₀ dd) →
        W.levN T₂ c ζ ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u) ^ K) dd →
        ∃ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1),
          ((PD.p : LL) ^ e) • dd 0 - ιV PD (LL := LL) (V := T₂.V)
              (φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V)
                (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ x))) ∈
            Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ))

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

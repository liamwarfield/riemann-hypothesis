module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
noncomputable section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypePlaceCover

variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [H.toHostAx.conjE_apply, H.toHostAx.conjE_apply, Complex.conj_conj]

def conjInt : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)

theorem conjInt_coe (x : 𝓞 H.E) : (conjInt H x : H.E) = H.conj x := rfl

theorem conjInt_conjInt (x : 𝓞 H.E) : conjInt H (conjInt H x) = x :=
  RingOfIntegers.ext (by rw [conjInt_coe, conjInt_coe, conj_conj])

def conjPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  ⟨w.asIdeal.comap (conjInt H), haveI := w.isPrime; Ideal.comap_isPrime _ _, fun h0 => w.ne_bot (by
    rw [eq_bot_iff]
    intro x hx
    have : conjInt H x ∈ w.asIdeal.comap (conjInt H) := by rwa [Ideal.mem_comap, conjInt_conjInt]
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← conjInt_conjInt H x, this, map_zero])⟩

theorem mem_conjPl (w : HeightOneSpectrum (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ (conjPl H w).asIdeal ↔ conjInt H x ∈ w.asIdeal := Iff.rfl

theorem conjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : conjPl H (conjPl H w) = w :=
  HeightOneSpectrum.ext (by ext x; rw [mem_conjPl, mem_conjPl, conjInt_conjInt])

theorem isConjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (conjPl H w) := by
  intro x y hxy
  have : y = conjInt H x := RingOfIntegers.ext hxy
  rw [mem_conjPl, this, conjInt_conjInt]

theorem conjPl_mem_placesOver {p : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E p) :
    conjPl H w ∈ placesOver H.E p := by
  show conjInt H _ ∈ w.asIdeal
  rw [map_natCast]; exact hw

theorem finrank_eq : Module.finrank ℚ H.E = 2 * R.f := by
  have h1 : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
  have h5 : R.f = 2 * R.ord := rfl
  rw [h1, h5]; ring

theorem place_cover : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    ∃ v : D.nd.PlG k, w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w := by
  intro D k w hw
  have hne : ∀ v v' : D.nd.PlG k, D.naut.plGw k v ≠ conjPl D.host (D.naut.plGw k v') := fun v v' e =>
    D.naut.plGw_nconj k v' v (e ▸ isConjPl_conjPl _ _)
  let f : D.nd.PlG k ⊕ D.nd.PlG k → placesOver D.host.E (D.host.g k) :=
    Sum.elim (fun v => ⟨D.naut.plGw k v, D.naut.plGw_over k v⟩)
      fun v => ⟨conjPl D.host (D.naut.plGw k v), conjPl_mem_placesOver _ (D.naut.plGw_over k v)⟩
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e <;> have e' := congrArg Subtype.val e
    · rw [D.naut.plGw_inj k e']
    · exact absurd e' (hne a b)
    · exact absurd e'.symm (hne b a)
    · have := congrArg (conjPl D.host) e'
      simp only [f, Sum.elim_inr, conjPl_conjPl] at this
      rw [D.naut.plGw_inj k this]
  have hc : Nat.card (placesOver D.host.E (D.host.g k)) = Nat.card (D.nd.PlG k ⊕ D.nd.PlG k) := by
    rw [Nat.card_coe_set_eq, D.nd.g_split k, finrank_eq, Nat.card_sum, Nat.card_eq_fintype_card, D.nd.card_PlG k, two_mul]
  haveI : Finite (placesOver D.host.E (D.host.g k)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_coe_set_eq, D.nd.g_split k]
    exact Module.finrank_pos.ne'
  obtain ⟨x, hx⟩ := ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hc.symm⟩).2 ⟨w, hw⟩
  rcases x with v | v
  · exact ⟨v, Or.inl (congrArg Subtype.val hx).symm⟩
  · refine ⟨v, Or.inr ?_⟩
    have e : conjPl D.host (D.naut.plGw k v) = w := congrArg Subtype.val hx
    exact e ▸ isConjPl_conjPl _ _

end GlobalTheory.TypePlaceCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf

theorem continuous_charpoly_coeff_of_matrix {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by

  have key : ∀ M : Matrix (Fin n) (Fin n) K, M.charpoly.coeff i =
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := fun M =>
    (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K)
      (fun p : Fin n × Fin n => M p.1 p.2) i).symm
  have hfun : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) = fun M =>
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := funext key
  rw [hfun]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)

theorem charpoly_eq_of_dense :
    ∀ (Γ : Type) [TopologicalSpace Γ] (K : Type) [CommRing K] [TopologicalSpace K]
      [IsTopologicalRing K] [T2Space K] (n : ℕ) (a b : Γ → Matrix (Fin n) (Fin n) K) (S : Set Γ),
      Dense S → Continuous a → Continuous b → (∀ g ∈ S, (a g).charpoly = (b g).charpoly) →
      ∀ g, (a g).charpoly = (b g).charpoly := by
  intro Γ _ K _ _ _ _ n a b S hS ha hb hab g

  ext i
  have hc : ∀ c : Γ → Matrix (Fin n) (Fin n) K, Continuous c →
      Continuous fun x => (c x).charpoly.coeff i :=
    fun c hc => (continuous_charpoly_coeff_of_matrix n i).comp hc
  have heq := Continuous.ext_on hS (hc a ha) (hc b hb) (fun x hx => by simp only [hab x hx])
  exact congrFun heq g

end GlobalTheory.TypeLeaf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.JumpMult

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_succ_le PD a)

theorem fildR_le_ddR (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ a ≤ DdR PD ρ :=
  le_trans inf_le_left inf_le_left

theorem jump_iff_of_finite [FiniteDimensional LL ↥(DdR PD ρ)] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FiniteDimensional LL ↥(FildR PD ρ τ a) ∧ 0 ≤ multV PD ρ τ a ∧
      (IsJumpV PD ρ τ a ↔ multV PD ρ τ a ≠ 0) := by
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    Submodule.finiteDimensional_of_le (fildR_le_ddR PD ρ τ a)
  have hle := fildR_succ_le PD ρ τ a
  refine ⟨this, ?_, ?_, ?_⟩
  · have := Submodule.finrank_mono hle
    unfold multV
    omega
  · intro hj h0
    apply hj
    apply Submodule.eq_of_le_of_finrank_eq hle
    unfold multV at h0
    omega
  · intro h h'
    exact h (by rw [multV, h', sub_self])

end General

theorem jump_iff_mult_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) ρ τ a) ∧ 0 ≤ multV (P.PD K) ρ τ a ∧ (IsJumpV (P.PD K) ρ τ a ↔ multV (P.PD K) ρ τ a ≠ 0) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ a
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  exact jump_iff_of_finite (P.PD K) ρ τ a

end GlobalTheory.Per.JumpMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.CycRing

theorem letφ_pow_const {O : Type} [CommRing O] {n : ℕ} (f : PowerSeries O →ₐ[O] PowerSeries O)
    (k : ℕ) (c : PowerSeries O) :
    (letφ (n := n) f ^ k) (fun _ => c) = fun _ => (f ^ k) c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih]
    funext i
    simp [letφ]

theorem XX_ne_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (hl : (l : O) ≠ 0) (s : ℕ) : GlobalTheory.Cyc.XX l O s ≠ 0 := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  rw [GlobalTheory.Cyc.XX, map_sub, PowerSeries.coeff_one_pow] at h1
  simp [PowerSeries.coeff_one] at h1
  exact hl h1.1

set_option maxHeartbeats 1000000 in
theorem rings_cyclotomic : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ χ : W.Gam →* ℤ_[l]ˣ, (∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) ∧ W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) ∧ (∀ g, W.γ₀ g = GlobalTheory.Cyc.act l ↥(OL LL) (χ g : ℤ_[l])) ∧ (∀ i, W.X i = GlobalTheory.Cyc.XX l ↥(OL LL) s) ∧ (∀ i, W.Q i = GlobalTheory.Cyc.QQ l ↥(OL LL) s) ∧ ‖(χ W.gam : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) ∧ ∀ u : ℤ_[l]ˣ, ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) → ∃ g, χ g = u := by
  intro D HW l _ K s LL h W
  obtain ⟨χ₀, hχ₀, -, honto⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l (D.loc l)
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hWs : W.s = s := (HW l).W_s K s LL h
  clear_value W
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hcoe : ∀ z : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z)
      = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) := by
    intro z
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
    rfl
  have hinjO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
    intro a b hab
    have := congrArg (algebraMap ↥(OL LL) ↥LL.1) hab
    rw [hcoe, hcoe] at this
    exact Subtype.ext ((algebraMap ℚ_[l] ↥LL.1).injective this)
  have hres : ∀ g : ↥(GK K), algebraMap ℤ_[l] ↥(OL LL) (χ₀ (g : GQ l) : ℤ_[l])
      = (W.χΓ (W.resΓ g) : ↥(OL LL)) := by
    intro g
    apply hinjO
    rw [hcoe, W.χΓ_res, hχ₀, (D.loc l).PD_χ]
  choose sec hsec using W.resΓ_onto
  have hsec' : ∀ g : W.Gam, algebraMap ℤ_[l] ↥(OL LL) (χ₀ (sec g : GQ l) : ℤ_[l])
      = (W.χΓ g : ↥(OL LL)) := fun g => by rw [hres, hsec]
  let χ : W.Gam →* ℤ_[l]ˣ := MonoidHom.mk' (fun g => χ₀ (sec g : GQ l)) (fun a b => by
    apply Units.ext
    apply hinj
    rw [Units.val_mul, map_mul, hsec', hsec', hsec', map_mul, Units.val_mul])
  have hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL)) := hsec'
  have hφX : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 := by
    rw [W.φ₀_X, W.q₀_def, hp]
  have hact : ∀ g, W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) ∧ W.γ₀ g = GlobalTheory.Cyc.act l ↥(OL LL) (χ g : ℤ_[l]) :=
    fun g => GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu (W.γ₀ g) W.φ₀ (χ g : ℤ_[l]) hφX (W.γ₀_comm g)
      (W.γ₀_X g).1 (by rw [(W.γ₀_X g).2, hχ])
  have hφ := (hact 1).1
  have hX : W.X = fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s := by
    rw [← GlobalTheory.Cyc.Series.phi_pow_X, ← hφ, ← letφ_pow_const, LocWach.X, hWs]
    rfl
  refine ⟨χ, hχ, hφ, fun g => (hact g).2, fun i => by rw [hX], fun i => ?_, ?_, ?_⟩
  · have h1 := congrFun W.φA_X i
    rw [hX, Pi.mul_apply] at h1
    have h2 : W.φA (fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s) i = W.φ₀ (GlobalTheory.Cyc.XX l ↥(OL LL) s) := by
      simp [LocWach.φA, letφ]
    rw [h2, hφ, GlobalTheory.Cyc.Series.phi_XX] at h1
    exact (mul_left_cancel₀ (XX_ne_zero l _ hl0 s) h1).symm
  · have h1 := W.gam_gen
    rw [hWs, ← hχ, hcoe] at h1
    have h2 := ((GlobalTheory.HWL.NormVal.locPrime_v_normalised l (D.loc l) LL).1 _ (s : ℚ)).1 (by exact_mod_cast h1)
    have h3 : ((algebraMap ℚ_[l] ↥LL.1 ((χ W.gam : ℤ_[l]) : ℚ_[l]) - 1 : ↥LL.1) : Om l)
        = algebraMap ℚ_[l] (Om l) (((χ W.gam : ℤ_[l]) - 1 : ℤ_[l]) : ℚ_[l]) := by
      rw [PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]
      rfl
    rw [h3, norm_algebraMap'] at h2
    rw [PadicInt.norm_def, h2, ← Real.rpow_intCast]
    push_cast
    rfl
  · intro u hu
    have hd : (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 :=
      Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ s).1 hu)
    obtain ⟨g, hg, hgu⟩ := honto K s h.2.2.1 u hd
    refine ⟨W.resΓ ⟨g, hg⟩, Units.ext (hinj ?_)⟩
    rw [hχ, ← hres, hgu]

end GlobalTheory.NL.CycRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistInvOfCharLawsMultOne
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf

theorem _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host)
    (χ χ' : D.naut.LP w) (c c' : ℂ)
    (hu : D.naut.unr χ) (hu' : D.naut.unr χ') (hd' : D.naut.lpDim χ' = 1)
    (hc : D.naut.frobEig χ = {c}) (hc' : D.naut.frobEig χ' = {c'}) (h : c * c' = 1) :
    D.naut.lpChar χ χ' = D.naut.lpUnr w {1} := by
  have hu2 := D.naut.unr_char χ χ' hd' hu hu'
  rw [D.naut.unr_eq_lpUnr _ hu2, D.naut.frobEig_char χ χ' c' hu hu' hd' hc', hc]
  simp [h]

private lemma exists_frobEig_etaT_inv_etaTinv (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host) :
    ∃ c : ℂ, c ≠ 0 ∧ D.naut.frobEig (D.naut.locG D.naut.etaT w) = {c} ∧
      D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {c⁻¹} := by
  have hu := D.naut.etaT_unr w
  have hcard : (D.naut.frobEig (D.naut.locG D.naut.etaT w)).card = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 hcard
  have hne := D.naut.frobEig_ne_zero _ hu
  refine ⟨c, fun h0 => hne (by rw [hc, h0]; exact Multiset.mem_singleton_self 0), hc, ?_⟩
  rw [(D.naut.etaTinv_def w).2, hc]
  simp

theorem _root_.GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne :
    ∀ D : _root_.Formalism.BasicNotions.D7, _root_.GlobalTheory.TypeLeaf.CharLaws D → _root_.GlobalTheory.TypeLeaf.MultOne D →
      _root_.GlobalTheory.TypeLeaf.TwistInv D := by
  intro D hlaw hmult
  have hdim : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 :=
    fun w => D.naut.locG_dim _ w
  have hdim' : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 :=
    fun w => D.naut.locG_dim _ w
  constructor
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim w) (hdim' w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c c⁻¹ (D.naut.etaT_unr w)
        (D.naut.etaTinv_def w).1 (hdim' w) hc hc' (mul_inv_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim' w) (hdim w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c (D.naut.etaTinv_def w).1
        (D.naut.etaT_unr w) (hdim w) hc' hc (inv_mul_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]

end GlobalTheory.TypeLeaf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DualSide

section Anti

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]

end Anti

section Dual

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]

theorem finite_TDual [Finite R] [Finite M] : Finite (TDual R M) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := TDual R M))

variable [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace M] [DiscreteTopology M]

theorem contAction_twDual [TopologicalSpace Γ] [ContinuousInv Γ] [Finite M] {χ : Γ →* Rˣ}
    {rho : Representation R Γ M} (hχ : ContAction (charRep χ)) (h : ContAction rho) :
    ContAction (twDual χ rho) := by
  have h1 : Continuous fun (p : Γ × TDual R M) (m : M) => twDual χ rho p.1 p.2 m :=
    continuous_pi fun m => hχ.comp (continuous_fst.prodMk
      ((continuous_of_discreteTopology (f := fun q : TDual R M × M => q.1 q.2)).comp
        (continuous_snd.prodMk (h.comp (continuous_fst.inv.prodMk continuous_const)))))
  exact (IsLocallyConstant.desc _ (fun (φ : TDual R M) (m : M) => φ m)
    ((IsLocallyConstant.iff_continuous _).2 h1) DFunLike.coe_injective).continuous

variable {D : Type*} [Group D] [TopologicalSpace D]

end Dual

section Global

open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
  {Av : S → ValuationSubring Ω}
  {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
  {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
  [DiscreteTopology M]
  {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}

omit [TopologicalSpace M] [DiscreteTopology M] in
theorem finite_TDual_pow : Finite (TDual (ZMod (l ^ r)) M) :=
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  finite_TDual

end Global

end GlobalTheory.DualSide
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnits
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.BdRTied

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def tu : P.R.BdRˣ := Units.map (P.ιB : P.R.B →* P.R.BdR) (isUnit_tB P).unit

theorem tu_val : (tu P : P.R.BdR) = P.ιB P.tB := by
  simp [tu]

theorem tz_eq (a : ℤ) : tz P a = ((tu P ^ a : P.R.BdRˣ) : P.R.BdR) := by
  rw [tz, tu, ← map_zpow]
  rfl

theorem fil_anti_le {a b : ℤ} (h : a ≤ b) (x : P.R.BdR) (hx : x ∈ Fil P b) : x ∈ Fil P a := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  subst b
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    change x ∈ (P.PD (botExt l)).Fil (a + ↑(n + 1)) at hx
    exact ih (by omega) ((P.PD (botExt l)).Fil_anti (a + n) (by simpa [add_assoc] using hx))

theorem ι_injective : Function.Injective P.ιB := fun a b h =>
  (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι]; exact h)

theorem fil_mul (a b : ℤ) (x y : P.R.BdR) (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy

theorem fil_act (a : ℤ) (g : GQ l) (x : P.R.BdR) (hx : x ∈ Fil P a) : P.actQdR g x ∈ Fil P a := by
  have h := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_botExt g⟩ a x hx
  rwa [P.PD_actdR] at h

theorem actQ_tpow (g : GQ l) (a : ℤ) : P.actQ g (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (isUnit_tB P).unit =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * (isUnit_tB P).unit := by
    apply Units.ext
    simpa [Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  have hι : ∀ b : P.R.B, P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := fun b => by
    have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
    rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
    exact h.symm
  rw [tz, hι, actQ_tpow, map_mul, AlgHom.commutes]

variable {AI : LocAinf l P}

theorem fil_step (T : LocTied l P AI) (a : ℤ) (x : P.R.BdR) : x ∈ Fil P a ↔ P.ιB P.tB * x ∈ Fil P (a + 1) := by
  have h := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 (botExt l) a (P.ιB P.tB * x))
  change x ∈ (P.PD (botExt l)).Fil a ↔ P.ιB P.tB * x ∈ (P.PD (botExt l)).Fil (a + 1)
  rw [h]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, e⟩
    have hu : IsUnit (P.ιB P.tB) := tu_val P ▸ (tu P).isUnit
    rwa [hu.mul_left_cancel e]

theorem fil_tz (T : LocTied l P AI) (b : ℤ) : ∀ (a : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b) := by
  induction b using Int.induction_on with
  | zero => intro a x; simp [tz_eq]
  | succ b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + b), tz_eq, tz_eq, zpow_add_one, Units.val_mul, tu_val, ← add_assoc]
    ring_nf
  | pred b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + (-(b : ℤ) - 1)), tz_eq, tz_eq, ← tu_val, ← mul_assoc, ← Units.val_mul,
      ← zpow_one_add]
    ring_nf

theorem isField (T : LocTied l P AI) : IsField P.R.BdR := by
  obtain ⟨-, -, hF, -⟩ := GlobalTheory.MemLoc.BdRField.bdR_isField l
  exact MulEquiv.isField hF T.eD.toMulEquiv

theorem unit_of_fil (T : LocTied l P AI) (x : P.R.BdR) (h0 : x ∈ Fil P 0) (h1 : x ∉ Fil P 1) :
    ∃ y ∈ Fil P 0, x * y = 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have he : GlobalTheory.MemLoc.IsEps AI.ε := hC.ε ▸ GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨-, hker, hunit, -, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have h0' : T.eD x ∈ Formalism.Per.FilD l 0 := (T.fil (botExt l) 0 x).1 h0
  obtain ⟨w, hw⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he 0 (T.eD x)).1 h0'
  rw [zpow_zero, Units.val_one, one_mul] at hw
  have hθ : Formalism.Per.θD l w ≠ 0 := by
    intro hz
    apply h1
    change x ∈ (P.PD (botExt l)).Fil 1
    rw [T.fil, hw]
    have := GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD 1 ((hker w).1 hz)
    simpa using this
  obtain ⟨w', hw'⟩ := (hunit w hθ).exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) w'), ?_, T.eD.injective ?_⟩
  · change _ ∈ (P.PD (botExt l)).Fil 0
    rw [T.fil, RingEquiv.apply_symm_apply]
    exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero w'
  · rw [map_mul, RingEquiv.apply_symm_apply, hw, ← map_mul, hw', map_one, map_one]

theorem exact_deg (x : P.R.BdR) (hx : x ≠ 0) : ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1) := by
  classical
  obtain ⟨a₀, ha₀⟩ := (P.PD (botExt l)).Fil_exh x
  have hc : ∃ c, x ∉ Fil P c := by
    by_contra h
    push_neg at h
    exact hx ((P.PD (botExt l)).Fil_sep x h)
  obtain ⟨c, hc⟩ := hc
  have hbd : ∀ z : ℤ, x ∈ Fil P z → z ≤ c := fun z hz => by
    by_contra hlt
    exact hc (fil_anti_le P (le_of_lt (not_le.1 hlt)) x hz)
  obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd ⟨c, hbd⟩ ⟨a₀, ha₀⟩
  exact ⟨a, ha, fun h => by have := hmax _ h; omega⟩

end GlobalTheory.PMon.BdRTied

namespace GlobalTheory.PMon

theorem bdR_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    IsField P.R.BdR ∧ Function.Injective P.ιB ∧
    (∀ (a b : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b)) ∧
    (∀ x ∈ Fil P 0, x ∉ Fil P 1 → ∃ y ∈ Fil P 0, x * y = 1) ∧
    (∀ x : P.R.BdR, x ≠ 0 → ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1)) ∧
    (∀ (a b : ℤ) (x y : P.R.BdR), x ∈ Fil P a → y ∈ Fil P b → x * y ∈ Fil P (a + b)) ∧
    (∀ (a : ℤ) (g : GQ l) (x : P.R.BdR), x ∈ Fil P a → P.actQdR g x ∈ Fil P a) ∧
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 ∧ tz P 1 = P.ιB P.tB := by
  intro l _ P AI T
  refine ⟨BdRTied.isField P T, BdRTied.ι_injective P, fun a b x => BdRTied.fil_tz P T b a x,
    fun x h0 h1 => BdRTied.unit_of_fil P T x h0 h1, BdRTied.exact_deg P, BdRTied.fil_mul P,
    BdRTied.fil_act P, fun a g => BdRTied.act_tz P g a, fun a b => ?_, ?_, ?_⟩
  · rw [BdRTied.tz_eq, BdRTied.tz_eq, BdRTied.tz_eq, zpow_add, Units.val_mul]
  · rw [BdRTied.tz_eq, zpow_zero, Units.val_one]
  · rw [BdRTied.tz_eq, zpow_one, BdRTied.tu_val]

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), IsField P.R.BdR ∧ Function.Injective P.ιB ∧ (∀ (a b : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b)) ∧ (∀ x ∈ Fil P 0, x ∉ Fil P 1 → ∃ y ∈ Fil P 0, x * y = 1) ∧ (∀ x : P.R.BdR, x ≠ 0 → ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1)) ∧ (∀ (a b : ℤ) (x y : P.R.BdR), x ∈ Fil P a → y ∈ Fil P b → x * y ∈ Fil P (a + b)) ∧ (∀ (a : ℤ) (g : GQ l) (x : P.R.BdR), x ∈ Fil P a → P.actQdR g x ∈ Fil P a) ∧ (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧ (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 ∧ tz P 1 = P.ιB P.tB := by
  first | exact @GlobalTheory.PMon.bdR_tied | exact GlobalTheory.PMon.bdR_tied | (intros; apply GlobalTheory.PMon.bdR_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParOfTwist
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem pointPar_of_twist (D : D7) (hT : TwistInv D) (hc : D.naut.csd D.naut.etaT)
    (hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ)) : PointPar D := by
  intro i x π hx
  obtain ⟨P, -, hB⟩ := hx
  have hp : (⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ : Formalism.BasicNotions.Part D.naut.CG) ∈
      twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
    List.mem_cons_self
  obtain ⟨h1, -, h2⟩ := hB.1 _ hp
  refine ⟨?_, (D.naut.ralg_def π).2 fun τ => ?_⟩
  · have := D.naut.csd_tw _ _ hc h2
    rwa [hT.2 _ π h1] at this
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (D.naut.infG_card D.naut.etaTinv τ)
  obtain ⟨k0, hk0⟩ := hz τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hW : (D.naut.infWt i τ).Nodup ∧
      ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    rw [D.nbc.embAV_inf i P]
    exact D.nbc.infW_alg _ _ τ
  have hle : (D.naut.infG π τ).map (· + s) ≤ D.naut.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ, ← D.naut.infG_tw π _ τ s hs]
    simp [isoInf, twistIso]
  refine ⟨Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle hW.1), fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  refine ⟨k - k0, ?_⟩
  rw [Ranks.nV] at hk
  push_cast at hk hk0 ⊢
  linear_combination hk - hk0

end GlobalTheory.TypeLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapEqProdOfValuationSubring
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem map_eq_prod_of_valuationSubring {O A K F : Type} [CommRing O] [Field K] [CommRing F]
    (B : ValuationSubring K) (j : O →+* K) (φ : B →+* F) (ψ : O →+* F)
    (h : ∀ y, ∃ h : j y ∈ B, φ ⟨_, h⟩ = ψ y) (t : A → K) (ι : A → F)
    (ht : ∀ x, ∃ h : t x ∈ B, ι x = φ ⟨_, h⟩) (p : O[X]) (s : Multiset A)
    (hp : p.map j = (s.map fun x => X - C (t x)).prod) :
    p.map ψ = (s.map fun x => X - C (ι x)).prod := by

  let j' : O →+* B :=
    { toFun := fun y => ⟨j y, (h y).1⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun a b => Subtype.ext (map_mul j a b)
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun a b => Subtype.ext (map_add j a b) }
  let t' : A → B := fun x => ⟨t x, (ht x).1⟩
  have hψ : ψ = φ.comp j' := by
    ext y
    exact ((h y).2).symm
  have hj : B.subtype.comp j' = j := by
    ext y
    rfl
  have hB : p.map j' = (s.map fun x => X - C (t' x)).prod := by
    apply Polynomial.map_injective B.subtype Subtype.val_injective
    rw [Polynomial.map_map, hj, hp, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [hψ, ← Polynomial.map_map, hB, Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [(ht x).2]

end GlobalTheory.TypeLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.WeakClosed

set_option synthInstance.maxHeartbeats 400000

instance vrOCb (l : ℕ) [Fact l.Prime] : ValuationRing (OCb l) :=
  (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2

@[reducible] def cbValued (l : ℕ) [Fact l.Prime] :
    Valued (Cb l) (ValuationRing.ValueGroup (OCb l) (Cb l)) :=
  Valued.mk' (ValuationRing.valuation (OCb l) (Cb l))

@[reducible] def cbTop (l : ℕ) [Fact l.Prime] : TopologicalSpace (Cb l) :=
  (cbValued l).toUniformSpace.toTopologicalSpace

@[reducible] def wTop (l : ℕ) [Fact l.Prime] : TopologicalSpace (WCb l) :=
  @GlobalTheory.WeakTop.wittTop l (Cb l) (cbTop l)

variable {l : ℕ} [Fact l.Prime]

@[reducible] def zlMod {K LL : FinExt l} (T : Lt K LL) : Module ℤ_[l] ↥T.L.T :=
  Module.compHom ↥T.L.T (algebraMap ℤ_[l] ↥(OL LL))

theorem zlTower_gen {O M : Type} [CommRing O] [Algebra ℤ_[l] O] [AddCommGroup M] [Module O M] :
    letI := Module.compHom M (algebraMap ℤ_[l] O)
    IsScalarTower ℤ_[l] O M :=
  letI := Module.compHom M (algebraMap ℤ_[l] O)
  ⟨fun c a x => by rw [Algebra.smul_def, mul_smul]; rfl⟩

theorem zlTower {K LL : FinExt l} (T : Lt K LL) :
    @IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T _ _ (zlMod T).toSMul :=
  zlTower_gen

abbrev LatB {K LL : FinExt l} (T : Lt K LL) (d : ℕ) : Type :=
  @Module.Basis (Fin d) ℤ_[l] ↥T.L.T _ _ (zlMod T)

@[reducible] def twTop {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) :
    TopologicalSpace (TW (RW LL) T) :=
  letI := zlMod T
  haveI := zlTower T
  TopologicalSpace.induced (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b)
    (@Pi.topologicalSpace (Fin d) (fun _ => WCb l) (fun _ => wTop l))

@[reducible] def oTop {LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    TopologicalSpace ↥(OL LL) :=
  TopologicalSpace.induced bO.equivFun inferInstance

@[reducible] def aTop {K LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    TopologicalSpace (AA K LL) :=
  letI := oTop bO
  @Pi.topologicalSpace _ _ fun _ => PowerSeries.WithPiTopology.instTopologicalSpace ↥(OL LL)

end GlobalTheory.WeakClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocity
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.GLm.ParBasic
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.FrobRecHC

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

theorem inPar_inv (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
  obtain ⟨P, hP⟩ := (par_basic g a b (a + b) rfl).1
  exact (hP _).1 (P.inv_mem ((hP x).2 h))

theorem inPar_inv_iff (x : Gn g (a + b)) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) ↔ InPar a (x : Mt g (a + b)) :=
  ⟨fun h => by simpa using inPar_inv x⁻¹ h, inPar_inv x⟩

theorem tl_one : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [tl_apply]
  simp [Matrix.one_apply]

theorem br_one : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [br_apply]
  simp [Matrix.one_apply]

theorem toG_inv (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    (toG (tl a (x : Mt g (a + b))))⁻¹ = toG (tl a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b))) ∧
    (toG (br a b (x : Mt g (a + b))))⁻¹ = toG (br a b ((x⁻¹ : Gn g (a + b)) : Mt g (a + b))) := by
  have hi := inPar_inv x h
  have hm := blocks_mul (x : Mt g (a + b)) ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) h hi
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, tl_one, br_one] at hm
  have u1 := isUnit_blocks x h
  have u2 := isUnit_blocks _ hi
  constructor
  · apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, toG_val u1.1, toG_val u2.1, ← hm.2.1, Units.val_one]
  · apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, toG_val u1.2, toG_val u2.2, ← hm.2.2, Units.val_one]

def fz (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (z : Gn g (a + b)) : ℂ :=
  χ z * (if InPar a ((z⁻¹ : Gn g (a + b)) : Mt g (a + b)) then
    Φ (toG (tl a ((z⁻¹ : Gn g (a + b)) : Mt g (a + b)))) (toG (br a b ((z⁻¹ : Gn g (a + b)) : Mt g (a + b))))
    else 0)

theorem lhs_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (hχ : IsClass χ) :
    ip χ (hcT a b Φ (a + b)) =
      ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
        ∑ z, fz χ Φ z := by
  have key : ∀ y : Gn g (a + b), (∑ x : Gn g (a + b), χ x *
      (if InPar a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)) then
        Φ (toG (tl a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b))))
          (toG (br a b ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)))) else 0)) = ∑ z, fz χ Φ z := by
    intro y
    symm
    refine Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ fun z => ?_
    have e : y⁻¹ * ((MulAut.conj y).toEquiv z)⁻¹ * y = z⁻¹ := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e, fz]
    congr 1
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    exact (hχ z y).symm
  unfold ip hcT
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hN : (Fintype.card (Gn g (a + b)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc _ = (Fintype.card (Gn g (a + b)) : ℂ)⁻¹ * ∑ y : Gn g (a + b),
        ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
          ∑ z, fz χ Φ z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← key y, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul, Finset.mul_sum]

theorem fz_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (x : Gn g (a + b)) :
    fz χ Φ x = if InPar a (x : Mt g (a + b)) then
      χ x * Φ (toG (tl a (x : Mt g (a + b))))⁻¹ (toG (br a b (x : Mt g (a + b))))⁻¹ else 0 := by
  rw [fz, inPar_inv_iff]
  split_ifs with h
  · rw [(toG_inv x h).1, (toG_inv x h).2]
  · rw [mul_zero]

theorem fibre_sum (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (x : Gn g (a + b)) :
    (∑ p : Gn g a × Gn g b, if InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (p.1 : Mt g a) ∧
        br a b (x : Mt g (a + b)) = (p.2 : Mt g b) then χ x * Φ p.1⁻¹ p.2⁻¹ else 0) = fz χ Φ x := by
  rw [fz_eq]
  by_cases h : InPar a (x : Mt g (a + b))
  · have hu := isUnit_blocks x h
    rw [if_pos h]
    have hc : ∀ p : Gn g a × Gn g b, (InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (p.1 : Mt g a) ∧
        br a b (x : Mt g (a + b)) = (p.2 : Mt g b)) ↔ (toG (tl a (x : Mt g (a + b))), toG (br a b (x : Mt g (a + b)))) = p := by
      intro p
      rw [Prod.ext_iff, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]
      simp [h]
    simp_rw [hc]
    rw [Finset.sum_ite_eq]
    simp
  · simp [h]

theorem rhs_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) :
    ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) =
      ((Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) : ℕ) : ℂ)⁻¹ * ∑ z, fz χ Φ z := by
  unfold ip res
  simp only [Prod.fst_inv, Prod.snd_inv, Fintype.card_prod]
  simp_rw [← fibre_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> push_cast <;> ring

theorem hcT_adjoint : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ),
    IsClass χ → ip χ (hcT a b Φ n) = ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) := by
  intro g _ a b n hn χ Φ hχ
  subst hn
  rw [lhs_eq χ Φ hχ, rhs_eq, card_par]

end GlobalTheory.GLq.FrobRecHC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocityStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_frobenius_reciprocity : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ), IsClass χ → ip χ (hcT a b Φ n) = ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) := by
  first | exact @GlobalTheory.GLq.FrobRecHC.hcT_adjoint | exact GlobalTheory.GLq.FrobRecHC.hcT_adjoint | (intros; apply GlobalTheory.GLq.FrobRecHC.hcT_adjoint <;> assumption)
end
end

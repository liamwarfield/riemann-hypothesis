module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepFormalDegreeBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightEventuallyZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

def pos (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def Dep (k r d : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j, pos k r j < pos k r i + d → X i j = 0

abbrev UTr (r : ℕ) : Type := {p : Fin r × Fin r // p.1 < p.2}

abbrev Bk (r : ℕ) : Type := UTr r ⊕ Fin r ⊕ UTr r ⊕ Fin r

def VM (k r : ℕ) : Bk r → Type
  | .inl _ => ℂ
  | .inr (.inl _) => Fin (k + 1) → ℂ
  | .inr (.inr (.inl _)) => ℂ
  | .inr (.inr (.inr _)) => ℝ

instance instVM (k r : ℕ) : ∀ β, AddCommGroup (VM k r β)
  | .inl _ => inferInstanceAs (AddCommGroup ℂ)
  | .inr (.inl _) => inferInstanceAs (AddCommGroup (Fin (k + 1) → ℂ))
  | .inr (.inr (.inl _)) => inferInstanceAs (AddCommGroup ℂ)
  | .inr (.inr (.inr _)) => inferInstanceAs (AddCommGroup ℝ)

def cM (k r : ℕ) : ∀ β : Bk r, Mt k r → VM k r β
  | .inl p, x => x (eI k r p.1.1) (eI k r p.1.2)
  | .inr (.inl a), x => fun j => x (eI k r a) (wI k r j)
  | .inr (.inr (.inl p)), x => x (eI k r p.1.1) (esI k r p.1.2)
  | .inr (.inr (.inr a)), x => (x (eI k r a) (esI k r a)).im

def degB (r : ℕ) : Bk r → ℕ
  | .inl p => p.1.2.val - p.1.1.val
  | .inr (.inl a) => r - a.val
  | .inr (.inr (.inl p)) => 2 * r - p.1.1.val - p.1.2.val
  | .inr (.inr (.inr a)) => 2 * r - 2 * a.val

section Glob

variable {E : Type} [Field E] [NumberField E]

def gM {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (w : InfinitePlace E) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  A w * γ.map w.embedding * (A w)⁻¹

def actM {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (x : InfinitePlace E → Mt k r) :
    InfinitePlace E → Mt k r :=
  fun w => Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ * Matrix.of (x w))

def GN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {γ | InN σ J P γ ∧ latMap γ Λ = Λ}

def ideLat (I : FractionalIdeal (𝓞 E)⁰ E) (c : ℝ) : AddSubgroup (InfinitePlace E → ℂ) where
  carrier := {z | ∃ y ∈ I, ∀ w, z w = (c : ℂ) * w.embedding y}
  zero_mem' := ⟨0, (I : Submodule (𝓞 E) E).zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', (I : Submodule (𝓞 E) E).add_mem hy hy', fun w => by simp [h, h', mul_add]⟩
  neg_mem' := by
    rintro a ⟨y, hy, h⟩
    exact ⟨-y, (I : Submodule (𝓞 E) E).neg_mem hy, fun w => by simp [h]⟩

def skewLat (σ : E →+* E) (I : FractionalIdeal (𝓞 E)⁰ E) (c : ℝ) : AddSubgroup (InfinitePlace E → ℝ) where
  carrier := {z | ∃ y ∈ I, σ y = -y ∧ ∀ w, z w = c * (w.embedding y).im}
  zero_mem' := ⟨0, (I : Submodule (𝓞 E) E).zero_mem, by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy, hs, h⟩ ⟨y', hy', hs', h'⟩
    exact ⟨y + y', (I : Submodule (𝓞 E) E).add_mem hy hy', by simp [hs, hs']; ring, fun w => by simp [h, h', mul_add]⟩
  neg_mem' := by
    rintro a ⟨y, hy, hs, h⟩
    exact ⟨-y, (I : Submodule (𝓞 E) E).neg_mem hy, by simp [hs], fun w => by simp [h]⟩

def midLat (σ : E →+* E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (I : FractionalIdeal (𝓞 E)⁰ E) :
    Set (Fin (2 * r + k + 1) → E) :=
  {t | (∀ a : Fin r, form σ J t (fun i => P i a.castSucc) = 0 ∧ form σ J t (fun i => f i a) = 0) ∧
    ∀ c ∈ I⁻¹, c • t ∈ Λ}

def homLat (σ : E →+* E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (I : FractionalIdeal (𝓞 E)⁰ E) (c : ℝ) : Set (InfinitePlace E → Fin (k + 1) → ℂ) :=
  {z | ∃ t ∈ midLat σ J Λ P f I, ∀ w l,
    z w l = (c : ℂ) * herm (Hpk k r) (bvec (wI k r l)) ((A w).mulVec fun i => w.embedding (t i))}

end Glob

section Bundle

variable {E : Type} [Field E] [NumberField E]

def HasDom {V : Type} [AddCommGroup V] [MeasurableSpace V] (μ : Measure V) (L : Set V) (c : ℝ≥0∞) : Prop :=
  ∃ D : Set V, MeasurableSet D ∧ (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) ∧ μ D = c

def blkSet (ι : Type) (k r : ℕ) (SU : UTr r → Set (ι → ℂ)) (SH : Fin r → Set (ι → Fin (k + 1) → ℂ))
    (SC : UTr r → Set (ι → ℂ)) (SG : Fin r → Set (ι → ℝ)) : ∀ β : Bk r, Set (ι → VM k r β)
  | .inl p => SU p
  | .inr (.inl a) => SH a
  | .inr (.inr (.inl p)) => SC p
  | .inr (.inr (.inr a)) => SG a

def IsVolData {F : Type} [Field F] [NumberField F] [Algebra F E] (σ : E →ₐ[F] E) {k r : ℕ}
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E))
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) : Prop :=
  IsCMExt F E σ ∧ Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧
    GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ ∧ IsFrame (σ : E →+* E) J (algebraMap F E T) P ∧
    IsDual (σ : E →+* E) J P f ∧ tupLat (id1 E r) (sideM P f) ≤ Λ ∧ IsModelAt J A ∧ (∀ a, 0 < s a) ∧
    Adapted A P f s

def rowE (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (e y : Fin n → E) (t : E) : Matrix (Fin n) (Fin n) E :=
  fun i j => (if i = j then 1 else 0) + (y i + t * e i) * Matrix.vecMul (fun l => σ (e l)) J j -
    e i * Matrix.vecMul (fun l => σ (y l)) J j

end Bundle

end GlobalTheory.SnMass.VolN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.FrameDual

section Det

variable {A : Type} [CommRing A]

end Det

section Ideals

variable {E : Type} [Field E] [NumberField E]

def Stab (σ : E →+* E) (I : FractionalIdeal (𝓞 E)⁰ E) : Prop := ∀ x ∈ I, σ x ∈ I

theorem stab_one (σ : E →+* E) : Stab σ 1 := by
  intro x hx
  obtain ⟨d, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  exact (FractionalIdeal.mem_one_iff _).2 ⟨RingOfIntegers.mapRingHom σ d, rfl⟩

theorem Stab.mul {σ : E →+* E} {I J : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (hJ : Stab σ J) :
    Stab σ (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun i hi j hj => ?_) (fun a b ha hb => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hI i hi) (hJ j hj)
  · rw [map_add (f := _)]; exact Submodule.add_mem (I * J).coeToSubmodule ha hb

theorem Stab.pow {σ : E →+* E} {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (j : ℕ) :
    Stab σ (I ^ j) := by
  induction j with
  | zero => simpa using stab_one σ
  | succ j ih => rw [pow_succ]; exact ih.mul hI

theorem Stab.inv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I)
    (h0 : I ≠ 0) : Stab σ I⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
  intro y hy
  have := stab_one σ _ (hx _ (hI y hy))
  rwa [map_mul, hσ] at this

theorem diff_ne_zero : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem dInv_ne_zero (j : ℕ) : dInv E j ≠ 0 := pow_ne_zero _ (inv_ne_zero diff_ne_zero)

theorem stab_dInv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) (j : ℕ) : Stab σ (dInv E j) := by
  refine Stab.pow ?_ j
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  intro x hx
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h10] at hx ⊢
  intro a ha
  have h1 := hx _ (stab_one σ a ha)
  let e : E ≃ₐ[ℚ] E := AlgEquiv.ofBijective σ.toRatAlgHom (Function.Involutive.bijective hσ)
  have h2 : Algebra.traceForm ℚ E (σ x) a = Algebra.traceForm ℚ E x (σ a) := by
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply, ← Algebra.trace_eq_of_algEquiv e (x * σ a)]
    congr 1
    change _ = σ (x * σ a)
    rw [map_mul, hσ]
  rwa [h2]

end Ideals

section Frame

variable {E : Type} [Field E] [NumberField E]

theorem frameDualTupleIdeals_castAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.castAdd r b.castSucc) = dInv E (r - b) := by
  simp [id1]

theorem frameDualTupleIdeals_natAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.natAdd (r + 1) b) = (dInv E (r - b))⁻¹ := by
  simp [id1]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem natAbs_discr_sq (h2 : Module.finrank F E = 2) [Algebra.FormallyUnramified (𝓞 F) (𝓞 E)] :
    (discr E).natAbs = (discr F).natAbs ^ 2 := by
  have h0 : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    exact not_dvd_differentIdeal_iff.2 (inferInstance : Algebra.IsUnramifiedAt (𝓞 F) P)
      (Ideal.dvd_iff_le.2 hle)
  have h1 := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rwa [h0, Ideal.absNorm_top, one_mul, h2] at h1

theorem absNorm_dInv (j : ℕ) :
    ((FractionalIdeal.absNorm (dInv E j) : ℚ) : ℝ) = |(discr E : ℝ)|⁻¹ ^ j := by
  rw [SgGlob.dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E (𝓞 E)]
  simp

end Frame

end GlobalTheory.SnMass.FrameDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.Push

variable {ι : Type} [Fintype ι] {X : ι → Type} {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)] in
private theorem lmarginal_prod_eq_prod_lintegral_mul_prod [DecidableEq ι] (f : (i : ι) → X i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (s : Finset ι) (x : (i : ι) → X i) :
    (∫⋯∫⁻_s, (fun z => ∏ i, f i (z i)) ∂μ) x =
      (∏ i ∈ s, ∫⁻ y, f i y ∂(μ i)) * ∏ i ∈ sᶜ, f i (x i) := by
  have hF : Measurable fun z : (i : ι) → X i => ∏ i, f i (z i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert i s hi ih =>
    rw [lmarginal_insert _ hF hi]
    simp_rw [ih]
    have h : ∀ y, ∏ j ∈ sᶜ, f j (Function.update x i y j) =
        f i y * ∏ j ∈ (insert i s)ᶜ, f j (x j) := by
      intro y
      rw [Finset.compl_insert, ← Finset.mul_prod_erase _ _ (Finset.mem_compl.2 hi),
        Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    simp_rw [h]
    rw [Finset.prod_insert hi, lintegral_const_mul _ ((hf i).mul_const _),
      lintegral_mul_const _ (hf i)]
    ring

theorem _root_.GlobalTheory.SnMass.Push.lintegral_fintype_prod {ι : Type} [Fintype ι] {X : ι → Type}
    {mX : ∀ i, MeasurableSpace (X i)}
    {μ : (i : ι) → Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → X i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  by_cases hne : ∀ i, Nonempty (X i)
  · rw [lintegral_eq_lmarginal_univ (fun i => (hne i).some), lmarginal_prod_eq_prod_lintegral_mul_prod f hf]
    simp
  · push_neg at hne
    obtain ⟨i, hi⟩ := hne
    haveI : IsEmpty ((i : ι) → X i) := ⟨fun x => hi.elim (x i)⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Measure.eq_zero_of_isEmpty (μ i)])]
    simp [Measure.eq_zero_of_isEmpty (Measure.pi μ)]

end GlobalTheory.SnMass.Push
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExactRanksOfRecord
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem exact_ranks_of_record : ∀ D : D7, (∀ i, StandardLattice.SplitsF D (D.host.g i)) → StandardLattice.volY0 D = StandardLattice.massI D D.R.r → StandardLattice.FactDstar D → (∀ u, (D.duS u : ℝ) = StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) → letI := D.host.cmStar; ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V] [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (L : Submodule (𝓞 D.host.E) V), h.IsSymm → (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.k → ∀ u : D.what₂.Word, (D.duS u : ℝ) = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, ∏ i ∈ Finset.Icc 1 D.R.k, ((Ideal.absNorm p.asIdeal : ℝ) ^ i - 1)) * (∏ τ, Formalism.MainNotions.S.vand (fun i : Fin D.R.k => (((D.hcW u τ).u i : ℚ) : ℝ)) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) ∧ (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.r → D.what₂.Dstar = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, (∏ i ∈ Finset.range D.R.r, ((Ideal.absNorm p.asIdeal : ℝ) ^ D.R.r - (Ideal.absNorm p.asIdeal : ℝ) ^ i)) / ((Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))) * ∏ τ, D.dsig τ) := by
  intro D hsp hvol hD hdu V _ _ _ _ h L hs
  letI := D.host.cmStar
  have hmass : ∀ n, Formalism.HermitianLatticesTheory.IsOrthoLattice h L n → Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D n :=
    fun n ho => StandardLattice.mass_ortho D.host.E D.sp.cm.cmUnram n V h L ho
  have hcol := GlobalTheory.T.finprod_places_over_typePrimes_split D (fun x : ℝ => ∏ i ∈ Finset.Icc 1 D.R.k, (x ^ i - 1)) hsp
  have hrow := GlobalTheory.T.finprod_places_over_typePrimes_split D (fun x : ℝ => (∏ i ∈ Finset.range D.R.r, (x ^ D.R.r - x ^ i)) /
    (x ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * x ^ (D.R.k * (D.R.k - 1) / 2))) hsp
  beta_reduce at hcol hrow
  obtain ⟨hc0, hr0⟩ := GlobalTheory.T.localIndices_column_row_levels_exact D 0
  obtain ⟨hc1, hr1⟩ := GlobalTheory.T.localIndices_column_row_levels_exact D 1
  refine ⟨fun ho u => ?_, fun ho => ?_⟩
  · rw [hdu u, hmass _ ho, hcol]
    unfold StandardLattice.duStarU StandardLattice.duStarP StandardLattice.idxPi
    rw [hc0, hc1]
    rfl
  · rw [show D.what₂.Dstar = StandardLattice.DstarD D from hD, hmass _ ho, hrow]
    unfold StandardLattice.DstarD StandardLattice.DstarP StandardLattice.idxSig
    rw [hvol, hr0, hr1]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverOfNorm
namespace GlobalTheory.RankSplit

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

private lemma span_prime_isMaximal' {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
private lemma liesOver_span_of_prime_natCast_mem {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (P : Ideal A) [hP : P.IsPrime]
    (h : (p : A) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨(span_prime_isMaximal' hp).eq_of_le (Ideal.IsPrime.comap (algebraMap ℤ A)).ne_top ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
  simpa using h

theorem ncard_primesOver_of_norm {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  classical
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
  haveI := span_prime_isMaximal' hp
  rw [← Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0,
    ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  haveI hPm : P.IsMaximal := hPp.isMaximal hPne
  have hpP : (p : 𝓞 E) ∈ P := by
    have := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using this
  obtain ⟨hn, hsq⟩ := h P hPm hpP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have he : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmap, pow_one, Ideal.span_singleton_le_iff_mem]
      exact hpP
    · rw [hmap, Ideal.span_singleton_le_iff_mem]
      exact hsq
  have hf : Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    have h1 := Ideal.pow_inertiaDeg p P
    rw [hn] at h1
    exact (Nat.pow_eq_self_iff hp.one_lt).mp h1
  rw [he, hf]

theorem splitsF_of_norm : ∀ (D : D7) (p : ℕ), p.Prime →
    (∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((p : 𝓞 D.host.E) ∈ P) →
      Ideal.absNorm P = p ∧ (p : 𝓞 D.host.E) ∉ P ^ 2) → StandardLattice.SplitsF D p := by
  intro D p hp h
  have hE := ncard_primesOver_of_norm hp h
  have hF := GlobalTheory.ColClassCompare.ncard_primesOver_of_split (F := D.host.F) hp hE
  rw [GlobalTheory.ColClassCompare.finrank_F] at hF
  refine ⟨?_, fun v hv => (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) hp hE v.asIdeal hv).2⟩
  rw [← hF, ← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun v => ⟨v.1.asIdeal, v.1.isPrime, liesOver_span_of_prime_natCast_mem hp v.1.asIdeal v.2⟩
      invFun := fun P => ⟨⟨P.1, P.2.1, ?_⟩, ?_⟩
      left_inv := fun v => rfl
      right_inv := fun P => rfl }
  · have := P.2.2
    have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
    exact Ideal.ne_bot_of_liesOver_of_ne_bot h0 P.1
  · have := P.2.2
    have h2 := (Ideal.mem_of_liesOver P.1 (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using h2

end GlobalTheory.RankSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetImageBall
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SnMass
open scoped ENNReal

namespace GlobalTheory.GramExp

def Sgn {a : ℕ} (d : Fin a → ℂ) : Prop := ∀ i, d i = 1 ∨ d i = -1

theorem _root_.GlobalTheory.GramExp.diag_sq {a : ℕ} {d : Fin a → ℂ}
    (hd : _root_.GlobalTheory.GramExp.Sgn d) : Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases hd i with h | h <;> simp [h]

theorem _root_.GlobalTheory.GramExp.isMatGroup_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H * H = 1) : _root_.PI.IsMatGroup (_root_.Formalism.QuantumDeterminants.UH H) := by
  unfold _root_.PI.IsMatGroup _root_.Formalism.QuantumDeterminants.UH
  have hdetH : H.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hH
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hunit : ∀ a : Matrix (Fin N) (Fin N) ℂ, aᴴ * H * a = H → IsUnit a.det := by
    intro a ha
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_mul] at this
    have h1 : aᴴ.det * a.det = 1 := by
      have : (aᴴ.det * a.det) * H.det = 1 * H.det := by linear_combination this
      exact mul_right_cancel₀ hdetH this
    exact isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · simp
  · intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [ha, hb]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hu := hunit a ha
    have hr : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
    refine ⟨?_, hr⟩
    have hc : (a⁻¹)ᴴ * aᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha]
      _ = ((a⁻¹)ᴴ * aᴴ) * H * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hc, hr, Matrix.one_mul, Matrix.mul_one]

theorem _root_.GlobalTheory.GramExp.exp_cont {n : ℕ} :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous

theorem _root_.GlobalTheory.GramExp.measurableSet_image_ball {X Y : Type} [PseudoMetricSpace X] [ProperSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {f : X → Y}
    (hf : Continuous f) (x : X) (ρ : ℝ) :
    MeasurableSet (f '' Metric.ball x ρ) := by
  have hb : Metric.ball x ρ = ⋃ k : ℕ, Metric.closedBall x (ρ - 1 / ((k : ℝ) + 1)) := by
    ext y
    simp only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hb, Set.image_iUnion]
  exact MeasurableSet.iUnion fun k =>
    ((isCompact_closedBall x _).image hf).isClosed.measurableSet

end GlobalTheory.GramExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixExtLast
namespace GlobalTheory.MatrixExtLast

theorem matrix_ext_last {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h₁ : ∀ i j : Fin k, M (Fin.castSucc i) (Fin.castSucc j) = N (Fin.castSucc i) (Fin.castSucc j))
    (h₂ : ∀ i : Fin k, M (Fin.castSucc i) (Fin.last k) = N (Fin.castSucc i) (Fin.last k))
    (h₃ : ∀ j : Fin k, M (Fin.last k) (Fin.castSucc j) = N (Fin.last k) (Fin.castSucc j))
    (h₄ : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h₄
    | cast j => exact h₃ j
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact h₂ i
    | cast j => exact h₁ i j

end GlobalTheory.MatrixExtLast
end

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace GlobalTheory.Tube

def Hd (k : ℕ) (η : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1

def blk {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun i j => Fin.lastCases (motive := fun _ => ℂ) (Fin.lastCases (motive := fun _ => ℂ) d r j)
    (fun i' => Fin.lastCases (motive := fun _ => ℂ) (b i') (A i') j) i

@[simp] theorem blk_ll {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) :
    blk A b r d (Fin.last k) (Fin.last k) = d := by simp [blk]

@[simp] theorem blk_lc {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (j : Fin k) :
    blk A b r d (Fin.last k) j.castSucc = r j := by simp [blk]

@[simp] theorem blk_cl {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (i : Fin k) :
    blk A b r d i.castSucc (Fin.last k) = b i := by simp [blk]

@[simp] theorem blk_cc {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (i j : Fin k) :
    blk A b r d i.castSucc j.castSucc = A i j := by simp [blk]

theorem blk_ext {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h1 : ∀ i j : Fin k, M i.castSucc j.castSucc = N i.castSucc j.castSucc)
    (h2 : ∀ i : Fin k, M i.castSucc (Fin.last k) = N i.castSucc (Fin.last k))
    (h3 : ∀ j : Fin k, M (Fin.last k) j.castSucc = N (Fin.last k) j.castSucc)
    (h4 : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  first
  | exact @_root_.GlobalTheory.MatrixExtLast.matrix_ext_last
  | exact _root_.GlobalTheory.MatrixExtLast.matrix_ext_last
  | (apply _root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixExtLast.matrix_ext_last ..)

theorem Hd_eq (k : ℕ) (η : ℝ) : Hd k η = blk 1 0 0 (η : ℂ) := by
  refine blk_ext (fun i j => ?_) (fun i => ?_) (fun j => ?_) ?_
  · simp [Hd, Matrix.diagonal_apply, Matrix.one_apply, Fin.castSucc_ne_last]
  · simp [Hd, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  · simp [Hd, Matrix.diagonal_apply, (Fin.castSucc_ne_last _).symm]
  · simp [Hd]

theorem Hd_sq (k : ℕ) {η : ℝ} (hη : η = 1 ∨ η = -1) : Hd k η * Hd k η = 1 := by
  refine GlobalTheory.GramExp.diag_sq fun i => ?_
  split_ifs
  · rcases hη with h | h <;> simp [h]
  · simp

def nsq {k : ℕ} (β : Fin k → ℂ) : ℝ := ∑ j, ‖β j‖ ^ 2

def dd {k : ℕ} (η : ℝ) (β : Fin k → ℂ) : ℝ := Real.sqrt (1 - η * nsq β)

def sec {k : ℕ} (η : ℝ) (β : Fin k → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  blk (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j - ((η / (1 + dd η β) : ℝ) : ℂ) * (conj (β i) * β j))
    (fun i => -(η : ℂ) * conj (β i)) β (dd η β : ℂ)

def kap {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (u : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := blk A 0 0 u

def row {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin k → ℂ := fun j => g (Fin.last k) j.castSucc

def ph {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℂ :=
  g (Fin.last k) (Fin.last k) / (‖g (Fin.last k) (Fin.last k)‖ : ℂ)

def bet {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin k → ℂ := fun j => conj (ph g) * row g j

def top {k : ℕ} (η : ℝ) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => (g * sec η (-bet g)) i.castSucc j.castSucc

abbrev Par (k : ℕ) : Type := lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) × ℝ × EuclideanSpace ℂ (Fin k)

def hv {k : ℕ} (w : EuclideanSpace ℂ (Fin k)) : Fin k → ℂ := fun j => w j / (Real.sqrt 2 : ℂ)

def chart {k : ℕ} (η : ℝ) (x : Par k) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  kap (NormedSpace.exp (unrealify (x.1 : EuclideanSpace ℝ _))) (Complex.exp (x.2.1 * Complex.I)) * sec η (hv x.2.2)

def tang {k : ℕ} (η : ℝ) (x : Par k) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  blk (unrealify (x.1 : EuclideanSpace ℝ _)) (fun i => -(η : ℂ) * conj (hv x.2.2 i)) (hv x.2.2) (x.2.1 * Complex.I)

def tubeO (k : ℕ) (η t : ℝ) : Set (PI.MtM (k + 1)) :=
  {g | Matrix.of g ∈ UH (Hd k η) ∧ nsq (row (Matrix.of g)) < t}

end GlobalTheory.Tube
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralDiscreteSeriesUnipotentVanishes
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralDiscreteSeriesUnipotentVanishes
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.RealFibre

private lemma eq_zero_of_sum_star_mul_const_mul_eq_zero {n : ℕ} (x : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : ∑ i, star (x i) * (c * x i) = 0) : x = 0 := by
  have h1 : c * ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) = 0 := by
    rw [← h, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (Complex.normSq (x i) : ℂ) = star (x i) * x i := Complex.normSq_eq_conj_mul_self
    rw [e]; ring
  have h2 : ∑ i, Complex.normSq (x i) = 0 := by
    have h3 := (mul_eq_zero.mp h1).resolve_left hc
    exact_mod_cast h3
  funext i
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp h2 i
    (Finset.mem_univ i)
  simpa using h4

theorem one_le_rkR_of_isIsoC {n : ℕ} {ε : Fin n → Bool} {W : Submodule ℂ (Fin n → ℂ)} (hW : IsIsoC ε W) :
    1 ≤ rkR ε := by
  unfold IsIsoC herm Jm at hW
  obtain ⟨hne, hiso⟩ := hW
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hq := hiso x hxW x hxW

  have hall : ∀ b : Bool, ∃ i, ε i = b := by
    intro b
    by_contra hno
    push_neg at hno
    have hb : ∀ i, ε i = !b := fun i => by
      have h' := hno i
      cases hε : ε i <;> cases b <;> simp_all
    apply hx0
    apply eq_zero_of_sum_star_mul_const_mul_eq_zero x (if (!b) = true then (1 : ℂ) else -1) (by split_ifs <;> norm_num)
    rw [← hq]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hb]
  obtain ⟨i, hi⟩ := hall true
  obtain ⟨j, hj⟩ := hall false
  unfold rkR
  apply le_min
  · exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  · exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

theorem decE_le_exp {q : ℕ} (hq : 1 ≤ q) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    decE q h t ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * t)) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hs1 : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  unfold decE
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  obtain ⟨s, hsd⟩ : ∃ s, s = Real.sqrt q := ⟨_, rfl⟩
  rw [← hsd] at hs hs1 ⊢
  have hs0 : s ≠ 0 := hs.ne'

  have key : t / s - min (2 * t ^ 2) (t / s) ≤ 1 := by
    rcases le_total (2 * t ^ 2) (t / s) with h' | h'
    · rw [min_eq_left h']
      obtain ⟨u, hu⟩ : ∃ u, u = t / s := ⟨_, rfl⟩
      rw [← hu]
      have ht : t = u * s := by rw [hu]; field_simp
      have h2 : t ^ 2 = u ^ 2 * s ^ 2 := by rw [ht]; ring
      have h1 : 0 ≤ u ^ 2 * (s ^ 2 - 1) := mul_nonneg (sq_nonneg u) (by nlinarith)
      nlinarith [sq_nonneg (u - 1 / 4)]
    · rw [min_eq_right h']; norm_num
  have e : h / (8 * s) * t = h / 8 * (t / s) := by ring
  rw [e]
  nlinarith [mul_nonneg hh (sub_nonneg.mpr key)]

theorem rate_lt {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) {h : ℝ}
    (hh : 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    0 ≤ h ∧ 12 * (n : ℝ) * q < h / (8 * Real.sqrt q) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hpow : (q : ℝ) ^ ((3 : ℝ) / 2) = q * Real.sqrt q := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hpow] at hh
  have hP : 0 < (n : ℝ) * q * Real.sqrt q := by positivity
  refine ⟨by nlinarith, ?_⟩
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

private lemma list_prod_eq_take_mul_pair_mul_drop {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ) (v : ι) :
    ∏ u, F u = F v * ∏ u ∈ Finset.univ.erase v, F u :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ v)).symm

private lemma rkR_le' {n : ℕ} (ε : Fin n → Bool) : rkR ε ≤ n := by
  unfold rkR
  calc min (Finset.univ.filter fun a => ε a = true).card (Finset.univ.filter fun a => ε a = false).card
      ≤ (Finset.univ.filter fun a => ε a = true).card := min_le_left _ _
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem integral_phe_eq_zero : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  classical
  intro hS B d h hD hL hh v Wv hW ν hν x y
  obtain ⟨hHC, hDS, hLow, hFd⟩ := hD v
  have hDS' := hDS
  obtain ⟨_, _, hU, _⟩ := hDS'
  obtain ⟨hw1, hwS⟩ := hLow
  have hq1 : 1 ≤ rkR (B.I.ε v) := one_le_rkR_of_isIsoC hW
  have hn1 : 1 ≤ B.I.n := le_trans hq1 (rkR_le' _)
  obtain ⟨h0, hc⟩ := rate_lt hn1 hq1 (hh v)

  obtain ⟨α, hαs, hαc, hαfix⟩ := exists_smooth_fix_lowKSub B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hU
    (hS B.I.n (B.I.ε v) (B.lam v) hHC (B.H v) (B.σ v) hDS).1

  have hT := GlobalTheory.T.unitary_rep_matrixCoeff_integral_eq_zero B.I.n (B.I.ε v) Wv ν hW hν (B.H v) (B.σ v) (d v)
    (h / (8 * Real.sqrt (rkR (B.I.ε v) : ℝ))) α (B.w v) hU hFd hc hw1 hαs hαc
    (fun u => hαfix (B.w v) hwS u)
    ⟨Real.exp (h / 8), fun g => (hL v g).trans (decE_le_exp hq1 h0 _)⟩ (x.1 v) (y.1 v)
  have hstar : ∫ m, star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν = 0 := by
    refine (integral_conj (μ := ν)
      (f := fun m => ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ)).trans ?_
    rw [hT]; simp

  have hfun : ∀ m : UJ (B.I.ε v),
      phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) =
        ((((∏ u, d u : ℝ) : ℂ) * star (∏ u ∈ Finset.univ.erase v,
          ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ)) * B.e (x.2 * y.2)) *
        star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ := by
    intro m
    have hrest : ∏ u ∈ Finset.univ.erase v,
        ⟪B.w u, B.σ u (uMat (x.1 u * (open Classical in (Pi.mulSingle v m : B.I.Ginf)) u * y.1 u)) (B.w u)⟫_ℂ =
        ∏ u ∈ Finset.univ.erase v, ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ :=
      Finset.prod_congr rfl fun u hu => by
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hu), mul_one]
    simp only [GlobalTheory.Count.phe, GlobalTheory.Count.ph, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one]
    rw [list_prod_eq_take_mul_pair_mul_drop _ v, hrest, Pi.mulSingle_eq_same, star_mul']
    ring
  refine (integral_congr_ae (ae_of_all ν hfun)).trans ?_
  rw [integral_const_mul, hstar, mul_zero]

end GlobalTheory.RealFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralDiscreteSeriesUnipotentVanishesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_discreteSeries_unipotent_vanishes : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  first | exact @GlobalTheory.RealFibre.integral_phe_eq_zero | exact GlobalTheory.RealFibre.integral_phe_eq_zero | (intros; apply GlobalTheory.RealFibre.integral_phe_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralEqOfQuotientMeasuresBesselUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralEqOfQuotientMeasuresBesselUnitary
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SnMass.QuotUniq

theorem lintegral_le {k r : ℕ} {R : Set (Mat k r)} {μG μR ν ν' : Measure (Mt k r)}
    (hR : IsClosedSub k r R) (hG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn R μR) (hU : IsUnimod R μR)
    (hν : IsQuotMeas μG μR ν) (hν' : IsQuotMeas μG μR ν') (F : Mt k r → ℝ≥0∞) (hF : Measurable F)
    (hFi : ∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) :
    ∫⁻ x, F x ∂ν ≤ ∫⁻ x, F x ∂ν' := by
  obtain ⟨-, -, φ, hφ, h⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν hR hG hμ hU hν
  obtain ⟨h1, -, -⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν' hR hG hμ hU hν'
  have h1' : ∀ᵐ x ∂ν', Matrix.of x ∈ GG k r := h1
  have hae : ∀ᵐ s ∂μR, Matrix.of s ∈ R := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (lmulM (Matrix.of s) x) ∂μR) ∂ν' := hν'
  have hTm := (GlobalTheory.Amp.CutQuot.continuous_act k r).measurable
  rw [h F hF hFi, hW' (fun x => φ x * F x) (hφ.1.mul hF)]
  refine lintegral_mono_ae ?_
  filter_upwards [h1'] with x hx
  have hTx : Measurable fun s : Mt k r => lmulM (Matrix.of s) x :=
    hTm.comp (measurable_id.prodMk measurable_const)
  have h2 : ∫⁻ s, φ (lmulM (Matrix.of s) x) * F (lmulM (Matrix.of s) x) ∂μR =
      ∫⁻ s, φ (lmulM (Matrix.of s) x) * F x ∂μR := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    rw [hFi _ hs x hx]
  rw [h2, lintegral_mul_const (F x) (f := fun s => φ (lmulM (Matrix.of s) x)) (hφ.1.comp hTx)]
  exact mul_le_of_le_one_left zero_le (hφ.2 x hx)

theorem quot_uniq : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν ν' : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → IsQuotMeas μG μR ν' → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : Mat k r → V), ContinuousOn F (GG k r) → (∀ ρ ∈ R, ∀ x ∈ GG k r, F (ρ * x) = F x) → (Integrable (fun x : Mt k r => F (Matrix.of x)) ν ↔ Integrable (fun x : Mt k r => F (Matrix.of x)) ν') ∧ ∫ x, F (Matrix.of x) ∂ν = ∫ x, F (Matrix.of x) ∂ν' := by
  intro k r R μG μR ν ν' hR hG hμ hU hν hν' V _ _ _ F hF hFi
  classical
  borelize V
  set S : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hS
  have hSm : MeasurableSet S := GlobalTheory.Amp.CutQuot.measurable_G k r
  have hFc : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) S := hF
  set F' : Mt k r → V := S.piecewise (fun x : Mt k r => F (Matrix.of x)) (fun _ => 0) with hF'
  have hF'm : Measurable F' := hFc.measurable_piecewise continuousOn_const hSm
  have hsep : TopologicalSpace.IsSeparable (Set.range F') := by
    have h1 : TopologicalSpace.IsSeparable ((fun x : Mt k r => F (Matrix.of x)) '' S) :=
      hFc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace S)
    refine (h1.union (Set.finite_singleton (0 : V)).isSeparable).mono ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ S
    · exact Or.inl ⟨x, hx, by rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]⟩
    · exact Or.inr (by rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; rfl)
  have hinv : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r → F' (lmulM ρ x) = F' x := by
    intro ρ hρ x hx
    have hx' : lmulM ρ x ∈ S := (GlobalTheory.Amp.CutQuot.mul_mem_iff (hR.1 hρ) (Matrix.of x)).2 hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx', Set.piecewise_eq_of_mem _ _ _ (show x ∈ S from hx)]
    exact hFi ρ hρ _ hx
  have hm : MeasurableSpace.comap F' inferInstance ≤ (inferInstance : MeasurableSpace (Mt k r)) :=
    hF'm.comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap F' inferInstance] F' :=
    (@stronglyMeasurable_iff_measurable_separable _ _ _ (MeasurableSpace.comap F' inferInstance)
      _ _ _ _).2 ⟨comap_measurable F', hsep⟩
  have htrim : ν.trim hm = ν'.trim hm := by
    refine @Measure.ext _ (MeasurableSpace.comap F' inferInstance) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]
    have hAm : MeasurableSet A := hm A hA
    obtain ⟨B, -, rfl⟩ := hA
    have hi : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r →
        (F' ⁻¹' B).indicator (1 : Mt k r → ℝ≥0∞) (lmulM ρ x) = (F' ⁻¹' B).indicator 1 x := by
      intro ρ hρ x hx
      simp only [Set.indicator, Set.mem_preimage, hinv ρ hρ x hx, Pi.one_apply]
    rw [← lintegral_indicator_one hAm, ← lintegral_indicator_one hAm]
    exact le_antisymm (lintegral_le hR hG hμ hU hν hν' _ (measurable_one.indicator hAm) hi)
      (lintegral_le hR hG hμ hU hν' hν _ (measurable_one.indicator hAm) hi)
  have hae : ∀ ν₀ : Measure (Mt k r), IsQuotMeas μG μR ν₀ →
      (fun x : Mt k r => F (Matrix.of x)) =ᵐ[ν₀] F' := by
    intro ν₀ h
    have h1 : ∀ᵐ x ∂ν₀, x ∈ S := (GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν₀ hR hG hμ hU h).1
    filter_upwards [h1] with x hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]
  rw [integrable_congr (hae ν hν), integrable_congr (hae ν' hν'), integral_congr_ae (hae ν hν),
    integral_congr_ae (hae ν' hν'), integral_trim hm hsm, integral_trim hm hsm, htrim]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, rfl⟩
  · exact integrable_of_integrable_trim hm (htrim ▸ h.trim hm hsm)
  · exact integrable_of_integrable_trim hm (htrim.symm ▸ h.trim hm hsm)

end GlobalTheory.SnMass.QuotUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralEqOfQuotientMeasuresBesselUnitaryStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν ν' : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → IsQuotMeas μG μR ν' → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : Mat k r → V), ContinuousOn F (GG k r) → (∀ ρ ∈ R, ∀ x ∈ GG k r, F (ρ * x) = F x) → (Integrable (fun x : Mt k r => F (Matrix.of x)) ν ↔ Integrable (fun x : Mt k r => F (Matrix.of x)) ν') ∧ ∫ x, F (Matrix.of x) ∂ν = ∫ x, F (Matrix.of x) ∂ν' := by
  first | exact @GlobalTheory.SnMass.QuotUniq.quot_uniq | exact GlobalTheory.SnMass.QuotUniq.quot_uniq | (intros; apply GlobalTheory.SnMass.QuotUniq.quot_uniq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightEventuallyZeroStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_eventually_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∀ y : H, ∀ᶠ g : UJ ε in nhds 1, ∑ a, ∑ b, Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g) = 0 := by
  first | exact @GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero | exact GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero | (intros; apply GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero <;> assumption)
end

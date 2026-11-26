module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealPlaces

variable (D : D7)

theorem embS_injective : Function.Injective (embS D) := by
  intro τ τ' h
  exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem mem_cm_iff (φ : D.host.E →+* ℂ) :
    φ ∈ D.host.cmType ↔ ∃ τ, embS D τ = φ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 φ
    have hg := ((factEmb D.R D.host).2 g).1 h
    refine ⟨D.eTau.symm ⟨g, hg⟩, ?_⟩
    unfold embS
    rw [Equiv.apply_symm_apply]
  · rintro ⟨τ, rfl⟩
    exact ((factEmb D.R D.host).2 _).2 (D.eTau τ).2

theorem range_iff (φ : D.host.E →+* ℂ) :
    (∃ τ, embS D τ = φ) ↔ ¬ ∃ τ, embS D τ = ComplexEmbedding.conjugate φ := by
  rw [← mem_cm_iff, ← mem_cm_iff]
  exact D.host.der.cmType.1 φ

theorem ne_conj (τ τ' : D.what₂.Tau) : embS D τ' ≠ ComplexEmbedding.conjugate (embS D τ) :=
  fun h => (range_iff D _).1 ⟨τ, rfl⟩ ⟨τ', h⟩

theorem sum_bijective : Function.Bijective
    (Sum.elim (embS D) (fun τ => ComplexEmbedding.conjugate (embS D τ))) := by
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg _ (embS_injective D h)
    · exact absurd h (ne_conj D _ _)
    · exact absurd h.symm (ne_conj D _ _)
    · exact congrArg _ (embS_injective D (star_injective h))
  · intro φ
    by_cases h : ∃ τ, embS D τ = φ
    · obtain ⟨τ, hτ⟩ := h
      exact ⟨Sum.inl τ, hτ⟩
    · obtain ⟨τ, hτ⟩ := not_not.1 (fun h' => h ((range_iff D φ).2 h'))
      refine ⟨Sum.inr τ, ?_⟩
      show star (embS D τ) = φ
      rw [hτ]
      exact star_star φ

theorem existsUnique_place (w : InfinitePlace D.host.E) :
    ∃! τ, InfinitePlace.mk (embS D τ) = w := by
  have hex : ∃ τ, InfinitePlace.mk (embS D τ) = w := by
    obtain ⟨τ | τ, h⟩ := (sum_bijective D).2 w.embedding
    · exact ⟨τ, by rw [show embS D τ = w.embedding from h, InfinitePlace.mk_embedding]⟩
    · refine ⟨τ, ?_⟩
      rw [← InfinitePlace.mk_conjugate_eq,
        show ComplexEmbedding.conjugate (embS D τ) = w.embedding from h, InfinitePlace.mk_embedding]
  obtain ⟨τ, hτ⟩ := hex
  refine ⟨τ, hτ, fun τ' h' => ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 (h'.trans hτ.symm) with h | h
  · exact embS_injective D h
  · exact absurd h.symm (ne_conj D _ _)

theorem prod_norm (a : D.host.E) :
    ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have hb : Function.Bijective (fun τ => InfinitePlace.mk (embS D τ)) :=
    (Function.bijective_iff_existsUnique _).2 (existsUnique_place D)
  have h := InfinitePlace.prod_eq_abs_norm a
  rw [Rat.cast_abs] at h
  rw [← h, ← hb.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hc : (InfinitePlace.mk (embS D τ)).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff]
    exact fun hr => ne_conj D τ τ (ComplexEmbedding.isReal_iff.1 hr).symm
  rw [hc.mult_eq_two, InfinitePlace.apply]

theorem placeProd_eq (X : (D.host.E →+* ℂ) → ℝ) (h0 : ∀ φ, 0 ≤ X φ)
    (hc : ∀ φ, X (ComplexEmbedding.conjugate φ) = X φ) : placeProd X = ∏ τ, X (embS D τ) := by
  unfold placeProd
  rw [← (sum_bijective D).prod_comp, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hc]
  exact Real.sqrt_mul_self (Finset.prod_nonneg fun τ _ => h0 _)

theorem finrank_E : finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
  ring

theorem finrank_F : finrank ℚ D.host.F = D.R.f := by
  have h := finrank_mul_finrank ℚ D.host.F D.host.E
  rw [finrank_E, D.sp.cm.deg2] at h
  omega

theorem one_le_rdE : 1 ≤ D.host.rdE := by
  unfold Host.rdE
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (discr_ne_zero D.host.E)
  exact_mod_cast this

theorem absNorm_ddS :
    ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hpos : finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  unfold ddS Host.rdE
  rw [FractionalIdeal.coeIdeal_absNorm, h2, ← finrank_E, one_div,
    Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
  have h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
  rw [h3]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

end GlobalTheory.RealPlaces

theorem GlobalTheory.real_places_facts : ∀ D : D7, Fintype.card D.what₂.Tau = D.R.f ∧ finrank ℚ D.host.E = 2 * D.R.f ∧ finrank ℚ D.host.F = D.R.f ∧ D.R.m = 2 * D.R.rS + 2 ∧ 1 ≤ D.host.rdE ∧ (∀ τ (a : D.host.E), embS D τ (star a) = starRingEnd ℂ (embS D τ a)) ∧ (∀ a : D.host.E, ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)|) ∧ (∀ X : (D.host.E →+* ℂ) → ℝ, (∀ φ, 0 ≤ X φ) → (∀ φ, X (NumberField.ComplexEmbedding.conjugate φ) = X φ) → placeProd X = ∏ τ, X (embS D τ)) ∧ ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) ∧ (∀ w : InfinitePlace D.host.E, ∃! τ, InfinitePlace.mk (embS D τ) = w) := by
  intro D
  refine ⟨D.what₂.card_Tau, GlobalTheory.RealPlaces.finrank_E D, GlobalTheory.RealPlaces.finrank_F D, D.R.rS_two.symm,
    GlobalTheory.RealPlaces.one_le_rdE D, fun τ a => D.sp.cm.cmUnram.2.1 _ a, GlobalTheory.RealPlaces.prod_norm D,
    GlobalTheory.RealPlaces.placeProd_eq D, GlobalTheory.RealPlaces.absNorm_ddS D,
    GlobalTheory.RealPlaces.existsUnique_place D⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrEqv

section Count

variable {α : Type} {R : α → α → Prop}

theorem cntCl_eq_encard (hR : Equivalence R) (X : Set α) :
    cntCl X R = ((fun a => {b | R a b}) '' X).encard := by

  have hset : {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} =
      (fun O => {b | b ∈ O ∧ b ∈ X}) '' ((fun a => {b | R a b}) '' X) := by
    ext O
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨{b | R a b}, ⟨a, ha, rfl⟩, by ext b; simp [and_comm]⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by ext b; simp [and_comm]⟩
  rw [cntCl, hset]
  apply Set.InjOn.encard_image
  rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ hEq
  have hEq' : {b | b ∈ {b | R a b} ∧ b ∈ X} = {b | b ∈ {b | R a' b} ∧ b ∈ X} := hEq
  have hmem : a' ∈ {b | b ∈ {b | R a b} ∧ b ∈ X} := by
    rw [hEq']
    exact ⟨hR.refl a', ha'⟩
  have haa' : R a a' := hmem.1
  ext b
  exact ⟨fun hb => hR.trans (hR.symm haa') hb, fun hb => hR.trans haa' hb⟩

theorem encard_biUnion_le' {ι β : Type} (s : Finset ι) (Y : ι → Set β) :
    (⋃ i ∈ s, Y i).encard ≤ ∑ i ∈ s, (Y i).encard := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add le_rfl ih)

theorem cntCl_le_sum (hR : Equivalence R) {ι : Type} (s : Finset ι) (X : Set α) (Y : ι → Set α)
    (h : ∀ a ∈ X, ∃ i ∈ s, ∃ b ∈ Y i, R a b) : cntCl X R ≤ ∑ i ∈ s, cntCl (Y i) R := by
  simp only [cntCl_eq_encard hR]
  calc ((fun a => {b | R a b}) '' X).encard
      ≤ (⋃ i ∈ s, (fun a => {b | R a b}) '' Y i).encard := by
        apply Set.encard_le_encard
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨i, hi, b, hb, hab⟩ := h a ha
        refine Set.mem_biUnion hi ⟨b, hb, ?_⟩
        ext c
        exact ⟨fun hc => hR.trans hab hc, fun hc => hR.trans (hR.symm hab) hc⟩
    _ ≤ ∑ i ∈ s, ((fun a => {b | R a b}) '' Y i).encard := encard_biUnion_le' s _

end Count

section Grp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
  {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T}

theorem mem_gmap (g : S.V ≃ₗ[E] S.V) (x : S.V) : x ∈ Formalism.HermitianLatticesTheory.gmap g Λ ↔ g.symm x ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g.symm x, hx, by simp⟩

theorem aut_mem_iff {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) (x : S.V) : n x ∈ Λ ↔ x ∈ Λ := by
  have hx := mem_gmap (Λ := Λ) n (n x)
  rw [hn.2, LinearEquiv.symm_apply_apply] at hx
  exact hx

theorem Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) ≤ Submodule.span E (F.fl.e '' {i | i.1 < j + 1})
  exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => Nat.lt_succ_of_lt hi)

theorem X_le_orth : Xsp F ≤ orth S (Xsp F) := by

  have key : ∀ a, Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a)) := fun a => by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact F.fl.e_iso a b
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  have key2 : Xsp F ≤ LinearMap.ker (S.hT.flip y) := by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact key a hy
  simpa using key2 hx

theorem symm_sub_mem (n : S.V ≃ₗ[E] S.V) {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, n x - x ∈ A) : ∀ x ∈ B, n.symm x - x ∈ A := by
  intro x hx

  have hmap : ∀ y ∈ B, n y ∈ B := fun y hy => by simpa using B.add_mem (hAB (h y hy)) hy
  have hinj : Function.Injective (n.toLinearMap.restrict hmap) := fun a b hab =>
    Subtype.ext (n.injective (congrArg Subtype.val hab))
  obtain ⟨⟨y, hy⟩, hyx⟩ := LinearMap.surjective_of_injective hinj ⟨x, hx⟩
  have hny : n y = x := congrArg Subtype.val hyx
  have hy' : n.symm x = y := by rw [← hny, LinearEquiv.symm_apply_apply]
  rw [hy', ← neg_sub]
  have hxy := h y hy
  rw [hny] at hxy
  exact A.neg_mem hxy

theorem trans_sub_mem (n m : S.V ≃ₗ[E] S.V) {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, n x - x ∈ A) (h' : ∀ x ∈ B, m x - x ∈ A) : ∀ x ∈ B, (m * n) x - x ∈ A := by
  intro x hx
  have hnx : n x ∈ B := by simpa using B.add_mem (hAB (h x hx)) hx
  show m (n x) - x ∈ A
  have e : m (n x) - x = (m (n x) - n x) + (n x - x) := by abel
  rw [e]
  exact A.add_mem (h' _ hnx) (h x hx)

theorem one_mem_NLam : (1 : S.V ≃ₗ[E] S.V) ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).one_mem, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · ext x
    rw [mem_gmap]
    rfl
  · simp
  · simp

theorem mul_mem_NLam {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F) : m * n ∈ NLam Λ F := by
  have hsymm : ∀ {k : S.V ≃ₗ[E] S.V}, IsAutLam S Λ k → ∀ y, k.symm y ∈ Λ ↔ y ∈ Λ := fun hk y => by
    rw [← aut_mem_iff hk, LinearEquiv.apply_symm_apply]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem hm.1.1 hn.1.1, ?_⟩,
    fun j => trans_sub_mem n m (Xflag_mono j) (hn.2.1 j) (hm.2.1 j),
    trans_sub_mem n m X_le_orth hn.2.2 hm.2.2⟩
  ext x
  rw [mem_gmap]
  exact (hsymm hn.1 _).trans (hsymm hm.1 _)

theorem symm_mem_NLam {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : n.symm ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).inv_mem hn.1.1, ?_⟩,
    fun j => symm_sub_mem n (Xflag_mono j) (hn.2.1 j), symm_sub_mem n X_le_orth hn.2.2⟩
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm]
  exact aut_mem_iff hn.1 x

theorem frameAct_one {k : ℕ} (f : Fin k → S.V) : frameAct f 1 = f := by
  funext b
  simp only [frameAct]
  rw [Finset.sum_eq_single b (fun a _ hab => by rw [Matrix.one_apply_ne hab]; simp)
    (fun hb => absurd (Finset.mem_univ b) hb), Matrix.one_apply_eq]
  simp

theorem frameAct_mul {k : ℕ} (f : Fin k → S.V) (ξ η : Matrix (Fin k) (Fin k) (𝓞 E)) :
    frameAct (frameAct f ξ) η = frameAct f (ξ * η) := by
  funext b
  simp only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem map_frameAct {k : ℕ} (n : S.V ≃ₗ[E] S.V) (f : Fin k → S.V) (ξ : Matrix (Fin k) (Fin k) (𝓞 E)) :
    (fun a => n (frameAct f ξ a)) = frameAct (fun a => n (f a)) ξ := by
  funext b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [frameAct, map_sum, map_smul]

theorem uni_mul {k : ℕ} {O : Type} [CommRing O] {ξ η : Matrix (Fin k) (Fin k) O}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a b, b < a → η a b = 0) (a : Fin k) :
    (ξ * η) a a = ξ a a * η a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with hc | hc
    · rw [h1 a c hc, zero_mul]
    · rw [h2 c a hc, mul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

theorem uni_inv {k : ℕ} {O : Type} [CommRing O] {ξ : Matrix (Fin k) (Fin k) O}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    ∃ η : Matrix (Fin k) (Fin k) O, (∀ a b, b < a → η a b = 0) ∧ (∀ a, η a a = 1) ∧ ξ * η = 1 := by

  have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : ξ.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]
    simp [h2]
  have hu : IsUnit ξ.det := by
    rw [hdet]
    exact isUnit_one
  let _ := Matrix.invertibleOfIsUnitDet ξ hu
  have hinv : ξ⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have hmul : ξ * ξ⁻¹ = 1 := Matrix.mul_nonsing_inv ξ hu
  refine ⟨ξ⁻¹, fun a b hab => hinv hab, fun a => ?_, hmul⟩
  have hd := uni_mul h1 (fun a b hab => hinv hab) a
  rw [hmul, Matrix.one_apply_eq, h2, one_mul] at hd
  exact hd.symm

end Grp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem TEqv_equivalence (D : D7) (Λ : LatV D) {T T' : D.host.E} (F : Fg D T) :
    Equivalence (TEqv D Λ F (T' := T')) := by
  refine ⟨fun F' => ?_, fun {F₁ F₂} h => ?_, fun {F₁ F₂ F₃} h h' => ?_⟩
  · refine ⟨1, one_mem_NLam, 1, fun a b hab => Matrix.one_apply_ne (ne_of_gt hab), fun a => Matrix.one_apply_eq a, ?_⟩
    rw [frameAct_one]
    rfl
  · obtain ⟨n, hn, ξ, h1, h2, hfr⟩ := h
    obtain ⟨η, hη1, hη2, hξη⟩ := uni_inv h1 h2
    refine ⟨n.symm, symm_mem_NLam hn, η, hη1, hη2, ?_⟩
    rw [hfr, map_frameAct]
    simp only [LinearEquiv.symm_apply_apply]
    rw [frameAct_mul, hξη, frameAct_one]
  · obtain ⟨n, hn, ξ, h1, h2, hfr⟩ := h
    obtain ⟨m, hm, ζ, k1, k2, hfr'⟩ := h'
    refine ⟨m * n, mul_mem_NLam hn hm, ξ * ζ, fun a b hab => ?_, fun a => ?_, ?_⟩
    · exact Matrix.BlockTriangular.mul (b := id) (fun i j hij => h1 i j hij) (fun i j hij => k1 i j hij) hab
    · rw [uni_mul h1 k1 a, h2, k2, one_mul]
    · rw [hfr', hfr, map_frameAct, frameAct_mul]
      rfl

end GlobalTheory.LoopC.FrEqv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.FlagIso

theorem exists_extension {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ P : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤)
    (hsat : ∀ c : O, c ≠ 0 → ∀ v ∈ Λ, c • v ∈ P → v ∈ P) (f : V →ₗ[K] K)
    (hf : ∀ z ∈ P, f z ∈ (algebraMap O K).range) :
    ∃ g : V →ₗ[K] K, (∀ z ∈ Λ, g z ∈ (algebraMap O K).range) ∧ ∀ z ∈ Λ, z ∈ P → g z = f z := by
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := fun s => by
        have := isLocalizedModule_id (nonZeroDivisors O) V K
        exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
      surj := fun y => by
        have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
        obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
        rw [Submodule.span_eq] at hs
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := P.comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c (nonZeroDivisors.coe_ne_zero c) v v.2 h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  have hu : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O K) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors O) (Algebra.linearMap O K) x
  let g : V →ₗ[K] K := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype
        (f.restrictScalars O ∘ₗ Λ.subtype ∘ₗ π) hu)
  have hg : ∀ y : Λ, g y = f (π y) := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hu y
  refine ⟨g, fun z hz => ?_, fun z hz hP => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact hf _ (hπ _)
  · rw [hg ⟨z, hz⟩, hπ' ⟨z, hz⟩ hP]

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def hR (x : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun y := Formalism.UG.hform (starRingEnd E) J x y
  map_add' y z := by simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_apply (x y : Fin n → E) : hR J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hform_star (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (x y : Fin n → E) :
    star (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    exact this
  simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_hR_eq (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[E] E) : ∃ y, hR J y = g := by
  refine ⟨star ((fun j => g (Pi.single j 1)) ᵥ* J⁻¹), ?_⟩
  ext j
  have h1 : ((fun j => g (Pi.single j 1)) ᵥ* J⁻¹) ᵥ* J = fun j => g (Pi.single j 1) := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.vecMul_one]
  have h2 := congrFun h1 j
  simp only [LinearMap.comp_apply, LinearMap.single_apply, hR_apply]
  rw [← h2]
  simp only [Formalism.UG.hform, starRingEnd_apply, Pi.star_apply, star_star]
  simp [Pi.single_apply, Matrix.vecMul, dotProduct]

end Form

theorem star_mem_range {E : Type} [Field E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨⟨_, map_isIntegral_int (starRingEnd E) b.isIntegral_coe⟩, rfl⟩

theorem card_le_of_isotropic {n k : ℕ} (ε : Fin n → Bool) (u : Fin k → Fin n → ℂ)
    (hu : LinearIndependent ℂ u) (hiso : ∀ i j, star (u i) ⬝ᵥ (Jm ε *ᵥ u j) = 0) (b : Bool) :
    k ≤ (univ.filter fun a => ε a = b).card := by
  let T : (Fin k → ℂ) →ₗ[ℂ] ({a // ε a = b} → ℂ) :=
    LinearMap.funLeft ℂ ℂ Subtype.val ∘ₗ Fintype.linearCombination ℂ u
  have hT : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have h0 : star (∑ i, c i • u i) ⬝ᵥ (Jm ε *ᵥ ∑ i, c i • u i) = 0 := by
      simp only [star_sum, star_smul, sum_dotProduct, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul,
        smul_dotProduct, dotProduct_smul, hiso, smul_zero, Finset.sum_const_zero]
    have h1 : ∀ a, ε a = b → (∑ i, c i • u i) a = 0 := fun a ha => congrFun hc ⟨a, ha⟩
    have h3 : ∑ i, c i • u i = 0 := by
      generalize ∑ i, c i • u i = w at h0 h1
      have h2 : star w ⬝ᵥ (Jm ε *ᵥ w) = (if b then -1 else 1) * (star w ⬝ᵥ w) := by
        simp only [dotProduct, Jm, Matrix.mulVec_diagonal, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : ε a = b
        · simp [h1 a ha]
        · cases b <;> simp_all
      rw [h2] at h0
      have h4 : star w ⬝ᵥ w = 0 := by cases b <;> simpa using h0
      open ComplexOrder in exact dotProduct_star_self_eq_zero.1 h4
    funext i
    exact Fintype.linearIndependent_iff.1 hu c h3 i
  have := LinearMap.finrank_le_finrank_of_injective hT
  simpa [Fintype.card_subtype] using this

variable (I : AutInst)

theorem rkK_le_rkR (S : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hS : ∀ y ∈ S, ∀ z ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) (v : InfinitePlace I.F) :
    rkK S ≤ rkR (I.ε v) := by
  obtain ⟨b, hbS, -, hb⟩ := Submodule.exists_fun_fin_finrank_span_eq I.E (S : Set (Fin I.n → I.E))
  letI : Algebra I.E ℂ := (I.φ v).toAlgebra
  have h1 : LinearIndependent ℂ (fun i => (I.φ v) ∘ b i) :=
    (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 hb
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPi : ∀ w : Fin I.n → ℂ, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  have h2 : LinearIndependent ℂ (fun i => (I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b i)) := by
    apply LinearIndependent.of_comp (Matrix.mulVecLin (I.P v))
    simpa [Function.comp_def, hPi] using h1
  have h3 : ∀ i j, star ((I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b i)) ⬝ᵥ
      (Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b j))) = 0 := by
    intro i j
    rw [← I.P_spec v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPi, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec, hPi]
    have h4 := congrArg (I.φ v) (hS _ (hbS i) _ (hbS j))
    rw [map_zero] at h4
    rw [← h4]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_apply, I.cm.cmUnram.2.1, dotProduct,
      Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, Function.comp_apply, Matrix.map_apply]
  exact le_min (card_le_of_isotropic _ _ h2 h3 true) (card_le_of_isotropic _ _ h2 h3 false)

theorem mem_perpIn (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => map_zero (hR I.J s)⟩
  | add y z _ _ hy hz =>
    exact ⟨add_mem hy.1 hz.1, fun s hs => by
      rw [← hR_apply, map_add (f := _), hR_apply, hR_apply, hy.2 s hs, hz.2 s hs, add_zero]⟩
  | smul c y _ hy =>
    exact ⟨Submodule.smul_mem _ _ hy.1, fun s hs => by
      rw [← hR_apply, LinearMap.map_smul_of_tower, hR_apply, hy.2 s hs, smul_zero]⟩

theorem hform_span (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) {y s : Fin I.n → I.E}
    (hy : y ∈ Submodule.span I.E (perpIn I x S : Set (Fin I.n → I.E))) (hs : s ∈ S) :
    Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  have : Submodule.span I.E (perpIn I x S : Set (Fin I.n → I.E)) ≤ LinearMap.ker (hR I.J s) :=
    Submodule.span_le.2 fun z hz => ((mem_perpIn I x S z).1 hz).2 s hs
  exact this hy

theorem flag_isotropic : ∀ (I : AutInst) (x : I.GA), (∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2), Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) ∧ (∀ v, rkK (stepLt I x (1 / 2)) ≤ rkR (I.ε v)) ∧ ∀ R : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → ∀ y ∈ Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)), (∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ y' ∈ perpIn I x R, y - y' ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := by
  intro I x
  obtain ⟨-, -, hd1, hd2⟩ := GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
  have hiso : ∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2),
      Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 := by
    intro y hy z hz
    obtain ⟨-, -, h1, h2, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2) (by norm_num)
    obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2)⁻¹ (by norm_num)
    have h4 := h3 (h2 (1 / 2)⁻¹ (by norm_num) (h1 hz))
    rw [← (hd1 (1 / 2) (by norm_num)).2] at h4
    exact ((mem_perpIn I x _ z).1 h4).2 y hy
  refine ⟨hiso, rkK_le_rkR I _ hiso, fun R hR hRR y hy hint => ?_⟩
  obtain ⟨-, -, hpp, -⟩ := hd2 R R hR hR le_rfl
  obtain ⟨g, hg, hgf⟩ := exists_extension (lamX I x) (perpIn I x R) hfg hspan
    (fun c hc v hv h => by
      refine (mem_perpIn I x R v).2 ⟨hv, fun s hs => ?_⟩
      have h1 := ((mem_perpIn I x R _).1 h).2 s hs
      rw [← hR_apply, LinearMap.map_smul_of_tower] at h1
      exact (smul_eq_zero.1 h1).resolve_left hc)
    (FlagIso.hR I.J y) (fun z hz => by
      rw [hR_apply, ← hform_star _ I.J_herm]
      exact star_mem_range (hint z hz))
  obtain ⟨y', rfl⟩ := exists_hR_eq I.J I.J_det g
  have hy' : y' ∈ lamX I x := (hdual y').2 fun z hz => by
    rw [← hform_star _ I.J_herm]
    exact star_mem_range (hg z hz)
  have heq : ∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y' =
      Formalism.UG.hform (starRingEnd I.E) I.J z y := fun z hz => by
    rw [← hform_star _ I.J_herm, ← hform_star _ I.J_herm y]
    exact congrArg star (hgf z ((mem_perpIn I x R z).1 hz).1 hz)
  refine ⟨y', (mem_perpIn I x R y').2 ⟨hy', fun s hs => ?_⟩, ?_⟩
  · rw [heq s (hRR hs)]
    exact hform_span I x R hy hs
  · have h1 : y - y' ∈ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 I.E)) I.E _ _ h1
    rw [Submodule.span_eq] at hc
    have hc' : (c : 𝓞 I.E) • (y - y') ∈ lamX I x := hc
    have h2 : (c : 𝓞 I.E) • (y - y') ∈ R := by
      rw [← hpp]
      refine (mem_perpIn I x _ _).2 ⟨hc', fun s hs => ?_⟩
      rw [← hR_apply, LinearMap.map_smul_of_tower, map_sub, hR_apply, hR_apply, heq s hs, sub_self, smul_zero]
    have hc0 : algebraMap (𝓞 I.E) I.E c ≠ 0 := by
      simpa using nonZeroDivisors.coe_ne_zero c
    have h3 := Submodule.smul_mem (Submodule.span I.E (R : Set (Fin I.n → I.E)))
      (algebraMap (𝓞 I.E) I.E c)⁻¹ (Submodule.subset_span h2)
    rwa [← algebraMap_smul I.E (c : 𝓞 I.E), smul_smul, inv_mul_cancel₀ hc0, one_smul] at h3

end GlobalTheory.FlagIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDualStatement
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalLatticeFlag_isotropic_selfDual : ∀ (I : AutInst) (x : I.GA), (∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2), Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) ∧ (∀ v, rkK (stepLt I x (1 / 2)) ≤ rkR (I.ε v)) ∧ ∀ R : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → ∀ y ∈ Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)), (∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ y' ∈ perpIn I x R, y - y' ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := by
  first | exact @GlobalTheory.FlagIso.flag_isotropic | exact GlobalTheory.FlagIso.flag_isotropic | (intros; apply GlobalTheory.FlagIso.flag_isotropic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualOfAnisotropicOrthogonal
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem exists_dual_of_anisotropic_orthogonal (E : Type) [Field E] [StarRing E] (n m : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin m) (Fin m) E) (x : Fin n → E)
    (A : Matrix (Fin n) (Fin m) E) (hn : m + 1 = n) (hJ : Jᴴ = J) (hdet : J'.det ≠ 0)
    (hβ : star x ⬝ᵥ (J *ᵥ x) ≠ 0) (hx : star x ᵥ* (J * A) = 0) (hA : Aᴴ * J * A = J') :
    ∃ (u : Fin n → E) (A' : Matrix (Fin m) (Fin n) E), A' * A = 1 ∧ A' *ᵥ x = 0 ∧
      u ᵥ* A = 0 ∧ u ⬝ᵥ x = 1 ∧ vecMulVec x u + A * A' = 1 ∧ Aᴴ *ᵥ (J *ᵥ x) = 0 := by
  have h6 : Aᴴ *ᵥ (J *ᵥ x) = 0 := by
    have := congrArg star hx
    rw [Matrix.star_vecMul, star_star, Matrix.conjTranspose_mul, hJ, star_zero,
      ← Matrix.mulVec_mulVec] at this
    exact this
  obtain ⟨u, hu⟩ : ∃ u : Fin n → E, u = (star x ⬝ᵥ (J *ᵥ x))⁻¹ • (star x ᵥ* J) := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin m) (Fin n) E, A' = J'⁻¹ * Aᴴ * J := ⟨_, rfl⟩
  have h1 : A' * A = 1 := by
    rw [hA', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA]
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
  have h2 : A' *ᵥ x = 0 := by
    rw [hA', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h6, Matrix.mulVec_zero]
  have h3 : u ᵥ* A = 0 := by
    rw [hu, Matrix.smul_vecMul, Matrix.vecMul_vecMul, hx, smul_zero]
  have h4 : u ⬝ᵥ x = 1 := by
    rw [hu, smul_dotProduct, ← Matrix.dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hβ]
  refine ⟨u, A', h1, h2, h3, h4, ?_, h6⟩
  subst hn
  let C : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
    Matrix.of fun i j => (Fin.cons (x i) (fun k => A i k) : Fin (m + 1) → E) j
  let C' : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
    Matrix.of fun i j => (Fin.cons (u j) (fun k => A' k j) : Fin (m + 1) → E) i
  have hCC : C' * C = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [C, C', Matrix.mul_apply, dotProduct] using h4
    · have := congrFun h3 j
      simpa [C, C', Matrix.mul_apply, dotProduct, Matrix.vecMul, (Fin.succ_ne_zero j).symm] using this
    · have := congrFun h2 i
      simpa [C, C', Matrix.mul_apply, dotProduct, Matrix.mulVec, Fin.succ_ne_zero i] using this
    · have := congrFun (congrFun h1 i) j
      simpa [C, C', Matrix.mul_apply, Matrix.one_apply] using this
  have hCC' : C * C' = 1 := mul_eq_one_comm.mp hCC
  rw [← hCC']
  ext i j
  simp [C, C', Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMulVec_apply]

end GlobalTheory.StabUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
open Formalism.MainNotions Formalism.BasicNotions Filter

namespace GlobalTheory

theorem sizes_large_of_power_bounds {D : D7} (L : SizeData₂ D) (h : SizesAt L) (M : ℝ)
    (h1 : M ≤ L.sc.x ^ (1 / 4 : ℝ)) (h2 : M ≤ L.sc.x ^ L.sc.eps)
    (h3 : 5 * |M| * Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps) :
    M ≤ (D.R.m : ℝ) ∧ M ≤ L.sc.L ∧ (D.R.k : ℝ) ^ M ≤ L.sc.b ∧ D.host.rdE ≤ L.sc.b ∧
      (D.R.k : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ) := by
  obtain ⟨-, hM, hK, -, hT, hC, hQ, -, -, -, -, -, -, -, -, -, hD, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hL0 : 0 ≤ L.sc.L := by unfold Scale.L; positivity
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL0
  refine ⟨?_, h2, ?_, ?_, ?_⟩
  · refine h1.trans (le_trans ?_ hM.1)
    have e : Real.sqrt (L.sc.x * L.sc.delta1) = L.sc.x ^ ((1 + -(L.sc.eps / 8)) * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_mul hx0.le, Real.rpow_add hx0, Real.rpow_one]
      rfl
    rw [e, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold szTh
    linarith
  · have hk1 : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ D.R.k)
    have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := by
      refine hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
      unfold szTh
      linarith
    calc (D.R.k : ℝ) ^ M ≤ (D.R.k : ℝ) ^ |M| := Real.rpow_le_rpow_of_exponent_le hk1 (le_abs_self M)
      _ ≤ (L.sc.x ^ (5 : ℝ)) ^ |M| := Real.rpow_le_rpow (by linarith) hk5 (abs_nonneg M)
      _ = Real.exp (5 * |M| * Real.log L.sc.x) := by
          rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0, mul_comm]
      _ ≤ L.sc.b := Real.exp_le_exp.mpr h3
  · have hr := hQ.2.2.2.2.2.2.2
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
      have hn : ∀ n : ℕ, Real.sqrt n ≤ n := by
        intro n
        rw [Real.sqrt_le_left (by positivity)]
        exact_mod_cast Nat.le_self_pow two_ne_zero n
      exact_mod_cast hn (D.host.q * D.host.d)
    have hn0 : (0 : ℝ) ≤ D.R.n := by positivity
    have hqd : (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by positivity
    have hc : D.host.rdE ≤ szCond L := by
      unfold szCond
      nlinarith [mul_le_mul_of_nonneg_left hs hn0, mul_nonneg hn0 hqd]
    refine hc.trans ?_
    rcases le_total (szCond L) 1 with h | h
    · exact h.trans hb1
    · have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ hT.1
      calc szCond L ≤ szCond L ^ 36 := le_self_pow₀ h (by norm_num)
        _ ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 := le_mul_of_one_le_right (by positivity) ht
        _ ≤ Real.sqrt L.sc.b := hC
        _ ≤ L.sc.b := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
  · refine le_trans ?_ hD.1
    have : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    gcongr

theorem family_sizes_eventually_large : ∀ (eps : ℝ) (Fm : FamP eps) (M : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Fm.x1 < x ∧ M ≤ ((Fm.D x i).R.m : ℝ) ∧ M ≤ (Fm.L x i).sc.L ∧ ((Fm.D x i).R.k : ℝ) ^ M ≤ (Fm.L x i).sc.b ∧ (Fm.D x i).host.rdE ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * ((Fm.D x i).R.m : ℝ) ^ 10 ≤ ((Fm.D x i).s.Del : ℝ) := by
  intro eps Fm M
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]
    exact (Fm.L 0 i).sc.eps_pos
  have e1 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop M
  have e2 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ eps := (tendsto_rpow_atTop he).eventually_ge_atTop M
  have e3 : ∀ᶠ x : ℝ in atTop, 5 * |M| * Real.log x ≤ x ^ eps := by
    have := ((isLittleO_log_rpow_atTop he).const_mul_left (5 * |M|)).bound one_pos
    filter_upwards [this, eventually_ge_atTop 0] with x hx h0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)] at hx
    exact (le_abs_self _).trans hx
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp (e1.and (e2.and (e3.and (eventually_gt_atTop Fm.x1))))
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx0 x hx
  refine ⟨a4, sizes_large_of_power_bounds (Fm.L x i) (Fm.sizes x a4 i) M ?_ ?_ ?_⟩ <;>
    simp only [Fm.L_x x i a4, Fm.L_eps x i] <;> assumption

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarComplexGLMatricesConjAndSingularNull
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarComplexGLMatricesConjAndSingularNull
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

private lemma continuous_det_of' (j : ℕ) :
    Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := by
  fun_prop

theorem measurable_haarLoc_density (j : ℕ) :
    Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) := by
  have hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_det_of' j).measurable
  exact ENNReal.measurable_ofReal.comp ((hd.norm.pow_const 2).inv.pow_const j)

theorem measurePreserving_withDensity_of_invariant {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) {g : X → ENNReal} (hg : Measurable g) (hfg : ∀ x, g (f x) = g x) :
    MeasurePreserving f (μ.withDensity g) (μ.withDensity g) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  conv_rhs => rw [← hf.map_eq]
  rw [setLIntegral_map hs hg hf.measurable]
  simp only [hfg]

theorem haarLoc_conj_and_null : ∀ j : ℕ, MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s)) (haarLoc j) (haarLoc j) ∧ haarLoc j {x | (Matrix.of x).det = 0} = 0 := by
  intro j
  have hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (show Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det by fun_prop).measurable
  constructor
  ·
    have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume := by
      have h := Complex.conjLIE.measurePreserving
      have e : (⇑Complex.conjLIE : ℂ → ℂ) = ⇑(starRingEnd ℂ) := funext Complex.conjLIE_apply
      rwa [e] at h
    have hv : MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s))
        (volume : Measure (Fin j → Fin j → ℂ)) volume :=
      volume_preserving_pi fun _ => volume_preserving_pi fun _ => hc
    refine measurePreserving_withDensity_of_invariant hv (measurable_haarLoc_density j) ?_
    intro x
    have hdet : (Matrix.of fun r s => starRingEnd ℂ (x r s)).det = starRingEnd ℂ (Matrix.of x).det :=
      ((starRingEnd ℂ).map_det (Matrix.of x)).symm
    simp only [hdet, Complex.norm_conj]
  ·
    have hS : MeasurableSet {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0} :=
      measurableSet_eq_fun hd measurable_const
    rw [haarLoc, withDensity_apply _ hS, ← lintegral_indicator hS]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have : ({x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0}.indicator
          fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)) = 0 := by
        funext x
        by_cases hx : (Matrix.of x).det = 0
        · simp [hx, zero_pow hj.ne']
        · simp [Set.indicator_of_notMem (show x ∉ {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0} from hx)]
      rw [this, Pi.zero_def, lintegral_zero]

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarComplexGLMatricesConjAndSingularNullStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarComplexGLMatrices_conj_and_singular_null : ∀ j : ℕ, MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s)) (haarLoc j) (haarLoc j) ∧ haarLoc j {x | (Matrix.of x).det = 0} = 0 := by
  first | exact @GlobalTheory.LeviIso.haarLoc_conj_and_null | exact GlobalTheory.LeviIso.haarLoc_conj_and_null | (intros; apply GlobalTheory.LeviIso.haarLoc_conj_and_null <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeft
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm

theorem map_haarGL_mul_left_eq : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (γ : MatInf E j), 0 < detNorm E j γ → (haarGL E j).map (fun g => γ * g) = haarGL E j :=
  fun E _ _ j γ h => (GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j γ h).2.map_eq

end GlobalTheory.OrbitTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeftStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (γ : MatInf E j), 0 < detNorm E j γ → (haarGL E j).map (fun g => γ * g) = haarGL E j := by
  first | exact @GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq | exact GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq | (intros; apply GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq <;> assumption)
end
end

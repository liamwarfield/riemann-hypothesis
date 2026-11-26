module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompletedTensorMatrixSplitSemilocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ResEtaFOfPow

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  have hr : NumberField.ComplexEmbedding.IsReal τ := by
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have e := h.2.2.2 τ x
    rw [hc] at e
    exact e.symm
  have hc2 := h.2.1.isComplex (NumberField.InfinitePlace.mk τ)
  exact (NumberField.InfinitePlace.isComplex_mk_iff.1 hc2) hr


variable (F E) in
abbrev normI : (AF F ⊗[F] E)ˣ →* (AF F)ˣ := Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)


variable (F E) in
abbrev normGrp : Subgroup (AF F)ˣ :=
  (Units.map (algebraMap F (AF F)).toMonoidHom).range ⊔ (normI F E).range

theorem algebraMap_inj : Function.Injective (algebraMap (AF F) (AF F ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

theorem exists_form {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : F, ¬ IsSquare δ ∧
    ∀ a : (AF F)ˣ, a ∈ (normI F E).range ↔
      ∃ x y : AF F, (a : AF F) = x ^ 2 - algebraMap F (AF F) δ * y ^ 2 := by
  obtain ⟨δ, hδ, hh⟩ := GlobalTheory.T.quadraticExt_norm_form_over_algebra F E σ h.2.2.1 (sig_invol h) (sig_ne h)
  obtain ⟨h1, h2⟩ := hh (AF F)
  have hN : ∀ z : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) (Algebra.norm (AF F) z) =
      z * sigR (AF F) σ z := fun z => by
    obtain ⟨x, y, e1, e2⟩ := h1 z
    rw [e1, e2]
  refine ⟨δ, hδ, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, y, e1, -⟩ := h1 z
    exact ⟨x, y, e1⟩
  · rintro ⟨x, y, e⟩
    obtain ⟨z, hz⟩ := h2 x y
    rw [← e] at hz
    have hu : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ a.isUnit.map _)
    refine ⟨hu.unit, Units.ext (algebraMap_inj (F := F) (E := E) ?_)⟩
    exact (hN z).trans hz

theorem isOpen_normGrp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : IsOpen (normGrp F E : Set (AF F)ˣ) := by
  obtain ⟨δ, hδ, hf⟩ := exists_form h
  have h0 : δ ≠ 0 := fun e => hδ (e ▸ IsSquare.zero)
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one F δ h0) fun a ha => ?_)
  exact Subgroup.mem_sup_right ((hf a).2 ha)

theorem normGrp_ne_top {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : normGrp F E ≠ ⊤ := by
  obtain ⟨δ, hδ, hf⟩ := exists_form h
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare F δ hδ
  intro e
  have hm : a ∈ normGrp F E := e ▸ Subgroup.mem_top a
  obtain ⟨_, ⟨t, rfl⟩, n, hn, rfl⟩ := Subgroup.mem_sup.1 hm
  obtain ⟨x, y, e⟩ := (hf n).1 hn
  exact ha t x y (by rw [Units.val_mul, e]; rfl)

theorem sq_mem_normGrp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : (AF F)ˣ) : a * a ∈ normGrp F E := by
  obtain ⟨δ, -, hf⟩ := exists_form h
  exact Subgroup.mem_sup_right ((hf _).2 ⟨a, 0, by simp [pow_two]⟩)

theorem exists_isEtaF {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ η : (AF F)ˣ →* Circle, Formalism.IndefR.DatumF.IsEtaF E η := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ normGrp F E := by
    by_contra hc
    push_neg at hc
    exact normGrp_ne_top h (eq_top_iff.2 fun a _ => hc a)
  obtain ⟨η, h1, h2⟩ := GlobalTheory.VolHeckeCompare.exists_char_of_not_mem _ (sq_mem_normGrp h) a ha
  refine ⟨η, ?_, fun b => h1 (Subgroup.mem_sup_left ⟨b, rfl⟩), fun x => h1 (Subgroup.mem_sup_right ⟨x, rfl⟩),
    fun e => h2 (by rw [e]; rfl)⟩
  refine continuous_of_continuousAt_one η ?_
  refine (continuousAt_const (y := (1 : Circle))).congr ?_
  filter_upwards [(isOpen_normGrp h).mem_nhds (one_mem _)] with b hb
  exact (h1 hb).symm


open Classical in
theorem resEtaF_of_resEtaPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → Formalism.IndefR.DatumF.ResEtaF χ n := by
  intro F E _ _ _ _ _ σ B hB χ n hχ
  have hcm : IsCMExt F E σ := hB.cm
  refine ⟨exists_isEtaF hcm, fun η hη a => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hη
  have hS : ∀ x ∈ normGrp F E, η x = 1 := by
    have : normGrp F E ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  have hsq : ∀ x, η x * η x = 1 := fun x => by rw [← map_mul]; exact hS _ (sq_mem_normGrp hcm x)
  have key : ∀ x, ((χ (Formalism.IndefR.DatumF.idFF F E x) : Circle) : ℂ) = if x ∈ normGrp F E then 1 else (-1) ^ n :=
    fun x => hχ x
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ normGrp F E
  · rw [if_pos ha, hS a ha]; simp
  rw [if_neg ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push_neg at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ normGrp F E := fun hm => hb (hS b hm)
  have hab : a * b ∈ normGrp F E := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]

end GlobalTheory.ResEtaFOfPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSigStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → Formalism.IndefR.DatumF.ResEtaF χ n := by
  first | exact @GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow | exact GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow | (intros; apply GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMeanValueNonnegative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilocalConjugateSameCharpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOpenHopfOrder
open Matrix Polynomial
open GlobalTheory.ClassParam (krylov krylov_map exists_cyclic_field)

namespace GlobalTheory.SemilocalConj

theorem exists_cyclic_of_finite_maximal {R : Type} [CommRing R]
    (hfin : Set.Finite {I : Ideal R | I.IsMaximal}) {r : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (hs : g.charpoly.Separable) : ∃ v, IsUnit (krylov g v).det := by
  classical
  haveI : Finite (MaximalSpectrum R) := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun m : MaximalSpectrum R =>
      (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal R | I.IsMaximal}))
      (fun a b h => MaximalSpectrum.ext (congrArg Subtype.val h))
  have hloc : ∀ m : MaximalSpectrum R, ∃ v : Fin r → R ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : R, ∀ m : MaximalSpectrum R,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum R => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

theorem conj_of_charpoly_eq_of_separable : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} →
    ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable →
      ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u := by
  intro R _ hfin n γ δ hχ hs
  obtain ⟨v, hv⟩ := exists_cyclic_of_finite_maximal hfin γ hs
  obtain ⟨w, hw⟩ := exists_cyclic_of_finite_maximal hfin δ (hχ ▸ hs)
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have h1 := GlobalTheory.Orb.mul_krylov_eq γ v
  have h2 := GlobalTheory.Orb.mul_krylov_eq δ w
  rw [← ha] at h1
  rw [← hb, ← hχ] at h2
  refine ⟨a * b⁻¹, ?_⟩
  set C := GlobalTheory.Orb.companionMat n γ.charpoly
  rw [Units.val_mul]
  calc (a : Matrix (Fin n) (Fin n) R) * ↑b⁻¹ * δ = ↑a * ↑b⁻¹ * (δ * ↑b) * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = ↑a * ↑b⁻¹ * (↑b * C) * ↑b⁻¹ := by rw [h2]
    _ = ↑a * C * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = γ * ↑a * ↑b⁻¹ := by rw [h1]
    _ = γ * (↑a * ↑b⁻¹) := by rw [mul_assoc]

end GlobalTheory.SemilocalConj
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilocal_conjugate_same_charpoly : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} → ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable → ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u := by
  first | (exact @GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable) | (exact GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable) | (intros; apply GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable <;> assumption)
end

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf.KottLat

variable {p : ℕ} [Fact p.Prime]

theorem isIntV_add (G : HTGroup p) (v : AwayP p) {a b : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a)
    (hb : IsIntV G v b) : IsIntV G v (a + b) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact Subring.add_mem _ (ha i) (hb i)

theorem isIntV_zero (G : HTGroup p) (v : AwayP p) : IsIntV G v 0 := fun i => by
  rw [map_zero, Finsupp.zero_apply]; exact Subring.zero_mem _

theorem eventually_isIntV_map (G : HTGroup p) (y : AfP p ⊗[ℚ] G.C) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      IsIntV G v (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) y) := by
  induction y using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun v => by rw [map_zero]; exact isIntV_zero G v
  | tmul a c =>
    have h1 : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
        AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ := a.2
    have h2 : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i,
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) ∈ v.1.adicCompletionIntegers ℚ := by
      simp only [Filter.eventually_all]; intro i; exact eventually_rat_mem_integers _
    filter_upwards [h1, h2] with v hv1 hv2 i
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsIntV, basV,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact Subring.mul_mem _ hv1 (hv2 i)
  | add y z hy hz =>
    filter_upwards [hy, hz] with v h1 h2
    rw [map_add (f := _)]; exact isIntV_add G v h1 h2

end GlobalTheory.OrbFinAf.KottLat

namespace GlobalTheory.OrbFinAf.KottLat

theorem conj_integral {A K : Type} [Ring A] [CommRing K] {n : ℕ} (R : Subring K)
    (Φ : Matrix (Fin n) (Fin n) K ≃+* A) (hfin : Set.Finite {I : Ideal R | I.IsMaximal})
    (Q : Polynomial R) (hQs : Q.Separable) (γ₀ : Aˣ) (hQm : Q.map R.subtype = (Φ.symm γ₀).charpoly)
    (hγ : ∀ i j, Φ.symm γ₀ i j ∈ R) (g : Aˣ) (hδ : ∀ i j, Φ.symm ((g⁻¹ * γ₀ * g : Aˣ) : A) i j ∈ R) :
    ∃ U : Aˣ, U * (g⁻¹ * γ₀ * g) = γ₀ * U ∧ (∀ i j, Φ.symm (U : A) i j ∈ R) ∧
      (∀ i j, Φ.symm ((U⁻¹ : Aˣ) : A) i j ∈ R) := by
  have lift : ∀ a : A, (∀ i j, Φ.symm a i j ∈ R) →
      ∃ M : Matrix (Fin n) (Fin n) R, M.map R.subtype = Φ.symm a :=
    fun a h => ⟨fun i j => ⟨_, h i j⟩, by ext i j; rfl⟩
  obtain ⟨Γ, hΓ⟩ := lift _ hγ
  obtain ⟨Δ, hΔ⟩ := lift _ hδ
  have hcΓ : Γ.charpoly.map R.subtype = (Φ.symm γ₀).charpoly := by
    rw [← Matrix.charpoly_map, hΓ]
  have hcΔ : Δ.charpoly.map R.subtype = (Φ.symm γ₀).charpoly := by
    rw [← Matrix.charpoly_map, hΔ]
    have e : Φ.symm ((g⁻¹ * γ₀ * g : Aˣ) : A) =
        (((Units.map (Φ.symm : A ≃+* _).toRingHom.toMonoidHom g)⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K) * Φ.symm γ₀ *
        ((Units.map (Φ.symm : A ≃+* _).toRingHom.toMonoidHom g : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K) := by
      rw [Units.val_mul, Units.val_mul, map_mul, map_mul]; rfl
    rw [e, Matrix.charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  have hinj : Function.Injective (Polynomial.map R.subtype) :=
    Polynomial.map_injective _ Subtype.val_injective
  have heq : Γ.charpoly = Δ.charpoly := hinj (hcΓ.trans hcΔ.symm)
  have hQ : Q = Γ.charpoly := hinj (hQm.trans hcΓ.symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.semilocal_conjugate_same_charpoly R hfin n Γ Δ heq (hQ ▸ hQs)
  let F : Matrix (Fin n) (Fin n) R →* A := (Φ.toRingHom.comp R.subtype.mapMatrix).toMonoidHom
  let U : Aˣ := Units.map F u
  have hUs : Φ.symm (U : A) = (u : Matrix (Fin n) (Fin n) R).map R.subtype := Φ.symm_apply_apply _
  have hUs' : Φ.symm ((U⁻¹ : Aˣ) : A) = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map R.subtype := by
    rw [show U⁻¹ = Units.map F u⁻¹ from (map_inv (Units.map F) u).symm]
    exact Φ.symm_apply_apply _
  refine ⟨U, Units.ext (Φ.symm.injective ?_), fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul U, Units.val_mul γ₀, map_mul, map_mul, hUs, ← hΔ, ← hΓ, ← Matrix.map_mul,
      ← Matrix.map_mul, hu]
  · rw [hUs, Matrix.map_apply]; exact (u : Matrix (Fin n) (Fin n) R) i j |>.2
  · rw [hUs', Matrix.map_apply]; exact ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j |>.2

end GlobalTheory.OrbFinAf.KottLat

namespace GlobalTheory.OrbFinAf.KottLat

end GlobalTheory.OrbFinAf.KottLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemLatGHat
namespace GlobalTheory.AdMark

open scoped Matrix

theorem exists_lift {R S La U A : Type} [CommRing R] [CommRing S] [AddCommGroup La] [Module R La] [Module.Projective R La]
    [AddCommGroup U] [Module R U] [AddCommGroup A] [Module S A] (φ : R → S) (fv : U →+ A)
    (hfv : ∀ c x, fv (c • x) = φ c • fv x) (K : A →ₗ[S] A) (hKi : Function.Injective K) (H₁ Hk : AddSubgroup A)
    (hsm : ∀ c, ∀ z ∈ Hk, φ c • z ∈ Hk) (L : Submodule R U) (ι : La →ₗ[R] U) (hι : Function.Injective ι) (N : ℕ)
    (hL : ∀ v, v ∈ L ↔ fv v ∈ Hk) (hK : ∀ z, z ∈ Hk ↔ ∃ y ∈ H₁, K y = z)
    (h1 : ∀ v, fv v ∈ H₁ ↔ ∃ a, ι a = v)
    (ap1 : ∀ y ∈ H₁, ∃ a, ∃ w ∈ H₁, y = fv (ι a) + N • w)
    (apk : ∀ z ∈ Hk, ∃ x ∈ L, ∃ w ∈ Hk, z = fv x + N • w)
    (hdiv : ∀ x z, fv x = N • z → ∃ w, fv w = z ∧ x = N • w) :
    ∃ mk : La →ₗ[R] U, (∀ a, mk a ∈ L) ∧ (∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w) ∧
      (∀ a, (∃ u ∈ L, mk a = N • u) → ∃ b, a = N • b) ∧ ∀ v ∈ L, ∃ a, ∃ u ∈ L, v = mk a + N • u := by
  let P : Submodule R (U × La) :=
    { carrier := {p | p.1 ∈ L ∧ ∃ w ∈ Hk, fv p.1 - K (fv (ι p.2)) = N • w}
      zero_mem' := ⟨L.zero_mem, 0, zero_mem _, by simp⟩
      add_mem' := by
        rintro p q ⟨hp, w, hw, e⟩ ⟨hq, w', hw', e'⟩
        refine ⟨L.add_mem hp hq, w + w', add_mem hw hw', ?_⟩
        rw [smul_add, ← e, ← e']
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        abel
      smul_mem' := by
        rintro c p ⟨hp, w, hw, e⟩
        refine ⟨L.smul_mem c hp, φ c • w, hsm c w hw, ?_⟩
        rw [smul_comm N, ← e]
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, hfv, smul_sub] }
  have hs : Function.Surjective ((LinearMap.snd R U La) ∘ₗ P.subtype) := by
    intro a
    obtain ⟨x, hx, w, hw, e⟩ := apk _ ((hK _).2 ⟨_, (h1 _).2 ⟨a, rfl⟩, rfl⟩)
    exact ⟨⟨(x, a), hx, -w, neg_mem hw, by rw [e]; simp⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  have hs2 : ∀ a, (s a).1.2 = a := fun a => LinearMap.congr_fun hs a
  let mk : La →ₗ[R] U := (LinearMap.fst R U La) ∘ₗ P.subtype ∘ₗ s
  have m1 : ∀ a, mk a ∈ L := fun a => (s a).2.1
  have m2 : ∀ a, ∃ w ∈ Hk, fv (mk a) - K (fv (ι a)) = N • w := fun a => by
    obtain ⟨w, hw, e⟩ := (s a).2.2
    rw [hs2] at e
    exact ⟨w, hw, e⟩
  refine ⟨mk, m1, m2, ?_, ?_⟩
  · rintro a ⟨u, hu, e⟩
    obtain ⟨w, hw, e'⟩ := m2 a
    obtain ⟨y, hy, ey⟩ := (hK _).1 (sub_mem ((hL u).1 hu) hw)
    have : fv (ι a) = N • y := by
      apply hKi
      rw [map_nsmul, ey, smul_sub, ← e', e, map_nsmul]
      abel
    obtain ⟨x, rfl, ex⟩ := hdiv _ _ this
    obtain ⟨b, rfl⟩ := (h1 _).1 hy
    exact ⟨b, hι (by rw [ex, map_nsmul])⟩
  · intro v hv
    obtain ⟨y, hy, ey⟩ := (hK _).1 ((hL v).1 hv)
    obtain ⟨a, w, hw, rfl⟩ := ap1 y hy
    obtain ⟨w', hw', e'⟩ := m2 a
    obtain ⟨u, hu, eu⟩ := hdiv (v - mk a) (K w - w') (by
      rw [map_sub, ← ey, smul_sub, ← e', map_add (f := _), map_nsmul]
      abel)
    refine ⟨a, u, (hL u).2 (hu ▸ sub_mem ((hK _).2 ⟨w, hw, rfl⟩) hw'), ?_⟩
    rw [← eu]
    abel

theorem sub_congr {A : Type} [AddCommGroup A] {x y z w w' : A} {M N c : ℕ} (hc : N = M * c) (e : y - z = M • w)
    (e' : x - z = N • w') : x - y = M • (c • w' - w) := by
  rw [smul_sub, ← mul_smul, ← hc, ← e, ← e']
  abel

end GlobalTheory.AdMark

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdMark

theorem latR_rfl {E : Type} [Field E] [NumberField E] {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E)) :
    latR rfl L = L := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem smul_mem_latGHat {D : D7} (W : HSp D) (k : GA D W) (c : 𝓞 D.host.E) :
    ∀ z ∈ latGHat W k, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z ∈ latGHat W k := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c • a, (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha, z, hz, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, ← _root_.mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_marking : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Geo.Tor.Level H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → l.M ∣ l₂.M → l₂.Mb ≤ l.Mb → ∀ k : GA D W, ∃ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), IsMark l₂ (latR hr (latG W k)) mk₂ ∧ MarkAd l₂ W hr ι k mk₂ ∧ ∀ mk, (∀ a, mk a ∈ latR hr (latG W k)) → MarkAd l W hr ι k mk → MarkOver l l₂ (latR hr (latG W k)) mk mk₂ := by
  intro D H Dw l l₂ W r hr ι hι hM hMb k
  subst hr
  rw [latR_rfl]
  haveI := Dw.proj
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hM2 : l₂.M ≠ 0 := by have := l₂.three_le; omega
  let fv : (Fin W.rank → D.host.E) →+ (Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (finVec W) (GlobalTheory.AdLat.cap_fv_add D.host.F)
  have ap : ∀ g : GA D W, ∀ z ∈ latGHat W g, ∃ x ∈ latG W g, ∃ w ∈ latGHat W g, z = fv x + l₂.M • w := by
    intro g
    obtain ⟨a1, a2, -, -, a5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D W g
    rw [a5]
    exact (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ a1 a2).2.1 l₂.M (Nat.pos_of_ne_zero hM2)
  obtain ⟨mk₂, m1, m2, m3, m4⟩ := exists_lift (fun c : 𝓞 D.host.E => (1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) fv
    (fun c x => by
      funext i
      change (1 : Af D.host.F) ⊗ₜ[D.host.F] ((c : D.host.E) * x i) = _ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one])
    (finHom W k).1.mulVecLin
    (fun x y h => by
      have := congrArg (fun v => ((finHom W k)⁻¹).1 *ᵥ v) h
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using this)
    (latGHat W 1) (latGHat W k) (smul_mem_latGHat W k) (latG W k) ι hι.1 l₂.M
    (GlobalTheory.MarkCoset.latG_spec D W k).1 (GlobalTheory.MarkCoset.latG_spec D W k).2
    (fun v => ((GlobalTheory.MarkCoset.latG_spec D W 1).1 v).symm.trans (by rw [← hι.2]; rfl))
    (fun y hy => by
      obtain ⟨x, hx, h⟩ := ap 1 y hy
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, h⟩)
    (ap k) (GlobalTheory.MarkCoset.finVec_div W l₂.M hM2)
  refine ⟨mk₂, ⟨m1, fun a _ => m3 a, fun v hv => ?_⟩, fun a _ => m2 a, fun mk _ hmk a ha => ?_⟩
  · refine Submodule.smul_induction_on hv (fun m hm v hv => ?_) (fun x y hx hy => ?_)
    · obtain ⟨a, u, hu, rfl⟩ := m4 v hv
      refine ⟨m • a, Submodule.smul_mem_smul hm trivial, m • u, Submodule.smul_mem _ m hu, ?_⟩
      rw [smul_add, map_smul, smul_comm m]
    · obtain ⟨a, ha, u, hu, rfl⟩ := hx
      obtain ⟨a', ha', u', hu', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', u + u', add_mem hu hu', by rw [map_add (f := _), smul_add]; abel⟩
  · obtain ⟨c, hc⟩ := hM
    obtain ⟨w, hw, e⟩ := hmk a (Submodule.smul_mono_left (Ideal.map_mono hMb) ha)
    obtain ⟨w', hw', e'⟩ := m2 a
    replace e : fv (mk a) - (finHom W k).1.mulVecLin (fv (ι a)) = l.M • w := e
    obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w) (by
      exact (fv.map_sub _ _).trans (sub_congr hc e e'))
    refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W k).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
    rw [← eu]
    abel

end GlobalTheory.AdMark
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.EtaSignReal

open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_signToCircle [Algebra.IsQuadraticExtension F E] (η : (AF F)ˣ →* Circle) (hη : IsEtaF E η) :
    η = signToCircle.comp (normSign E) := by
  obtain ⟨-, h1, h3, h4⟩ := hη
  refine eq_signToCircle_comp _ η (fun a ha => ?_) h4
  obtain ⟨t, x, hx⟩ := (normSign_eq_one_iff E a).1 ha
  rw [← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]
  exact h1 t

theorem finComp_eq_one {a : (AF F)ˣ} (ha : At (evI F) ((a : AF F) - 1)) : finComp a = 1 := by
  have h := ha ((0 : Ainf F), (1 : Af F)) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : ((a : AF F) - 1).2 = 0 := by
    have := congrArg Prod.snd h
    change (1 : Af F) * ((a : AF F) - 1).2 = 0 at this
    rwa [one_mul] at this
  have h3 : (a : AF F).2 = 1 := sub_eq_zero.1 (h2 : (a : AF F).2 - 1 = 0)
  funext v
  apply Units.ext
  change (a : AF F).2 v = 1
  rw [h3]
  rfl

theorem normSign_eq_prod [Algebra.IsQuadraticExtension F E] {a : (AF F)ˣ} (ha : finComp a = 1) :
    normSign E a = ∏ w : InfinitePlace F, eta F E w.Completion (infComp a w) := by
  change etaProd F E (finComp a) (infComp a) = _
  rw [etaProd, ha]
  have : ∀ v : HeightOneSpectrum (𝓞 F), eta F E (v.adicCompletion F) ((1 : FinFam F) v) = 1 :=
    fun v => eta_eq_one_iff.2 (one_mem _)
  simp only [this, finprod_one, one_mul]

theorem ringEquivReal_neg {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) {δ : F} (hδ : δ ≠ 0) {θ : E} (hθ : σ θ = -θ) (h1 : θ * θ = algebraMap F E δ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion δ) < 0 := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set z := τ.1 θ
  have hz : star z = -z := by rw [← hcm.2.2.2 τ.1 θ, hθ, map_neg]
  have hre : z.re = 0 := by
    have := congrArg Complex.re hz
    simp at this
    linarith
  have hc : ((e (algebraMap F w.Completion δ) : ℝ) : ℂ) = z * z := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    have h5 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion δ) = w.embedding δ := by
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply, InfinitePlace.Completion.extensionEmbedding_coe]
      rfl
    rw [h5, ← τ.2, RingHom.comp_apply, ← h1, map_mul]
  have hr := congrArg Complex.re hc
  simp only [Complex.ofReal_re, Complex.mul_re, hre, zero_mul, zero_sub] at hr
  have hne : e (algebraMap F w.Completion δ) ≠ 0 := (map_ne_zero e).2 ((map_ne_zero _).2 hδ)
  refine lt_of_le_of_ne ?_ hne
  rw [hr]
  nlinarith [mul_self_nonneg z.im]

theorem mem_normGroup_iff_pos {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) (x : (w.Completion)ˣ) :
    x ∈ normGroup F E w.Completion ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (x : w.Completion) := by
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.1.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra h
    push_neg at h
    haveI := hcm.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ.1)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact (hcm.2.2.2 τ.1 x).symm.trans (by rw [h x])
  obtain ⟨δ, b, hδ, h0, hσb, h1⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hcm.2.2.1 hinv hne
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hneg := ringEquivReal_neg hcm hw τ hδ0 hσb h1
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  rw [mem_normGroup_iff_form b h0 h1]
  constructor
  · rintro ⟨p, q, h⟩
    have hx0 : e (x : w.Completion) ≠ 0 := (map_ne_zero e).2 x.ne_zero
    have h2 : e (x : w.Completion) = e p ^ 2 - e (algebraMap F w.Completion δ) * e q ^ 2 := by
      rw [h, map_sub, map_mul, map_pow, map_pow]
    refine lt_of_le_of_ne ?_ hx0.symm
    rw [h2]
    nlinarith [sq_nonneg (e p), sq_nonneg (e q)]
  · intro hpos
    refine ⟨e.symm (Real.sqrt (e x)), 0, ?_⟩
    apply e.injective
    simp [Real.sq_sqrt hpos.le]

theorem piInf_idFF {w : InfinitePlace F} (hw : w.IsReal) (τ : EmbOver E w) (a : (AF F)ˣ) :
    piInf τ ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion) : ℝ) : ℂ) := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  change infEmb τ (compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) a)) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  rfl

theorem eta_eq_prod_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg : r < 0 := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [if_neg (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]

end GlobalTheory.EtaSignReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSignsStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmQuadraticCharacter_eq_prod_realSigns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  first | exact @GlobalTheory.EtaSignReal.eta_eq_prod_sign | exact GlobalTheory.EtaSignReal.eta_eq_prod_sign | (intros; apply GlobalTheory.EtaSignReal.eta_eq_prod_sign <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicVectorHermitianRankGeThreeIndefin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicVectorHermitianRankGeThreeIndefin
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HermIso

theorem posIndex_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) :
    GlobalTheory.Inertia.posIndex M = r := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
    Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))
  have hD : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1) = D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [D, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map (starRingEnd ℂ) = D.submatrix e.symm e.symm := by
    rw [← hD, ← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply]
  have hdet : A'.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hA'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_submatrix_equiv_self,
      Matrix.det_diagonal] at h1
    simp [Fintype.prod_sum_type] at h1
    exact pow_ne_zero s (by norm_num) h1.symm
  rw [← GlobalTheory.Inertia.posIndex_congr M hdet, hA', GlobalTheory.Inertia.posIndex_submatrix_equiv,
    GlobalTheory.Inertia.posIndex_diagonal]
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp

theorem exists_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), 3 ≤ n → 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∃ x : Fin n → E, x ≠ 0 ∧ form σ Y.J x x = 0 := by
  intro F E _ _ _ _ _ σ B hB n Y r s hn hr hs hY
  obtain ⟨-, hEC, h2, hconj⟩ := hB.cm
  obtain ⟨w0⟩ : Nonempty (InfinitePlace E) := inferInstance
  have invol : ∀ x, σ (σ x) = x := fun x =>
    w0.embedding.injective (by rw [hconj, hconj, star_star])
  let σe : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext invol) (AlgHom.ext invol)
  have hne : σe ≠ 1 := by
    intro h
    have hid : ∀ x, σ x = x := fun x => by simpa [σe] using DFunLike.congr_fun h x
    have hre : ComplexEmbedding.IsReal w0.embedding :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj w0.embedding x
        rw [hid] at this
        exact this.symm)
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEC.isComplex w0) (InfinitePlace.isReal_iff.2 hre)
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨hc, hF, θ, hθ0, hθ⟩ := GlobalTheory.HermGlobal.involutive_and_fixed hne
  obtain ⟨P, g, hP, hPg, hgf, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    two_ne_zero (fun t => invol t) (G := Y.J) (fun a b => hY.herm b a)
  have hgf' : ∀ i, σ (g i) = g i := fun i => hgf i
  have key : ∀ y : Fin n → E,
      form σ Y.J (P *ᵥ y) (P *ᵥ y) = y ⬝ᵥ Matrix.diagonal g *ᵥ (fun i => σ (y i)) := by
    intro y
    have h1 : (fun i => σ ((P *ᵥ y) i)) = (P.map (σ : E →+* E)) *ᵥ (fun i => σ (y i)) := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [form, h1, ← hPg]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  by_cases hz : ∃ i, g i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨P *ᵥ Pi.single i 1, fun h => ?_, ?_⟩
    · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) i
      simp at this
    · rw [key]
      simp [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply, hi]
  push_neg at hz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsg : ∀ τ : E →+* ℂ, (∀ x, τ (σe x) = conj (τ x)) →
      ∃ i : Fin m, (0 < (τ (g i.succ)).re ↔ 0 < (τ (-g 0)).re) := by
    intro τ _
    have hre : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun c => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj τ (algebraMap F E c)
        rw [AlgHom.commutes] at this
        exact this.symm)
    have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
      InfinitePlace.embedding_mk_eq_of_isReal hre
    set w := InfinitePlace.mk (τ.comp (algebraMap F E))
    set τ' := (B.emb w).1
    have hτ' : ∀ c : F, τ' (algebraMap F E c) = τ (algebraMap F E c) := fun c => by
      have := congrArg (fun f => f c) ((B.emb w).2.trans hw)
      simpa using this
    have hgτ : ∀ k, τ' (g k) = τ (g k) := fun k => by
      obtain ⟨c, hc'⟩ := (hF (g k)).1 (hgf' k)
      rw [← hc', hτ']
    have hcong : (Matrix.diagonal g).map τ' =
        (P.map τ')ᵀ * Y.J.map τ' * (P.map τ').map (starRingEnd ℂ) := by
      rw [← hPg, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      congr 1
      ext a b
      simp [hconj]
    have hPd : (P.map τ').det ≠ 0 := by
      rw [show (P.map τ').det = τ' P.det from (RingHom.map_det τ' P).symm]
      exact (map_ne_zero τ').2 hP
    have hcount : (Finset.univ.filter fun k => 0 < (τ (g k)).re).card = r := by
      have := GlobalTheory.Inertia.posIndex_congr (Y.J.map τ') hPd
      rw [← hcong, posIndex_of_hasSig (hY.sig w), Matrix.diagonal_map (map_zero _),
        GlobalTheory.Inertia.posIndex_diagonal] at this
      simpa [hgτ] using this
    have hrn : r < m + 1 := by have := (hY.sig w).1; omega
    have him : (τ (g 0)).im = 0 := by
      have h := hconj τ (g 0)
      rw [hgf' 0] at h
      exact Complex.conj_eq_iff_im.1 h.symm
    have hne0 : τ (g 0) ≠ 0 := (map_ne_zero τ).2 (hz 0)
    by_cases hp : 0 < (τ (g 0)).re
    · obtain ⟨k, hk⟩ : ∃ k, ¬ 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = Finset.univ :=
          Finset.filter_true_of_mem fun k _ => hall k
        rw [h', Finset.card_univ, Fintype.card_fin] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hk hp)
      refine ⟨i, iff_of_false hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
    · have hneg : (τ (g 0)).re < 0 := by
        rcases lt_or_eq_of_le (not_lt.1 hp) with h | h
        · exact h
        · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hne0
      obtain ⟨k, hk⟩ : ∃ k, 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = ∅ :=
          Finset.filter_false_of_mem fun k _ => not_lt.2 (hall k)
        rw [h', Finset.card_empty] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hp hk)
      refine ⟨i, iff_of_true hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
  obtain ⟨z, hz'⟩ := GlobalTheory.HermGlobal.exists_represent hc hF hθ0 hθ (r := m) (by omega)
    (g := fun i => g i.succ) (fun i => hgf' _) (fun i => hz _) (b := -g 0)
    (by simp [σe, hgf']) (neg_ne_zero.2 (hz 0)) hsg
  refine ⟨P *ᵥ Fin.cons 1 z, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [key]
    simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      map_one, one_mul, mul_one] at hz' ⊢
    simp only [σe, Function.comp_apply, RingHom.coe_coe, AlgEquiv.ofAlgHom_apply] at hz'
    linear_combination hz'

end GlobalTheory.HermIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicVectorHermitianRankGeThreeIndefinStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_vector_hermitian_rank_ge_three_indefinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), 3 ≤ n → 1 ≤ r → 1 ≤ s → Y.IsHerm σ B r s →
    ∃ x : Fin n → E, x ≠ 0 ∧ form σ Y.J x x = 0 := by
  first | exact @GlobalTheory.HermIso.exists_isotropic | exact GlobalTheory.HermIso.exists_isotropic | (intros; apply GlobalTheory.HermIso.exists_isotropic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGramComp
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.RestrictNorm

theorem hasGram_comp {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (N : (K →+* ℂ) → V → ℝ) (φ : W →ₗ[K] V) (hφ : Function.Injective φ) {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hG : IsGram b X N) :
    HasGram (fun σ (x : W) => N σ (φ x)) := by
  haveI : Module.Finite K V := Module.Finite.of_basis b
  let e : W ≃ₗ[K] LinearMap.range φ := LinearEquiv.ofInjective φ hφ
  let c := Module.finBasis K (LinearMap.range φ)
  obtain ⟨Y, hY, hn⟩ := GlobalTheory.Mem.DivInhab.exists_frames_restrict b X (fun v => (hG v).1) (LinearMap.range φ) c
  refine IsGram.hasGram (b := c.map e.symm) (X := Y) fun v => ⟨hY v, fun x => ?_⟩
  have h1 : Formalism.HermitianLatticesTheory.normAt (c.map e.symm) Y v x = Formalism.HermitianLatticesTheory.normAt c Y v (e x) := by
    have hv : Formalism.HermitianLatticesTheory.vecAt (c.map e.symm) v x = Formalism.HermitianLatticesTheory.vecAt c v (e x) := by
      funext i
      simp only [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [hv]
  rw [h1, hn, (hG v).2]
  rfl

theorem restrict_deg : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (φ : W →ₗ[K] V), Function.Injective φ → HasGram N → HasGram (fun σ (x : W) => N σ (φ x)) ∧ ∀ L : Submodule (𝓞 K) W, L.FG → Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = Formalism.HN.rkK L ∧ deg N (L.map (φ.restrictScalars (𝓞 K))) = deg (fun σ (x : W) => N σ (φ x)) L := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N φ hφ hN
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  have hN' := hasGram_comp N φ hφ b X hG
  refine ⟨hN', fun L hL => ?_⟩
  obtain ⟨⟨m, ⟨c, Y⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hr := Formalism.HN.rerealize K W (Fin m) V (Fin n) c Y b X φ (fun v => (hG' v).1) (fun v => (hG v).1) hφ
    (fun v x => by rw [(hG v).2, (hG' v).2]) L hL
  have hrk : Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = Formalism.HN.rkK L := by
    unfold Formalism.HN.rkK
    have hs : Submodule.span K ((L.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
        (Submodule.span K (L : Set W)).map φ := by
      rw [Submodule.map_coe, ← Submodule.span_image]
      rfl
    rw [hs]
    exact (Submodule.equivMapOfInjective φ hφ _).finrank_eq.symm
  refine ⟨hrk, ?_⟩
  unfold GlobalTheory.AllWt.deg GlobalTheory.AllWt.slope
  rw [hrk, slope_sq_eq hG (hL.map _), slope_sq_eq hG' hL]
  unfold Formalism.HN.muDef
  rw [hr.2.2.1]

end GlobalTheory.RestrictNorm
end
end

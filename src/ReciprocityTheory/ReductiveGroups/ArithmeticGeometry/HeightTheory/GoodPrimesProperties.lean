module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussGenericHeight.GaussGenericStatements.GaussGenericTheorem.HtGaussGen

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessTheorem.HtGaussUniq
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.AdmissibleValuationPrimeSubsingleton
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.ImgRSuccAbove
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.ExistsSmulOfLine
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

theorem mem_vRing_iff {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) (x : Ω) :
    x ∈ vRing v ↔ 0 ≤ v x := by
  rfl

theorem pos_of_not_isUnit {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ))
    (x : vRing v) (hx : ¬ IsUnit x) : 0 < v (x : Ω) := by
  have h0 : 0 ≤ v (x : Ω) := x.2
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have hx0 : (x : Ω) ≠ 0 := by
      intro h'
      rw [h', AddValuation.map_zero] at h
      exact WithTop.top_ne_zero h.symm
    have hinv : (x : Ω)⁻¹ ∈ vRing v := by
      show 0 ≤ v ((x : Ω)⁻¹)
      rw [AddValuation.map_inv, ← h, neg_zero]
    exact ⟨⟨x, ⟨(x : Ω)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem ratio_eq_of {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  unfold ratio
  have hex : ∃ a : Ω, f = a • g := ⟨a, h⟩
  rw [dite_eq_left hex]
  have h2 := hex.choose_spec
  exact smul_left_injective Ω hg (h.symm.trans h2).symm

theorem exists_smul_of_line {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    {l : Submodule Ω V} (h1 : Module.finrank Ω l = 1) {f g : V} (hf : f ∈ l) (hg : g ∈ l)
    (hg0 : g ≠ 0) : ∃ a : Ω, f = a • g := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hg⟩ : l) (by simpa using hg0)).mp h1 ⟨f, hf⟩
  refine ⟨c, ?_⟩
  have h2 := congrArg Subtype.val hc
  simpa using h2.symm

theorem eq_of_le_ht {R : Type*} [CommRing R] [IsDomain R] {Q P : Ideal R} [Q.IsPrime]
    [P.IsPrime] (hP : P.height = 1) (hQ : Q ≠ ⊥) (hle : Q ≤ P) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hle hne
  have hP1 : P.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hP]; rfl
  have h1 : Q.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp hP1) Q inferInstance hlt
  have h2 : Q.height = 0 := ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast h1)
  have hmin := Ideal.height_eq_zero_iff.mp h2
  have hbot : Q ≤ ⊥ := hmin.2 ⟨Ideal.isPrime_bot, le_refl _⟩ bot_le
  exact hQ (le_bot_iff.mp hbot)

theorem sac_same {α : Type*} {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α) :
    Fin.succAboveCases (α := fun _ => α) i x f i = x := Fin.insertNth_apply_same (α := fun _ => α) i x f

theorem sac_succAbove {α : Type*} {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α)
    (k : Fin n) : Fin.succAboveCases (α := fun _ => α) i x f (i.succAbove k) = f k := Fin.insertNth_apply_succAbove (α := fun _ => α) i x f k

end GaussValuationUniqueness
end

namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

noncomputable def imgR {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (p : TVar D N) : MvPolynomial (SVar D N) R :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) R) j0
    (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (ρ k))
    (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2

theorem imgR_same {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (i : Fin (D + 1)) : imgR (D := D) j0 ρ (i, j0) = if i = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (ρ k) := by
  unfold imgR
  exact sac_same j0 _ _

theorem imgR_succAbove {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (i : Fin (D + 1)) (k : Fin N) :
    imgR (D := D) j0 ρ (i, j0.succAbove k) = MvPolynomial.X (Sum.inr (i, k)) := by
  unfold imgR
  exact sac_succAbove j0 _ _ k

theorem imgR_map {R R' : Type*} [CommRing R] [CommRing R'] {D N : ℕ} (φ : R →+* R')
    (j0 : Fin (N + 1)) (ρ : Fin N → R) (t : TVar D N) :
    MvPolynomial.map φ (imgR j0 ρ t) = imgR j0 (fun k => φ (ρ k)) t := by
  obtain ⟨i, j⟩ := t
  rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
  · rw [imgR_same, imgR_same]
    split_ifs
    · exact MvPolynomial.map_X φ _
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_neg, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  · rw [imgR_succAbove, imgR_succAbove, MvPolynomial.map_X]

section Ker

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

theorem alg_mem (hv : IsTrivOn K v) (x : K) : algebraMap K Ω x ∈ vRing v := by
  rw [mem_vRing_iff]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [hv x hx]

noncomputable def kap (hv : IsTrivOn K v) : K →+* vRing v :=
  (algebraMap K Ω).codRestrict (vRing v) (alg_mem v hv)

noncomputable def psiT (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (ρ : Fin N → vRing v) :
    MvPolynomial (TVar D N) K →+* MvPolynomial (SVar D N) (vRing v) :=
  MvPolynomial.eval₂Hom ((MvPolynomial.C : vRing v →+* MvPolynomial (SVar D N) (vRing v)).comp
    (kap v hv)) (imgR j0 ρ)

noncomputable def psiR (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (ρ : Fin N → vRing v) :
    MvPolynomial (TVar D N) K →+* MvPolynomial (SVar D N) (IsLocalRing.ResidueField (vRing v)) :=
  (MvPolynomial.map (IsLocalRing.residue (vRing v))).comp (psiT (D := D) v hv j0 ρ)

theorem pos_of_ker {w : AddValuation (OmS Ω D N) (WithTop ℤ)}
    (hw : ∀ a : Ω, w (algebraMap Ω (OmS Ω D N) a) = v a)
    (e : SVar D N → OmS Ω D N) (he : ∀ s, 0 ≤ w (e s))
    (q : MvPolynomial (SVar D N) (vRing v))
    (hq : MvPolynomial.map (IsLocalRing.residue (vRing v)) q = 0) :
    0 < w (MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) e q) := by
  rw [MvPolynomial.eval₂_eq]
  refine Finset.sum_induction _ (fun x => 0 < w x)
    (fun a b ha hb => lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add w a b)) (by simp) ?_
  intro d _
  have hprod : 0 ≤ w (∏ s ∈ d.support, e s ^ d s) :=
    Finset.prod_induction _ (fun x => 0 ≤ w x)
      (fun a b ha hb => by rw [AddValuation.map_mul]; exact add_nonneg ha hb)
      (le_of_eq (AddValuation.map_one w).symm)
      (fun s _ => by rw [AddValuation.map_pow]; exact nsmul_nonneg (he s) _)
  have hnu : ¬ IsUnit (q.coeff d) := by
    have h0 := congrArg (AddMonoidAlgebra.coeff · d) hq
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h0
    exact (IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0)
  have hc : 0 < w (((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) (q.coeff d)) := by
    rw [RingHom.comp_apply, hw]
    exact pos_of_not_isUnit v _ hnu
  rw [AddValuation.map_mul]
  exact lt_of_lt_of_le hc (le_add_of_nonneg_right hprod)

end Ker

end GaussValuationUniqueness
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.SHomFactor
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

theorem sImg_rel {Ω : Type} [Field Ω] {D N : ℕ} (jc : Fin (N + 1)) (b : Fin (N + 1) → Ω)
    (hb : b jc = 1) (i : Fin (D + 1)) (hi : i ≠ 0) :
    ∑ j, sImg (D := D) jc (fun k => b (jc.succAbove k)) (i, j) *
      algebraMap Ω (OmS Ω D N) (b j) = 0 := by
  rw [Fin.sum_univ_succAbove _ jc]
  simp only [sImg, GaussValuationUniqueness.sac_same, GaussValuationUniqueness.sac_succAbove, if_neg hi, hb, map_one,
    mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
    MvPolynomial.algebraMap_eq, ← map_mul, ← map_sum, ← map_add, neg_add_cancel, map_zero]

noncomputable def eS {Ω : Type} [Field Ω] {D N : ℕ} (jc j0 : Fin (N + 1)) (x : Fin N → Ω) :
    SVar D N → OmS Ω D N :=
  Sum.elim (fun _ => sImg jc x (0, j0)) (fun ik => sImg jc x (ik.1, j0.succAbove ik.2))

section Fac

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

theorem sub_apply (y : vRing v) : (vRing v).subtype y = (y : Ω) := rfl

theorem sHom_factor (hv : IsTrivOn K v) (jc j0 : Fin (N + 1)) (x : Fin N → Ω)
    (a : Fin (N + 1) → Ω) (ha : ∀ j, a j ∈ vRing v) (ha0 : a j0 = 1)
    (hrel : ∀ i : Fin (D + 1), i ≠ 0 →
      ∑ j, sImg jc x (i, j) * algebraMap Ω (OmS Ω D N) (a j) = 0) (f : MvPolynomial (TVar D N) K) :
    sHom (K := K) jc x f = MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
      (eS jc j0 x) (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) f) := by
  have key : ((sHom (K := K) jc x : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N) :
      MvPolynomial (TVar D N) K →+* OmS Ω D N) =
      (MvPolynomial.eval₂Hom ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
        (eS jc j0 x)).comp (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, sHom,
        MvPolynomial.aeval_C, psiT, MvPolynomial.eval₂Hom_C, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C]
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
      rfl
    · rintro ⟨i, j⟩
      rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same]
        · have h := hrel i hi
          rw [Fin.sum_univ_succAbove _ j, ha0, map_one, mul_one] at h
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same, hi, GaussValuationUniqueness.sub_apply]
          linear_combination h
      · simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_succAbove]
  exact RingHom.congr_fun key f

end Fac

end GaussValuationUniqueness
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.NotInjOfTrdeg
namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

theorem not_inj_of_trdeg {F E : Type} [Field F] [Field E] [Algebra F E] {D N : ℕ} (S : Set E)
    (j0 : Fin (N + 1)) (ρ : Fin N → IntermediateField.adjoin F S) (hD : 1 ≤ D)
    (htr : Algebra.trdeg F (IntermediateField.adjoin F S) = ((D - 1 : ℕ) : Cardinal)) :
    ¬ Function.Injective (MvPolynomial.aeval (R := F) (imgR (D := D) j0 ρ)) := by
  intro hinj
  have hai : AlgebraicIndependent F (imgR (D := D) j0 ρ) := hinj
  have h1 := hai.cardinalMk_le_trdeg
  first
  | rw [← Algebra.trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  | rw [← trdeg_add_eq F (IntermediateField.adjoin F S)] at h1
  rw [htr, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at h1
  have hT : Fintype.card (TVar D N) = (D + 1) * (N + 1) := by simp [TVar]
  have hS : Fintype.card (SVar D N) = 1 + (D + 1) * N := by simp [SVar]
  rw [Cardinal.mk_fintype, Cardinal.mk_fintype, hT, hS] at h1
  norm_cast at h1
  rw [show (D + 1) * (N + 1) = (D + 1) * N + (D + 1) by ring] at h1
  generalize (D + 1) * N = P at h1
  omega

section Tr

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

noncomputable def gK (hv : IsTrivOn K v) :
    K →+* IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)) :=
  (IsLocalRing.residue _).comp ((RingHom.id K).codRestrict ((vRing v).comap (algebraMap K Ω))
    (fun x => by rw [ValuationSubring.mem_comap]; exact alg_mem v hv x))

theorem gK_surj (hv : IsTrivOn K v) : Function.Surjective (gK v hv) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨x.1, rfl⟩

end Tr

end GaussValuationUniqueness
end

namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0 NumberField

theorem admissibleValuation_prime_subsingleton {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT]
    {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : Data K ι Ω WT A) : LeafSt.AdmissibleValuationPrimeUnique 𝒜 d := by
  intro hd _ c v hAdm hK p1 hp1 p2 hp2
  obtain ⟨hH1, w1, hw1, hv1⟩ := hp1
  obtain ⟨hH2, w2, hw2, hv2⟩ := hp2

  have hRC : d.ResCond c v (d.D - 1) := by
    rcases hAdm.2 with ⟨la, hla, _⟩ | ⟨_, hRC⟩
    · exfalso
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
      have h1 := (hla z).mpr hz
      have hK0 : ((z : 𝓞 K) : K) ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hz0
      rw [hK _ hK0] at h1
      exact lt_irrefl _ h1
    · exact hRC
  obtain ⟨_, j0, hj0, hnn, htr⟩ := hRC
  set a : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w j0 c) with ha_def
  have ha : ∀ j, a j ∈ vRing v := fun j => (GaussValuationUniqueness.mem_vRing_iff v _).mpr (hnn j)
  have hQne : RingHom.ker
      (GaussValuationUniqueness.psiR (D := d.D) v hK j0
        (fun k => ⟨a (j0.succAbove k), ha _⟩)) ≠ ⊥ := by
    letI := resAlg (F := K) v
    intro hbot
    let S : Set (IsLocalRing.ResidueField (vRing v)) :=
      {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}
    let ρL : Fin d.N → IntermediateField.adjoin
        (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K (Ω c)))) S :=
      fun k => ⟨IsLocalRing.residue (vRing v) ⟨a (j0.succAbove k), ha _⟩,
        IntermediateField.subset_adjoin _ _ ⟨j0.succAbove k, ha _, rfl⟩⟩
    have hni := GaussValuationUniqueness.not_inj_of_trdeg (D := d.D) S j0 ρL
      (by have := hd.D_ge; omega) htr
    rw [injective_iff_map_eq_zero] at hni
    push_neg at hni
    obtain ⟨G, hG0, hG⟩ := hni
    obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective
      (GaussValuationUniqueness.gK v hK) (GaussValuationUniqueness.gK_surj v hK) G
    have hf : f ≠ 0 := by
      rintro rfl
      exact hG (map_zero _)
    have H : GaussValuationUniqueness.psiR (D := d.D) v hK j0
          (fun k => ⟨a (j0.succAbove k), ha _⟩) =
        (MvPolynomial.map (algebraMap
          (IntermediateField.adjoin
            (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K (Ω c)))) S)
          (IsLocalRing.ResidueField (vRing v)))).comp
        (((MvPolynomial.aeval (imgR (D := d.D) j0 ρL)).toRingHom).comp
          (MvPolynomial.map (gK v hK))) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [GaussValuationUniqueness.psiR, GaussValuationUniqueness.psiT,
          RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
          MvPolynomial.algebraMap_apply]
        congr 1
      · intro t
        simp only [GaussValuationUniqueness.psiR, GaussValuationUniqueness.psiT,
          RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
        rw [GaussValuationUniqueness.imgR_map, GaussValuationUniqueness.imgR_map]
        rfl
    have hmem : f ∈ RingHom.ker
        (GaussValuationUniqueness.psiR (D := d.D) v hK j0
          (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
      rw [RingHom.mem_ker, H]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hG0, map_zero]
    rw [hbot] at hmem
    exact hf (Ideal.mem_bot.mp hmem)
  set Q := RingHom.ker (GaussValuationUniqueness.psiR (D := d.D) v hK j0 (fun k => ⟨a (j0.succAbove k), ha _⟩))
    with hQ
  haveI : Q.IsPrime := RingHom.ker_isPrime _

  have hbase := hd.w_base c
  have hline := hd.finrank_one c d.wL
  set b : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) with hb_def
  have hα : ∀ j, d.w j c = b j • d.w (d.jc c) c := by
    intro j
    obtain ⟨α, hα⟩ := GaussValuationUniqueness.exists_smul_of_line hline (hd.w_mem j c) (hd.w_mem _ c) hbase
    rw [hb_def]
    simp only
    rw [GaussValuationUniqueness.ratio_eq_of hbase hα]
    exact hα
  have hb : b (d.jc c) = 1 := GaussValuationUniqueness.ratio_eq_of hbase (one_smul _ _).symm
  have hb0 : b j0 ≠ 0 := by
    intro h0
    apply hj0
    rw [hα j0, h0, zero_smul]
  have hab : ∀ j, a j = b j * (b j0)⁻¹ := by
    intro j
    apply GaussValuationUniqueness.ratio_eq_of hj0
    rw [hα j, hα j0, smul_smul, mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  have ha0 : a j0 = 1 := by rw [hab, mul_inv_cancel₀ hb0]
  have hrel : ∀ i : Fin (d.D + 1), i ≠ 0 →
      ∑ j, sImg (D := d.D) (d.jc c) (d.x c) (i, j) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a j) = 0 := by
    intro i hi
    have rel : ∑ j, sImg (D := d.D) (d.jc c) (d.x c) (i, j) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (b j) = 0 := sImg_rel (d.jc c) b hb i hi
    simp_rw [hab, map_mul, ← mul_assoc]
    rw [← Finset.sum_mul, rel, zero_mul]

  have key : ∀ p, ∀ w ∈ d.GoodP c p, d.Wres c w = v → Q ≤ p := by
    intro p w hw hwv f hf
    have hOv := hw.1
    have hwv' : ∀ t : Ω c, w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) t) = v t := by
      intro t; rw [← hwv]; rfl
    have he : ∀ s, 0 ≤ w (GaussValuationUniqueness.eS (D := d.D) (d.jc c) j0 (d.x c) s) := by
      intro s
      rcases s with u | ik
      · have e1 : GaussValuationUniqueness.eS (D := d.D) (d.jc c) j0 (d.x c) (Sum.inl u) =
            d.sH c (MvPolynomial.X ((0, j0) : TVar d.D d.N)) := by
          simp [GaussValuationUniqueness.eS, Data.sH, sHom]
        rw [e1]; exact (hOv.2 _).1
      · have e1 : GaussValuationUniqueness.eS (D := d.D) (d.jc c) j0 (d.x c) (Sum.inr ik) =
            d.sH c (MvPolynomial.X ((ik.1, j0.succAbove ik.2) : TVar d.D d.N)) := by
          simp [GaussValuationUniqueness.eS, Data.sH, sHom]
        rw [e1]; exact (hOv.2 _).1
    have hq : MvPolynomial.map (IsLocalRing.residue (vRing v))
        (GaussValuationUniqueness.psiT (D := d.D) v hK j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) f) = 0 :=
      RingHom.mem_ker.mp hf
    have hpos := GaussValuationUniqueness.pos_of_ker v hwv' _ he _ hq
    have hfac := GaussValuationUniqueness.sHom_factor v hK (d.jc c) j0 (d.x c) a ha ha0 hrel f
    rw [← hfac] at hpos
    exact (hOv.2 f).2.mp hpos
  haveI := hH1.1
  haveI := hH2.1
  have e1 := GaussValuationUniqueness.eq_of_le_ht hH1.2 hQne (key p1 w1 hw1 hv1)
  have e2 := GaussValuationUniqueness.eq_of_le_ht hH2.2 hQne (key p2 w2 hw2 hv2)
  rw [← e1, ← e2]

end GaussValuationUniqueness
end

open NumberField

theorem HtGaussUniq {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.AdmissibleValuationPrimeUnique 𝒜 d :=
  GaussValuationUniqueness.admissibleValuation_prime_subsingleton 𝒜 d
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AdmissibleValuationPrimeUnique
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem AdmissibleValuationPrimeUnique (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∀ v : AddValuation (Ω c) (WithTop ℤ), d.admitted c v → IsTrivOn K v →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}.Subsingleton :=
  HtGaussUniq 𝒜 d hd h c

theorem GeneratorMultiHomogeneous (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p) :=
  HtGaussGen 𝒜 d (Data.PlaceTrivialOrPositive (𝒜 := 𝒜) d) (Data.AdmissibleValuationPrimeUnique (𝒜 := 𝒜) d) hd h c

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem good_primes_properties (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    (∀ v : AddValuation (Ω c) (WithTop ℤ), d.admitted c v → IsTrivOn K v →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}.Subsingleton) ∧
    (∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p)) ∧
    (∀ (G : WT) (ta : A c), ta ∈ 𝒜 c G → ta ≠ 0 →
      {p | p ∈ d.HtOne ∧ d.nP h c G ta p ≠ 0}.Finite) ∧
    (∀ ta : A c, ta ∈ 𝒜 c d.wL → ta ≠ 0 → {p | p ∈ d.HtOne ∧ d.nPMM h c ta p ≠ 0}.Finite) := by
  classical
  have hgoodI : ∀ {p : Ideal (KTp K d.D d.N)}, p ∈ d.HtOne →
      ∀ {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)}, w ∈ d.GoodP c p →
        d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) := by
    intro p hp w hw
    rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with h1 | ⟨hadm, htriv, -⟩
    · obtain ⟨a, ha, hne⟩ := hw.2
      exact absurd (h1 a ha) hne
    · exact ⟨hadm, htriv⟩

  have hcover : ∀ (V : Set (AddValuation (Ω c) (WithTop ℤ))), V.Finite →
      ∀ S : Set (Ideal (KTp K d.D d.N)),
        (∀ p ∈ S, p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w ∈ V) → S.Finite := by
    intro V hV S hS
    have hfin : (⋃ v ∈ V, {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}).Finite := by
      refine hV.biUnion fun v _ => ?_
      by_cases hv' : d.admitted c v ∧ IsTrivOn K v
      · exact (d.AdmissibleValuationPrimeUnique hd h c v hv'.1 hv'.2).finite
      · refine Set.Subsingleton.finite ?_
        rintro p ⟨hp, w, hw, rfl⟩
        exact absurd (hgoodI hp hw) hv'
    refine hfin.subset ?_
    intro p hpS
    obtain ⟨hp, w, hw, hwV⟩ := hS p hpS
    exact Set.mem_biUnion hwV ⟨hp, w, hw, rfl⟩
  refine ⟨d.AdmissibleValuationPrimeUnique hd h c, d.GeneratorMultiHomogeneous hd h c, ?_, ?_⟩
  · intro G ta hta hta0
    refine hcover {v | d.admitted c v ∧ d.ord c v G ta ≠ 0} (hd.a3' c hta hta0) _ ?_
    rintro p ⟨hp, hne⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hne
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_
    have := hcon w hw
    simp only [Set.mem_setOf_eq, not_and, not_not] at this
    rw [this (hgoodI hp hw).1, mul_zero]
  · intro ta hta hta0
    let V : Set (AddValuation (Ω c) (WithTop ℤ)) :=
      {v | d.admitted c v ∧ d.ord c v d.wL ta ≠ 0} ∪
        ⋃ j : {j // d.w j c ≠ 0}, {v | d.admitted c v ∧ d.ord c v d.wL (d.w j c) ≠ 0}
    have hV : V.Finite := (hd.a3' c hta hta0).union
      (Set.finite_iUnion fun j => hd.a3' c (hd.w_mem j c) j.2)
    refine hcover V hV _ ?_
    rintro p ⟨hp, hne⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hne
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_
    have hnot := hcon w hw
    have hadm := (hgoodI hp hw).1
    have h1 : d.ord c (d.Wres c w) d.wL ta = 0 := by
      by_contra h0
      exact hnot (Or.inl ⟨hadm, h0⟩)
    have h2 : ∀ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c) = 0 := by
      intro j
      by_contra h0
      exact hnot (Or.inr (Set.mem_iUnion.mpr ⟨j, hadm, h0⟩))
    haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨d.jc c, hd.w_base c⟩⟩
    unfold ordMM
    rw [h1, show (⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c)) = 0 by
      simp only [h2, ciInf_const]]
    simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0

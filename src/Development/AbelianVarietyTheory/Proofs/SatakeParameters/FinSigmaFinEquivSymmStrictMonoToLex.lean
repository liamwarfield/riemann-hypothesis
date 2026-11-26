module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem finSigmaFinEquiv_val_eq_range {s : ℕ} (t : Fin s → ℕ) (x : (a : Fin s) × Fin (t a)) :
    ((finSigmaFinEquiv x : Fin (∑ a, t a)) : ℕ) =
      (∑ i ∈ Finset.range x.1, (fun i : ℕ => if h : i < s then t ⟨i, h⟩ else 0) i) + x.2 := by
  rw [finSigmaFinEquiv_apply]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) < s := lt_of_lt_of_le i.2 x.1.2.le
  simp only [hi, dif_pos]
  rfl

theorem finSigmaFinEquiv_lt_of_lex_lt {s : ℕ} (t : Fin s → ℕ) (x y : (a : Fin s) × Fin (t a))
    (hxy : toLex x < toLex y) :
    (finSigmaFinEquiv x : Fin (∑ a, t a)) < finSigmaFinEquiv y := by
  rw [Fin.lt_def, finSigmaFinEquiv_val_eq_range, finSigmaFinEquiv_val_eq_range]
  set t' : ℕ → ℕ := fun i => if h : i < s then t ⟨i, h⟩ else 0 with ht'
  rcases Sigma.Lex.lt_def.mp hxy with h | ⟨h, h2⟩
  · have h' : (x.1 : ℕ) < y.1 := h
    have hsub : Finset.range (x.1 + 1) ⊆ Finset.range y.1 :=
      Finset.range_subset_range.mpr h'
    have hle : (Finset.range (x.1 + 1)).sum t' ≤ (Finset.range y.1).sum t' :=
      Finset.sum_le_sum_of_subset hsub
    replace hle := (Finset.sum_range_succ t' x.1).symm.trans_le hle
    have hx : t' x.1 = t x.1 := by simp [ht', x.1.2]
    have h3 : (x.2 : ℕ) < t x.1 := x.2.2
    have h4 : (∑ i ∈ Finset.range x.1, t' i) = (Finset.range x.1).sum t' := rfl
    omega
  · obtain ⟨a, i⟩ := x
    obtain ⟨b, j⟩ := y
    change a = b at h
    subst h
    change i < j at h2
    have : (i : ℕ) < j := h2
    simp only
    omega

theorem finSigmaFinEquiv_symm_strictMono_lex :
    ∀ (s : ℕ) (t : Fin s → ℕ), StrictMono fun c : Fin (∑ a, t a) =>
      (toLex (finSigmaFinEquiv.symm c) : Σₗ a, Fin (t a)) := by
  intro s t c d hcd
  by_contra hn
  rw [not_lt] at hn
  rcases hn.lt_or_eq with h | h
  · have := finSigmaFinEquiv_lt_of_lex_lt t _ _ h
    simp only [Equiv.apply_symm_apply] at this
    exact absurd hcd (not_lt.mpr this.le)
  · have h' : finSigmaFinEquiv.symm d = finSigmaFinEquiv.symm c := toLex.injective h
    have := finSigmaFinEquiv.symm.injective h'
    exact absurd hcd (by rw [this]; exact lt_irrefl _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLexStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex : ∀ (s : ℕ) (t : Fin s → ℕ), StrictMono fun c : Fin (∑ a, t a) => (toLex (finSigmaFinEquiv.symm c) : Σₗ a, Fin (t a)) := by
  first | exact @GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | exact GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | (intros; apply GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNorm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrWeilAbs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_pow_central {n : ℕ} (a : WDRep h (Fin n → ℂ)) {φ : Weil h} (hφ : deg φ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ : Weil h, a.ρ (φ ^ m) * a.ρ σ = a.ρ σ * a.ρ (φ ^ m) := by
  classical
  let S : Set (Module.End ℂ (Fin n → ℂ)) := Set.range fun τ : Ine (F := E) A => a.ρ (ineIncl h τ)
  haveI : Finite S := a.smooth.finite_range.to_subtype
  have conj_mem : ∀ (k : ℕ), ∀ s ∈ S, a.ρ (φ ^ k) * s * a.ρ ((φ ^ k)⁻¹) ∈ S := by
    rintro k _ ⟨τ, rfl⟩
    have h0 : deg (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) = 0 := by simp
    refine ⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only [← map_mul]
    exact congrArg a.ρ (Subtype.ext rfl)
  let g : ℕ → (S → S) := fun k s => ⟨_, conj_mem k s.1 s.2⟩
  obtain ⟨k1, k2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  obtain ⟨k, m, hm, hkm⟩ : ∃ k m : ℕ, 0 < m ∧ g k = g (k + m) := by
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact ⟨k1, k2 - k1, by omega, by rw [show k1 + (k2 - k1) = k2 by omega]; exact heq⟩
    · exact ⟨k2, k1 - k2, by omega, by rw [show k2 + (k1 - k2) = k1 by omega]; exact heq.symm⟩
  have comm_ine : ∀ τ : Ine (F := E) A,
      a.ρ (φ ^ m) * a.ρ (ineIncl h τ) = a.ρ (ineIncl h τ) * a.ρ (φ ^ m) := by
    intro τ
    have e1 : a.ρ (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) =
        a.ρ (φ ^ (k + m) * ineIncl h τ * (φ ^ (k + m))⁻¹) := by
      have := congrArg Subtype.val (congrFun hkm ⟨_, τ, rfl⟩)
      rw [map_mul, map_mul, map_mul, map_mul]
      exact this
    have e2 := congrArg (fun X => a.ρ ((φ ^ k)⁻¹) * X * a.ρ (φ ^ k * φ ^ m)) e1
    simp only [← map_mul] at e2
    rw [← map_mul, ← map_mul]
    convert e2.symm using 2 <;> group
  refine ⟨m, hm, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hφ σ
  have hc : φ ^ m * φ ^ deg σ = φ ^ deg σ * φ ^ m :=
    ((Commute.refl φ).pow_left m).zpow_right (deg σ)
  rw [hτ, map_mul, ← mul_assoc, ← map_mul, hc, map_mul, mul_assoc, comm_ine, ← mul_assoc]

theorem exists_smul_of_commute {n : ℕ} (a : WDRep h (Fin n → ℂ)) (hirr : a.ρ.IsIrreducible)
    (P : Module.End ℂ (Fin n → ℂ)) (hP : ∀ σ : Weil h, P * a.ρ σ = a.ρ σ * P) :
    ∃ c : ℂ, ∀ v, P v = c • v := by
  haveI := hirr
  let f : Representation.IntertwiningMap a.ρ a.ρ :=
    ⟨P, fun σ => LinearMap.ext fun v => LinearMap.congr_fun (hP σ) v⟩
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := a.ρ)).2 f
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun F : Representation.IntertwiningMap a.ρ a.ρ => F v) hc
  rw [Algebra.algebraMap_eq_smul_one] at this
  simpa [f] using this.symm

theorem irrWD_eig_norm_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := by
  intro E Ω _ _ _ _ _ A w h x hx φ hφ α hα β hβ
  obtain ⟨n, a, rfl, hirr⟩ := hx
  rw [WD.eig_mk] at hα hβ
  obtain ⟨m, hm, hcomm⟩ := exists_pow_central a hφ
  obtain ⟨c, hc⟩ := exists_smul_of_commute a hirr _ hcomm
  have hev : ∀ γ ∈ (a.ρ φ).charpoly.roots, γ ^ m = c := by
    intro γ hγ
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      (Polynomial.isRoot_of_mem_roots hγ)).exists_hasEigenvector
    have hpow : ∀ k : ℕ, ((a.ρ φ) ^ k) v = γ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv.apply_eq_smul, smul_smul, pow_succ]
    have h1 : γ ^ m • v = c • v := by rw [← hpow, ← map_pow, hc]
    exact smul_left_injective ℂ hv.2 h1
  have h2 : ‖α‖ ^ m = ‖β‖ ^ m := by rw [← norm_pow, ← norm_pow, hev α hα, hev β hβ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hm.ne').mp h2

end GlobalTheory.IrrWeilAbs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNormStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_wd_eigen_equal_norm : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := by
  first | exact @GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq | exact GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq | (intros; apply GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSum
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Module

namespace GlobalTheory.WeilDeligne

section ProdLin

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem inl_absSpace_le (f : End ℂ V) (g : End ℂ V') (r : ℝ) :
    (absSpace f r).map (LinearMap.inl ℂ V V') ≤ absSpace (f.prodMap g : End ℂ (V × V')) r :=
  map_absSpace_le (f := f) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inl ℂ V V')
    (fun x => Prod.ext rfl (map_zero g).symm) r

theorem inr_absSpace_le (f : End ℂ V) (g : End ℂ V') (r : ℝ) :
    (absSpace g r).map (LinearMap.inr ℂ V V') ≤ absSpace (f.prodMap g : End ℂ (V × V')) r :=
  map_absSpace_le (f := g) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inr ℂ V V')
    (fun x => Prod.ext (map_zero f).symm rfl) r

theorem mem_absSpace_prodMap (f : End ℂ V) (g : End ℂ V') (r : ℝ) (v : V × V') :
    v ∈ absSpace (f.prodMap g : End ℂ (V × V')) r ↔ v.1 ∈ absSpace f r ∧ v.2 ∈ absSpace g r := by
  constructor
  · intro hv
    exact ⟨map_absSpace_le (LinearMap.fst ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩,
      map_absSpace_le (LinearMap.snd ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    have e : v = LinearMap.inl ℂ V V' v.1 + LinearMap.inr ℂ V V' v.2 := by simp
    rw [e]
    exact add_mem (inl_absSpace_le f g r ⟨_, h1, rfl⟩) (inr_absSpace_le f g r ⟨_, h2, rfl⟩)

theorem IsPurePair.prodMap {q : ℝ} {f N : End ℂ V} {g M : End ℂ V'} (hf : IsPurePair q f N)
    (hg : IsPurePair q g M) :
    IsPurePair q (f.prodMap g : End ℂ (V × V')) (N.prodMap M) := by
  have hpow : ∀ i : ℕ, (N.prodMap M : End ℂ (V × V')) ^ i = (N ^ i).prodMap (M ^ i) :=
    fun i => (map_pow (LinearMap.prodMapRingHom ℂ V V') (N, M) i).symm
  refine ⟨eq_top_iff.mpr fun v _ => ?_, fun i => ?_⟩
  · have h1 : v.1 ∈ ⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2)) := hf.1 ▸ Submodule.mem_top
    have h2 : v.2 ∈ ⨆ i : ℤ, absSpace g (q ^ ((i : ℝ) / 2)) := hg.1 ▸ Submodule.mem_top
    have hl : (⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2))).map (LinearMap.inl ℂ V V') ≤
        ⨆ i : ℤ, absSpace (f.prodMap g : End ℂ (V × V')) (q ^ ((i : ℝ) / 2)) := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun i => inl_absSpace_le f g _
    have hr : (⨆ i : ℤ, absSpace g (q ^ ((i : ℝ) / 2))).map (LinearMap.inr ℂ V V') ≤
        ⨆ i : ℤ, absSpace (f.prodMap g : End ℂ (V × V')) (q ^ ((i : ℝ) / 2)) := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun i => inr_absSpace_le f g _
    have e : v = LinearMap.inl ℂ V V' v.1 + LinearMap.inr ℂ V V' v.2 := by simp
    rw [e]
    exact add_mem (hl ⟨_, h1, rfl⟩) (hr ⟨_, h2, rfl⟩)
  · rw [hpow]
    refine ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩
    · rw [SetLike.mem_coe, mem_absSpace_prodMap] at hv ⊢
      exact ⟨(hf.2 i).1 hv.1, (hg.2 i).1 hv.2⟩
    · rw [SetLike.mem_coe, mem_absSpace_prodMap] at hv hv'
      have := Prod.ext_iff.mp hvv
      exact Prod.ext ((hf.2 i).2.1 hv.1 hv'.1 this.1) ((hg.2 i).2.1 hv.2 hv'.2 this.2)
    · rw [SetLike.mem_coe, mem_absSpace_prodMap] at hv
      obtain ⟨u, hu, e1⟩ := (hf.2 i).2.2 hv.1
      obtain ⟨u', hu', e2⟩ := (hg.2 i).2.2 hv.2
      exact ⟨(u, u'), (mem_absSpace_prodMap _ _ _ _).mpr ⟨hu, hu'⟩, Prod.ext e1 e2⟩

end ProdLin

theorem WDRep.Tempered.sum {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {a : WDRep h V} {b : WDRep h V'}
    (ha : a.Tempered) (hb : b.Tempered) : (a.sum b).Tempered :=
  fun φ hφ => (ha φ hφ).prodMap (hb φ hφ)

theorem WD.tempered_lpSum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (x.lpSum y).tempered := by
  intro E Ω _ _ _ _ _ A w h x y hx hy
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.tempered_mk] at hx hy
      rw [WD.lpSum_mk, WD.tempered_mk]
      exact hx.sum hy

end GlobalTheory.WeilDeligne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSumStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_direct_sum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (x.lpSum y).tempered := by
  first | exact @GlobalTheory.WeilDeligne.WD.tempered_lpSum | exact GlobalTheory.WeilDeligne.WD.tempered_lpSum | (intros; apply GlobalTheory.WeilDeligne.WD.tempered_lpSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProduct
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.DetSp

open Polynomial TensorProduct Module

theorem prod_roots_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) : f.charpoly.roots.prod = LinearMap.det f := by
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), ← Matrix.det_eq_prod_roots_charpoly,
    LinearMap.det_toMatrix]

theorem det_map {n m : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (g : Module.End ℂ (Fin m → ℂ)) :
    LinearMap.det (TensorProduct.map f g) = LinearMap.det f ^ m * LinearMap.det g ^ n := by
  classical
  set b := Pi.basisFun ℂ (Fin n)
  set c := Pi.basisFun ℂ (Fin m)
  rw [← LinearMap.det_toMatrix (b.tensorProduct c), TensorProduct.toMatrix_map, Matrix.det_kronecker,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix, Fintype.card_fin, Fintype.card_fin]

theorem det_diagEnd {m : ℕ} (c : Fin m → ℂ) : LinearMap.det (diagEnd c) = ∏ i, c i := by
  classical
  have e : diagEnd c = Matrix.toLin' (Matrix.diagonal c) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [Matrix.mulVec_diagonal]
  rw [e, LinearMap.det_toLin', Matrix.det_diagonal]

theorem sum_centred (m : ℕ) : ∑ i : Fin m, (((i : ℕ) : ℝ) - ((m : ℝ) - 1) / 2) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) - ((m : ℝ) - 1) / 2)), Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ∀ k : ℕ, ∑ i ∈ Finset.range k, (i : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [this]; ring

variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem prod_qPow {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, qPow w (f i) = qPow w (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, qPow_add]

theorem prod_spEig (m : ℕ) : ∏ i, WDRep.spEig w m i = 1 := by
  simp only [WDRep.spEig]
  rw [prod_qPow, sum_centred, qPow_zero]

end GlobalTheory.WeilDeligne.DetSp

namespace GlobalTheory.WeilDeligne

theorem prod_eig_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp (h := h) l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  intro E Ω _ _ _ _ _ A w h x l σ
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
      DetSp.prod_roots_charpoly, DetSp.prod_roots_charpoly, DetSp.det_map, DetSp.det_diagEnd,
      Finset.prod_zpow, ← Units.coe_prod, DetSp.prod_spEig, Units.val_one, one_zpow, one_pow, mul_one]

end GlobalTheory.WeilDeligne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProductStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_character_eigen_product : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp (h := h) l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  exact @_root_.GlobalTheory.WeilDeligne.prod_eig_lpChar_lpSp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequality
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequality
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory.Cong

theorem eigen_small_sub_finite_approx : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (V X J I : Type) [AddCommGroup V] [Module ℂ V] [Fintype I] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ), (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) → ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → ∀ (v : I → V) (η : I → J → ℂ), (∀ i j, T j (v i) = η i j • v i) → ∀ ε : ℝ, (∀ x, ‖ι.symm (ev x (v₀ + ∑ i, v i))‖ ≤ ε) → ∃ (s : Finset (J → Qbar l)) (c : (J → Qbar l) → Qbar l), (∀ z ∈ s, ∃ i, z = fun j => ι.symm (η i j)) ∧ ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (θ j)) P - ∑ z ∈ s, c z * MvPolynomial.aeval z P‖ ≤ ε := by
  intro l _ ι V X J I _ _ _ T ev hT v₀ θ x₀ hθ hx₀ v η hη ε hε
  classical
  have hmap : ∀ (w : J → ℂ) (P : MvPolynomial J ℤ),
      ι.symm (MvPolynomial.aeval w P) = MvPolynomial.aeval (fun j => ι.symm (w j)) P := by
    intro w P
    induction P using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  let u : MvPolynomial J ℤ → V := fun P =>
    MvPolynomial.aeval θ P • v₀ + ∑ i, MvPolynomial.aeval (η i) P • v i
  have good : ∀ P, ∀ x, ‖ι.symm (ev x (u P))‖ ≤ ε := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C n =>
      intro x
      have e : u (MvPolynomial.C n) = (n : ℂ) • (v₀ + ∑ i, v i) := by
        simp [u, smul_add, Finset.smul_sum]
      rw [e, map_smul, smul_eq_mul, map_mul, norm_mul, map_intCast]
      have h1 : ‖((n : ℤ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) n
      have h2 := hε x
      have h3 := norm_nonneg (ι.symm (ev x (v₀ + ∑ i, v i)))
      nlinarith
    | add p q hp hq =>
      intro x
      have e : u (p + q) = u p + u q := by
        simp only [u, map_add (f := _), add_smul, Finset.sum_add_distrib]; abel
      rw [e, map_add (f := _), map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hp x) (hq x))
    | mul_X p j hp =>
      intro x
      have e : u (p * MvPolynomial.X j) = T j (u p) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [u, map_add (f := _), map_sum, map_smul, hθ, hη, map_mul, MvPolynomial.aeval_X, smul_smul]
      rw [e]
      exact hT (u p) ε hp j x
  have hb0 : ι.symm (ev x₀ v₀) ≠ 0 := by
    intro h; rw [h, norm_zero] at hx₀; exact zero_ne_one hx₀
  refine ⟨Finset.univ.image (fun i => fun j => ι.symm (η i j)),
    fun z => - ∑ i ∈ Finset.univ.filter (fun i => (fun j => ι.symm (η i j)) = z),
      ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀), ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨i, rfl⟩ := hz
    exact ⟨i, rfl⟩
  · intro P
    have key : ∑ z ∈ Finset.univ.image (fun i => fun j => ι.symm (η i j)),
        (- ∑ i ∈ Finset.univ.filter (fun i => (fun j => ι.symm (η i j)) = z),
          ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀)) * MvPolynomial.aeval z P
        = - ∑ i, ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀) *
            MvPolynomial.aeval (fun j => ι.symm (η i j)) P := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => fun j => ι.symm (η i j))
        (t := Finset.univ.image (fun i => fun j => ι.symm (η i j)))
        (fun i hi => Finset.mem_image_of_mem _ hi), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hi]
    have hexp : ι.symm (ev x₀ (u P)) =
        (MvPolynomial.aeval (fun j => ι.symm (θ j)) P + ∑ i, ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀) *
            MvPolynomial.aeval (fun j => ι.symm (η i j)) P) * ι.symm (ev x₀ v₀) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [u, map_add (f := _), map_sum, map_smul, smul_eq_mul, map_mul, hmap, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [key, sub_neg_eq_add]
    have h := good P x₀
    rw [hexp, norm_mul, hx₀, mul_one] at h
    exact h

end GlobalTheory.Cong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequalityStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (V X J I : Type) [AddCommGroup V] [Module ℂ V] [Fintype I] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ), (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) → ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → ∀ (v : I → V) (η : I → J → ℂ), (∀ i j, T j (v i) = η i j • v i) → ∀ ε : ℝ, (∀ x, ‖ι.symm (ev x (v₀ + ∑ i, v i))‖ ≤ ε) → ∃ (s : Finset (J → Qbar l)) (c : (J → Qbar l) → Qbar l), (∀ z ∈ s, ∃ i, z = fun j => ι.symm (η i j)) ∧ ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (θ j)) P - ∑ z ∈ s, c z * MvPolynomial.aeval z P‖ ≤ ε := by
  first | (exact @GlobalTheory.Cong.eigen_small_sub_finite_approx) | (exact GlobalTheory.Cong.eigen_small_sub_finite_approx) | (intros; apply GlobalTheory.Cong.eigen_small_sub_finite_approx  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquiv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.BlockRename

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n]
  {f : γ' → γ} {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]


omit [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n]
  [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] in
theorem blk_rename {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (j : n) : blk e j = f (blk e₂ j) := by
  obtain ⟨⟨c', x⟩, rfl⟩ := e₂.surjective j
  calc
    blk e (e₂ ⟨c', x⟩) = f c' := by rw [he]; simp [blk]
    _ = f (blk e₂ (e₂ ⟨c', x⟩)) := by simp [blk]


omit [Fintype γ] [Fintype γ'] [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] in
theorem mem_parab_rename (hf : StrictMono f) {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (g : GL n k) : g ∈ parab k e ↔ g ∈ parab k e₂ := by
  simp only [mem_parab, blk_rename he, hf.lt_iff_lt]


omit [∀ c, DecidableEq (m c)] in
theorem modExp_rename (hf : StrictMono f) (hs : Function.Surjective f) (c' : γ') :
    modExp (fun c' => m (f c')) c' = modExp m (f c') := by
  unfold modExp
  let E := Equiv.ofBijective f ⟨hf.injective, hs⟩
  congr 1
  · rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv E _ _ fun b => if_congr hf.lt_iff_lt.symm rfl rfl
  · rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv E _ _ fun b => if_congr hf.lt_iff_lt.symm rfl rfl

theorem deltaHalf_rename (hf : StrictMono f) (hs : Function.Surjective f) (g : Levi k m) :
    deltaHalf k (fun c' => m (f c')) (fun c' => g (f c')) = deltaHalf k m g := by
  rw [deltaHalf_apply, deltaHalf_apply]
  let E := Equiv.ofBijective f ⟨hf.injective, hs⟩
  exact Fintype.prod_equiv E _ _ fun c' => by rw [modExp_rename hf hs]; rfl

theorem leviProj_rename {e : (Σ c, m c) ≃ n} {e₂ : (Σ c', m (f c')) ≃ n}
    (he : ∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) (p : parab k e₂) (q : parab k e) (hpq : (p : GL n k) = q) :
    leviProj k e₂ p = fun c' => leviProj k e q (f c') := by
  funext c'
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, leviProj_apply, he, he, hpq]

def kappa (hf : StrictMono f) (hs : Function.Surjective f) (X : γ → Type) [∀ c, AddCommGroup (X c)]
    [∀ c, Module ℂ (X c)] : (⨂[ℂ] c, X c) ≃ₗ[ℂ] ⨂[ℂ] c', X (f c') :=
  PiTensorProduct.reindex ℂ X (Equiv.ofBijective f ⟨hf.injective, hs⟩).symm

theorem kappa_tprod (hf : StrictMono f) (hs : Function.Surjective f) {X : γ → Type} [∀ c, AddCommGroup (X c)]
    [∀ c, Module ℂ (X c)] (x : ∀ c, X c) :
    kappa hf hs X (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ fun c' => x (f c') := by
  exact PiTensorProduct.reindex_tprod (R := ℂ) (s := X) _ x

theorem piTensor_rename (hf : StrictMono f) (hs : Function.Surjective f) {X : γ → Type}
    [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c))
    (g : Levi k m) (w : ⨂[ℂ] c, X c) :
    piTensor (fun c' => σ (f c')) (fun c' => g (f c')) (kappa hf hs X w) = kappa hf hs X (piTensor σ g w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x => simp only [map_smul, kappa_tprod, piTensor_tprod]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.SmGL.BlockRename

namespace GlobalTheory.SmGL.BlockRename

theorem multiProd_rename : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n] (f : γ' → γ), StrictMono f → Function.Surjective f → ∀ {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (e : (Σ c, m c) ≃ n) (e₂ : (Σ c', m (f c')) ≃ n), (∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) → ∀ {X : γ → Type} [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c)), Nonempty ((multiProd e σ).Equiv (multiProd e₂ fun c' => σ (f c'))) := by
  intro k _ _ _ _ γ γ' n _ _ _ _ _ _ f hf hs m _ _ e e₂ he X _ _ σ
  let κ := kappa hf hs X
  have key : ∀ (p : parab k e₂) (q : parab k e), (p : GL n k) = q → ∀ w,
      ((twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂)) p (κ w) =
        κ (((twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e)) q w) := by
    intro p q hpq w
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, leviProj_rename he p q hpq, twist_apply, twist_apply,
      deltaHalf_rename hf hs, piTensor_rename hf hs]
    exact (map_smul κ _ _).symm
  have hP := mem_parab_rename (k := k) hf he
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear
    (GlobalTheory.SmGL.MultiIrr.indPull
      (σ := (twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂))
      (τ := (twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e))
      (MonoidHom.id _) continuous_id κ.toLinearMap fun p => ⟨⟨p, (hP p).2 p.2⟩, rfl, fun w => key p _ rfl w⟩)
    (GlobalTheory.SmGL.MultiIrr.indPull
      (σ := (twist (piTensor σ) (deltaHalf k m)).comp (leviProj k e))
      (τ := (twist (piTensor fun c' => σ (f c')) (deltaHalf k fun c' => m (f c'))).comp (leviProj k e₂))
      (MonoidHom.id _) continuous_id κ.symm.toLinearMap fun q => ⟨⟨q, (hP q).1 q.2⟩, rfl, fun w =>
        κ.injective (by
          simp only [LinearEquiv.coe_coe]
          rw [LinearEquiv.apply_symm_apply, ← key ⟨q, (hP q).1 q.2⟩ q rfl, LinearEquiv.apply_symm_apply])⟩) ?_ ?_) fun g => ?_⟩
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => κ.apply_symm_apply (F.1.1 x)))
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => κ.symm_apply_apply (F.1.1 x)))
  · exact LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => rfl))

end GlobalTheory.SmGL.BlockRename
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquivStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n] (f : γ' → γ), StrictMono f → Function.Surjective f → ∀ {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (e : (Σ c, m c) ≃ n) (e₂ : (Σ c', m (f c')) ≃ n), (∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) → ∀ {X : γ → Type} [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c)), Nonempty ((multiProd e σ).Equiv (multiProd e₂ fun c' => σ (f c'))) := by
  first | exact @GlobalTheory.SmGL.BlockRename.multiProd_rename | exact GlobalTheory.SmGL.BlockRename.multiProd_rename | (intros; apply GlobalTheory.SmGL.BlockRename.multiProd_rename <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedSpecialOfUnitEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedSpecialOfUnitEigen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

section VecShift

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def vecShift (n : ℕ) : End ℂ (Fin n → V) where
  toFun v i := if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0
  map_add' v v' := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]
  map_smul' a v := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]

theorem vecShift_apply {n : ℕ} (v : Fin n → V) (i : Fin n) :
    vecShift n v i = if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0 := rfl

theorem vecShift_pow_apply {n : ℕ} (k : ℕ) (v : Fin n → V) (i : Fin n) :
    (vecShift n ^ k) v i = if k ≤ (i : ℕ) then v ⟨i - k, by omega⟩ else 0 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', End.mul_apply, vecShift_apply]
    by_cases h1 : 1 ≤ (i : ℕ)
    · rw [if_pos h1, ih]
      by_cases h2 : k + 1 ≤ (i : ℕ)
      · rw [if_pos h2, if_pos (by simp only; omega)]
        congr 2
        simp only; omega
      · rw [if_neg h2, if_neg (by simp only; omega)]
    · rw [if_neg h1, if_neg (by omega)]

def scaledDiag {n : ℕ} (f : End ℂ V) (c : Fin n → ℂ) : End ℂ (Fin n → V) where
  toFun v i := c i • f (v i)
  map_add' v v' := by ext i; simp [smul_add]
  map_smul' a v := by ext i; simp [smul_comm (c i) a]

theorem scaledDiag_apply {n : ℕ} (f : End ℂ V) (c : Fin n → ℂ) (v : Fin n → V) (i : Fin n) :
    scaledDiag f c v i = c i • f (v i) := rfl

theorem mem_absSpace_scaledDiag [FiniteDimensional ℂ V] {f : End ℂ V} (hs : f.IsSemisimple)
    (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {n : ℕ} (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0) (r : ℝ)
    (v : Fin n → V) : v ∈ absSpace (scaledDiag f c) r ↔ ∀ i, ‖c i‖ ≠ r → v i = 0 := by
  classical
  constructor
  · intro hv i hi
    have hle : absSpace (scaledDiag f c) r ≤
        LinearMap.ker (LinearMap.proj i : (Fin n → V) →ₗ[ℂ] V) := by
      refine iSup₂_le fun α hα u hu => ?_
      have h1 := congrFun (End.mem_eigenspace_iff.mp hu) i
      simp only [scaledDiag_apply, Pi.smul_apply] at h1
      have h2 : u i ∈ absSpace f ‖α / c i‖ := by
        refine Submodule.mem_iSup_of_mem (α / c i) (Submodule.mem_iSup_of_mem rfl ?_)
        rw [End.mem_eigenspace_iff]
        have : f (u i) = (c i)⁻¹ • (α • u i) := by
          rw [← h1, smul_smul, inv_mul_cancel₀ (hc i), one_smul]
        rw [this, smul_smul, div_eq_inv_mul]
      have h3 : ‖α / c i‖ ≠ 1 := by
        rw [norm_div, Ne, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (hc i)), hα]
        exact fun h => hi h.symm
      rw [absSpace_eq_bot_of_norm_charpoly_roots hf h3, Submodule.mem_bot] at h2
      simp [h2]
    simpa using hle hv
  · intro hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ‖c i‖ = r
    · have hvi : v i ∈ absSpace f 1 := by
        rw [absSpace_one_eq_top_of_norm_charpoly_roots hs hf]; trivial
      have hle : (absSpace f 1).map (LinearMap.single ℂ (fun _ : Fin n => V) i) ≤
          absSpace (scaledDiag f c) r := by
        simp only [absSpace, Submodule.map_iSup]
        refine iSup₂_le fun β hβ => ?_
        rintro _ ⟨x, hx, rfl⟩
        refine Submodule.mem_iSup_of_mem (c i * β)
          (Submodule.mem_iSup_of_mem (by rw [norm_mul, hβ, mul_one, hi]) ?_)
        rw [SetLike.mem_coe, End.mem_eigenspace_iff] at hx
        rw [End.mem_eigenspace_iff]
        ext j
        by_cases hj : j = i
        · subst hj; simp [scaledDiag_apply, hx, smul_smul]
        · simp [scaledDiag_apply, hj]
      exact hle ⟨v i, hvi, by simp⟩
    · simp [hv i hi]

theorem isPurePair_scaledDiag_vecShift [FiniteDimensional ℂ V] {q : ℝ} (hq : 1 < q)
    {f : End ℂ V} (hs : f.IsSemisimple) (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {n : ℕ}
    (c : Fin n → ℂ) (hc : ∀ i : Fin n, ‖c i‖ = q ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2)) :
    IsPurePair q (scaledDiag f c) (vecShift n) := by
  classical
  have hc0 : ∀ i, c i ≠ 0 := fun i h0 => by
    have := hc i
    rw [h0, norm_zero] at this
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hq) _).ne this
  have hmem : ∀ (j : ℤ) (v : Fin n → V), v ∈ absSpace (scaledDiag f c) (q ^ ((j : ℝ) / 2)) ↔
      ∀ i : Fin n, 2 * ((i : ℕ) : ℤ) + 1 - n ≠ j → v i = 0 := by
    intro j v
    rw [mem_absSpace_scaledDiag hs hf c hc0]
    refine forall_congr' fun i => imp_congr_left (not_congr ?_)
    rw [hc, Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne', ← @Int.cast_inj ℝ]
    push_cast
    constructor <;> intro h <;> linarith
  refine ⟨eq_top_iff.mpr fun v _ => ?_, fun k => ?_⟩
  · rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem (2 * ((i : ℕ) : ℤ) + 1 - n) ((hmem _ _).mpr fun j hj => ?_)
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact hj rfl
  · have e1 : (-(k : ℝ) / 2) = ((-(k : ℤ) : ℤ) : ℝ) / 2 := by push_cast; ring
    have e2 : ((k : ℝ) / 2) = (((k : ℤ) : ℤ) : ℝ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩
    · rw [SetLike.mem_coe, hmem] at hv ⊢
      intro i hi
      rw [vecShift_pow_apply]
      split_ifs with hk
      · exact hv _ (by simp only; omega)
      · rfl
    · rw [SetLike.mem_coe, hmem] at hv hv'
      ext1 i
      by_cases hi : 2 * ((i : ℕ) : ℤ) + 1 - n = -(k : ℤ)
      · have := congrFun hvv ⟨i + k, by omega⟩
        rw [vecShift_pow_apply, vecShift_pow_apply, if_pos (by simp), if_pos (by simp)] at this
        simpa using this
      · rw [hv i hi, hv' i hi]
    · rw [SetLike.mem_coe, hmem] at hv
      refine ⟨fun i => if hi : (i : ℕ) + k < n then v ⟨i + k, hi⟩ else 0, ?_, ?_⟩
      · rw [SetLike.mem_coe, hmem]
        intro i hi
        split_ifs with hk
        · exact hv _ (by simp only; omega)
        · rfl
      · ext1 i
        rw [vecShift_pow_apply]
        split_ifs with hk h2
        · congr 2
          simp only; omega
        · exfalso; apply h2; simp only; omega
        · exact (hv i (by omega)).symm

end VecShift

end GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp (h := h) l)).tempered := by
  intro E Ω _ _ _ _ _ A w h x
  induction x using WD.ind with
  | hP n a =>
  intro hx heig l
  have hN : a.N = 0 := (WD.monodromyZero_ofWeilDeligneRepClass_iff a).mp hx
  rw [WD.lpSp, WD.lpChar_mk, WD.tempered_mk]
  intro φ hφ
  have hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1 := fun α hα =>
    heig φ hφ α (by rw [WD.eig_mk]; exact hα)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hp := isPurePair_scaledDiag_vecShift hq (a.semisimple φ) hroots
    (fun i => (WDRep.spEig w l i : ℂ)) (fun i => by rw [WDRep.spEig, norm_qPow])
  let e := TensorProduct.piScalarRight ℂ ℂ (Fin n → ℂ) (Fin l)
  have h1 : ∀ t, e ((a.tensor (WDRep.sp (h := h) l)).ρ φ t) =
      scaledDiag (a.ρ φ) (fun i => (WDRep.spEig w l i : ℂ)) (e t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      ext1 i
      simp [e, TensorProduct.piScalarRightHom_tmul, scaledDiag_apply, hφ, smul_smul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h2 : ∀ t, e ((a.tensor (WDRep.sp (h := h) l)).N t) = vecShift l (e t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      ext1 i
      by_cases hi : 1 ≤ (i : ℕ) <;>
        simp [e, TensorProduct.piScalarRightHom_tmul, vecShift_apply, shiftEnd_apply, hN, hi]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine hp.of_equiv e.symm (fun v => ?_) (fun v => ?_)
  · obtain ⟨t, rfl⟩ := e.surjective v
    rw [← h1, e.symm_apply_apply, e.symm_apply_apply]
  · obtain ⟨t, rfl⟩ := e.surjective v
    rw [← h2, e.symm_apply_apply, e.symm_apply_apply]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedSpecialOfUnitEigenStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_special_of_unit_eigen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp (h := h) l)).tempered := by
  first | exact @GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 | exact GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 | (intros; apply GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleCoinvariantsSubsingletonOfCharConj
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleCoinvariantsSubsingletonOfCharConj
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

theorem jacquet_subsingleton_of_char_nontrivial_on_conj :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible →
      ∀ (N H : Subgroup G) (χ : H →* ℂˣ) (v : V), v ≠ 0 → (∀ h : H, π h v = (χ h : ℂ) • v) →
      (∀ g : G, ∃ h : H, g * h * g⁻¹ ∈ N ∧ χ h ≠ 1) → Subsingleton (Jacquet π N) := by
  intro G V _ _ _ π hπ N H χ v hv0 hv hconj
  set K : Submodule ℂ V := twKer π N 1 with hK

  have hgv : ∀ g : G, π g v ∈ K := by
    intro g
    obtain ⟨h, hn, hχ⟩ := hconj g
    have hmem : π (g * h * g⁻¹) (π g v) - (1 : ℂ) • π g v ∈ K := by
      refine Submodule.subset_span ⟨⟨_, hn⟩, π g v, ?_⟩
      simp
    have hcalc : π (g * h * g⁻¹) (π g v) = (χ h : ℂ) • π g v := by
      rw [← Module.End.mul_apply, ← map_mul]
      have : g * (h : G) * g⁻¹ * g = g * h := by group
      rw [this, map_mul, Module.End.mul_apply, hv h, map_smul]
    rw [hcalc, ← sub_smul] at hmem
    have hne : (χ h : ℂ) - 1 ≠ 0 := by
      intro e
      apply hχ
      ext
      simpa [sub_eq_zero] using e
    have := K.smul_mem ((χ h : ℂ) - 1)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  let S : Submodule ℂ V := ⨅ g : G, K.comap (π g)
  have hS : ∀ w, w ∈ S ↔ ∀ g : G, π g w ∈ K := by
    intro w; simp [S, Submodule.mem_iInf]
  let Wr : Subrepresentation π :=
    { toSubmodule := S
      apply_mem_toSubmodule := by
        intro g w hw
        rw [hS] at hw ⊢
        intro g'
        rw [← Module.End.mul_apply, ← map_mul]
        exact hw _ }
  have hvW : v ∈ S := (hS v).2 hgv
  have htop : K = ⊤ := by
    rcases hπ.eq_bot_or_eq_top Wr with e | e
    · exfalso
      have : v ∈ Wr.toSubmodule := hvW
      rw [e] at this
      exact hv0 this
    · rw [eq_top_iff]
      intro w _
      have : w ∈ Wr.toSubmodule := by rw [e]; trivial
      have := (hS w).1 this 1
      simpa using this
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K b
  exact (Submodule.Quotient.eq K).2 (by rw [htop]; trivial)
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleCoinvariantsSubsingletonOfCharConjStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModuleCoinvariants_subsingleton_of_char_conj : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible → ∀ (N H : Subgroup G) (χ : H →* ℂˣ) (v : V), v ≠ 0 → (∀ h : H, π h v = (χ h : ℂ) • v) → (∀ g : G, ∃ h : H, g * h * g⁻¹ ∈ N ∧ χ h ≠ 1) → Subsingleton (Jacquet π N) := by
  first | exact @GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj | exact GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj | (intros; apply GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj <;> assumption)
end
end

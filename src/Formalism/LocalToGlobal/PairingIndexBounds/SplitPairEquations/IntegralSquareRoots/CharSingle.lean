module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.ConstCopies
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SemiCharImg

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.CardSmulMem
noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sum_reps_perm {M P : AddSubgroup V} {S : Finset V} (hS : IsReps M P S) (ℓ : V → V)
    (hP : ∀ x ∈ P, ℓ x ∈ P) (hinj : ∀ x ∈ P, ∀ y ∈ P, ℓ x - ℓ y ∈ M → x - y ∈ M)
    (f : V → ℂ) (hf : ∀ x ∈ P, ∀ y ∈ M, f (x + y) = f x) :
    ∑ x ∈ S, f (ℓ x) = ∑ x ∈ S, f x := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hex : ∀ x ∈ S, ∃ s ∈ S, ℓ x - s ∈ M := fun x hx => h3 _ (hP x (h1 x hx))
  choose! r hr1 hr2 using hex
  have hfr : ∀ x ∈ S, f (ℓ x) = f (r x) := by
    intro x hx
    have := hf (r x) (h1 _ (hr1 x hx)) (ℓ x - r x) (hr2 x hx)
    rwa [add_sub_cancel] at this
  have hinjr : Set.InjOn r S := by
    intro x hx y hy hxy
    refine h2 x hx y hy (hinj x (h1 x hx) y (h1 y hy) ?_)
    have : ℓ x - ℓ y = (ℓ x - r x) - (ℓ y - r y) := by rw [hxy]; abel
    rw [this]; exact M.sub_mem (hr2 x hx) (hr2 y hy)
  have himg : S.image r = S :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hr1) (by rw [Finset.card_image_of_injOn hinjr])
  calc ∑ x ∈ S, f (ℓ x) = ∑ x ∈ S, f (r x) := Finset.sum_congr rfl hfr
    _ = ∑ y ∈ S.image r, f y := (Finset.sum_image hinjr).symm
    _ = ∑ x ∈ S, f x := by rw [himg]

theorem card_smul_mem {M P : AddSubgroup V} {S : Finset V} (hS : IsReps M P S) {x : V} (hx : x ∈ P) : S.card • x ∈ M := by
  have hc : Nat.card (P ⧸ M.addSubgroupOf P) = S.card := by
    rw [← Nat.card_congr (Equiv.ofBijective _ (repClass_bijective hS))]
    simp
  have h : S.card • (QuotientAddGroup.mk (⟨x, hx⟩ : P) : P ⧸ M.addSubgroupOf P) = 0 := by
    rw [← hc]; exact card_nsmul_eq_zero'
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h
  simpa using h

theorem comm_symm (g : V →ₗ[ℂ] V) (φ : V ≃ₗ[ℂ] V) (h : ∀ x, g (φ x) = φ (g x)) (x : V) : g (φ.symm x) = φ.symm (g x) := by
  apply φ.injective
  rw [← h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

structure Multipliers (H : Sesq V) (Λ : AddSubgroup V) (δ : V ≃ₗ[ℂ] V) (ℓ ℓ' σ : V →ₗ[ℂ] V) (e : ℕ) : Prop where
  lΛ : ∀ x ∈ Λ, ℓ x ∈ Λ
  l'Λ : ∀ x ∈ Λ, ℓ' x ∈ Λ
  sΛ : ∀ x ∈ Λ, σ x ∈ Λ
  lδ : ∀ x, ℓ (δ x) = δ (ℓ x)
  l'δ : ∀ x, ℓ' (δ x) = δ (ℓ' x)
  sδ : ∀ x, σ (δ x) = δ (σ x)
  adj : ∀ x y, H (ℓ x) y = H x (ℓ' y)
  sadj : ∀ x y, H (σ x) y = H x (σ y)
  rel : ∀ x, ℓ' (ℓ x) = -x + (4 * e) • σ x

variable {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} {δ Ae : V ≃ₗ[ℂ] V}

theorem comm_cay (hA : ∀ x, Ae x = x - δ.symm x) (g : V →ₗ[ℂ] V) (h : ∀ x, g (δ x) = δ (g x)) (x : V) :
    g (Ae x) = Ae (g x) := by
  rw [hA, hA, map_sub, comm_symm g δ h]

theorem latA_stable (hA : ∀ x, Ae x = x - δ.symm x) (g : V →ₗ[ℂ] V) (hΛ : ∀ x ∈ Λ, g x ∈ Λ)
    (h : ∀ x, g (δ x) = δ (g x)) {y : V} (hy : y ∈ latA Λ δ Ae) : g y ∈ latA Λ δ Ae := by
  unfold latA at hy ⊢
  rw [mem_imgLat_iff, AddSubgroup.mem_inf, mem_imgLat_iff] at hy ⊢
  rw [← comm_symm g Ae (comm_cay hA g h), ← comm_symm g δ h]
  exact ⟨hΛ _ hy.1, hΛ _ hy.2⟩

theorem cayC_comm (hA : ∀ x, Ae x = x - δ.symm x) (g : V →ₗ[ℂ] V) (h : ∀ x, g (δ x) = δ (g x)) (x : V) :
    cayC Ae (g x) = g (cayC Ae x) := by
  unfold cayC
  rw [map_sub, map_smul, comm_symm g Ae (comm_cay hA g h)]

variable {ℓ ℓ' σ : V →ₗ[ℂ] V} {e : ℕ}

theorem phi_conj (hU : UnitaryData H Λ α δ Ae) (hM : Multipliers H Λ δ ℓ ℓ' σ e)
    (he : ∀ x ∈ Λ, e • x ∈ latA Λ δ Ae) (hα : ∀ x ∈ Λ, α (ℓ x) = α x) {x : V} (hx : x ∈ Λ) :
    phiC H α Ae (ℓ x) = conj (phiC H α Ae x) := by
  obtain ⟨hskew, hre, -, -⟩ := phiBasic V H Λ α δ Ae hU
  have h1 : H (cayC Ae (ℓ x)) (ℓ x) = -H (cayC Ae x) x + (4 * e : ℂ) * H (cayC Ae x) (σ x) := by
    rw [cayC_comm hU.cay ℓ hM.lδ, hM.adj, hM.rel, map_add (f := _), map_neg, map_nsmul, nsmul_eq_mul]
    push_cast
    rfl
  have hXre : (H (cayC Ae x) (σ x)).re = 0 := by
    have h2 : H (cayC Ae x) (σ x) = -conj (H (cayC Ae x) (σ x)) := by
      conv_lhs => rw [hskew, cayC_comm hU.cay σ hM.sδ, ← hM.sadj, hU.herm (cayC Ae x) (σ x)]
    have h3 := congrArg Complex.re h2
    simp only [Complex.neg_re, Complex.conj_re] at h3
    linarith
  have hs0 : (H x (σ x)).im = 0 := by
    have h2 : H x (σ x) = conj (H x (σ x)) := by
      conv_lhs => rw [← hM.sadj, hU.herm x (σ x)]
    have h3 := congrArg Complex.im h2
    simp only [Complex.conj_im] at h3
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (e : ℝ) * (H (cayC Ae x) (σ x)).im = (n : ℝ) := by
    have hw : Ae.symm (e • x) ∈ Λ := by
      have := he x hx
      unfold latA at this
      rw [mem_imgLat_iff, AddSubgroup.mem_inf] at this
      exact this.1
    rw [← hU.selfDual] at hw
    obtain ⟨n, hn⟩ := hw (σ x) (hM.sΛ x hx)
    refine ⟨n, ?_⟩
    rw [← hn]
    unfold altE cayC
    rw [map_nsmul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    simp only [Complex.sub_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, hs0]
    norm_num
  have hX : (4 * e : ℂ) * H (cayC Ae x) (σ x) = (4 * n : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hXre]
    · have : ((4 * e : ℂ) * H (cayC Ae x) (σ x)).im = 4 * ((e : ℝ) * (H (cayC Ae x) (σ x)).im) := by
        simp [hXre]; ring
      rw [this, hn]
      simp
  have hexp : Complex.exp (-(Real.pi : ℂ) * ((4 * n : ℂ) * Complex.I)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-2 * n)
    rw [← this]
    congr 1
    push_cast
    ring
  have hc : conj (H (cayC Ae x) x) = -H (cayC Ae x) x := by
    apply Complex.ext
    · simp [hre x]
    · simp
  have hαc : conj (α x) = α x := by
    rcases hU.semi.1 x hx with h | h <;> rw [h] <;> simp
  unfold phiC
  rw [hα x hx, h1, hX, map_mul, hαc, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, hc, mul_add,
    Complex.exp_add, hexp, mul_one]

theorem gauss_sq (hU : UnitaryData H Λ α δ Ae) (hM : Multipliers H Λ δ ℓ ℓ' σ e)
    (he : ∀ x ∈ Λ, e • x ∈ latA Λ δ Ae) (hα : ∀ x ∈ Λ, α (ℓ x) = α x) {S : Finset V}
    (hS : IsReps (latA Λ δ Ae) Λ S) : gaussC H α Ae S ^ 2 = 1 := by
  obtain ⟨-, -, -, hwd⟩ := phiBasic V H Λ α δ Ae hU
  have hinj : ∀ x ∈ Λ, ∀ y ∈ Λ, ℓ x - ℓ y ∈ latA Λ δ Ae → x - y ∈ latA Λ δ Ae := by
    intro x hx y hy h
    rw [← map_sub] at h
    have h2 := latA_stable hU.cay ℓ' hM.l'Λ hM.l'δ h
    rw [hM.rel] at h2
    have h3 : (4 * e) • σ (x - y) ∈ latA Λ δ Ae := by
      rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ (he _ (hM.sΛ _ (Λ.sub_mem hx hy))) 4
    have h4 := AddSubgroup.sub_mem _ h3 h2
    have h5 : (4 * e) • σ (x - y) - (-(x - y) + (4 * e) • σ (x - y)) = x - y := by abel
    rwa [h5] at h4
  have hsum := sum_reps_perm hS ℓ hM.lΛ hinj (phiC H α Ae) hwd
  have hreal : conj (gaussC H α Ae S) = gaussC H α Ae S := by
    unfold gaussC
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_inv₀, Complex.conj_ofReal, map_sum, ← hsum]
    congr 1
    exact Finset.sum_congr rfl fun x hx => (phi_conj hU hM he hα (hS.1 x hx)).symm
  have h8 := unitaryGauss V H Λ α δ Ae hU S hS
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hreal
  rw [hr] at h8 ⊢
  have h8' : (r ^ 2) ^ 4 = 1 := by
    have : ((r ^ 2) ^ 4 : ℝ) = r ^ 8 := by ring
    rw [this]
    exact_mod_cast h8
  have h2 := (pow_eq_one_iff_of_nonneg (sq_nonneg r) (by norm_num)).mp h8'
  exact_mod_cast h2

end Formalism.L2.PairingIndexBounds.Eq.J
end
end

noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

variable {ι : Type} [Fintype ι] {V V₁ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁]

theorem idx_coord (e : V ≃ₗ[ℂ] (ι → V₁)) (i₀ : ι) {M P : AddSubgroup V} {M₁ P₁ : AddSubgroup V₁}
    (hM : ∀ x, x ∈ M ↔ ∀ i, e x i ∈ M₁) (hP : ∀ x, x ∈ P ↔ ∀ i, e x i ∈ P₁) (h : relIdx M P ≠ 0) :
    relIdx M₁ P₁ ≠ 0 := by
  let f : V₁ →+ V := AddMonoidHom.mk' (fun x => e.symm (Pi.single i₀ x)) (fun x y => by
    rw [Pi.single_add, map_add (f := _)])
  have hcomap : ∀ (N : AddSubgroup V) (N₁ : AddSubgroup V₁), (∀ x, x ∈ N ↔ ∀ i, e x i ∈ N₁) →
      N₁ = N.comap f := by
    intro N N₁ hN
    ext x
    rw [AddSubgroup.mem_comap, hN]
    show x ∈ N₁ ↔ ∀ i, e (e.symm (Pi.single i₀ x)) i ∈ N₁
    simp only [LinearEquiv.apply_symm_apply]
    constructor
    · intro hx i
      by_cases hi : i = i₀
      · subst hi
        simpa using hx
      · rw [Pi.single_eq_of_ne hi]
        exact N₁.zero_mem
    · intro h
      simpa using h i₀
  unfold relIdx at *
  rw [hcomap M M₁ hM, hcomap P P₁ hP]
  exact AddSubgroup.relIndex_comap_ne_zero f h

variable {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem Copies.mem_img (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (x : V) :
    x ∈ imgLat (δ : V →ₗ[ℂ] V) Λ ↔ ∀ i, e x i ∈ imgLat (δ₁ : V₁ →ₗ[ℂ] V₁) Λ₁ := by
  have key : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (d : W ≃ₗ[ℂ] W) (L : AddSubgroup W) (z : W),
      z ∈ imgLat (d : W →ₗ[ℂ] W) L ↔ d.symm z ∈ L := by
    intro W _ _ d L z
    simp only [imgLat, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨d.symm z, hz, by simp⟩
  rw [key, c.lat]
  apply forall_congr'
  intro i
  rw [key]
  have hmap := c.map (δ.symm x) i
  rw [LinearEquiv.apply_symm_apply] at hmap
  rw [hmap, LinearEquiv.symm_apply_apply]

theorem Copies.form_single (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) (x : V₁) (y : V) :
    H (e.symm (Pi.single i₀ x)) y = H₁ x (e y i₀) := by
  rw [c.form, LinearEquiv.apply_symm_apply, Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Copies.single_mem (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) {x : V₁} (hx : x ∈ Λ₁) :
    e.symm (Pi.single i₀ x) ∈ Λ := by
  rw [c.lat]
  intro i
  rw [LinearEquiv.apply_symm_apply]
  by_cases hi : i = i₀
  · subst hi
    simpa using hx
  · rw [Pi.single_eq_of_ne hi]
    exact Λ₁.zero_mem

theorem Copies.char_single (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (h0 : α₁ 0 = 1) (i₀ : ι) {x : V₁} (hx : x ∈ Λ₁) :
    α (e.symm (Pi.single i₀ x)) = α₁ x := by
  rw [c.char _ (c.single_mem i₀ hx), LinearEquiv.apply_symm_apply, Finset.prod_eq_single i₀]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, h0]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Copies.unitaryData₁ (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) (hU : UnitaryData H Λ α δ Ae)
    (hH₁ : IsHerm H₁) (hP₁ : IsPosDef H₁) (hI₁ : IsIsom H₁ H₁ (δ₁ : V₁ →ₗ[ℂ] V₁)) (hA₁ : ∀ x, Ae₁ x = x - δ₁.symm x)
    (h0 : α₁ 0 = 1) (hαδ : ∀ x, α₁ (δ₁ x) = α₁ x) : UnitaryData H₁ Λ₁ α₁ δ₁ Ae₁ := by
  have hs : ∀ x : V₁, e (e.symm (Pi.single i₀ x)) i₀ = x := fun x => by simp
  have hform : ∀ x y : V₁, H (e.symm (Pi.single i₀ x)) (e.symm (Pi.single i₀ y)) = H₁ x y := by
    intro x y
    rw [c.form_single, hs]
  have hadd : ∀ x y : V₁, e.symm (Pi.single i₀ (x + y)) = e.symm (Pi.single i₀ x) + e.symm (Pi.single i₀ y) := by
    intro x y
    rw [Pi.single_add, map_add (f := _)]
  have hδs : ∀ y : V₁, δ (e.symm (Pi.single i₀ y)) = e.symm (Pi.single i₀ (δ₁ y)) := by
    intro y
    apply e.injective
    funext i
    rw [c.map, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    by_cases hi : i = i₀
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]
  have himg_single : ∀ x : V₁, x ∈ imgLat (δ₁ : V₁ →ₗ[ℂ] V₁) Λ₁ →
      e.symm (Pi.single i₀ x) ∈ imgLat (δ : V →ₗ[ℂ] V) Λ := by
    intro x hx
    rw [c.mem_img]
    intro i
    rw [LinearEquiv.apply_symm_apply]
    by_cases hi : i = i₀
    · subst hi
      simpa using hx
    · rw [Pi.single_eq_of_ne hi]
      exact (imgLat _ Λ₁).zero_mem
  have hαimg : ∀ x : V₁, x ∈ imgLat (δ₁ : V₁ →ₗ[ℂ] V₁) Λ₁ → α (e.symm (Pi.single i₀ x)) = α₁ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    show α (e.symm (Pi.single i₀ (δ₁ y))) = α₁ (δ₁ y)
    rw [← hδs, hU.inv _ (c.single_mem i₀ hy), c.char_single h0 i₀ hy, hαδ]
  refine ⟨hH₁, hP₁, ?_, ⟨?_, ?_⟩, hI₁, ⟨?_, ?_⟩, fun x _ => hαδ x, ?_, ?_, hA₁⟩
  · ext x
    constructor
    · intro hx
      have hv : e.symm (Pi.single i₀ x) ∈ Λ := by
        rw [← hU.selfDual]
        intro y hy
        obtain ⟨m, hm⟩ := hx (e y i₀) ((c.lat y).1 hy i₀)
        refine ⟨m, ?_⟩
        simp only [altE] at hm ⊢
        rw [c.form_single]
        exact hm
      have h1 := (c.lat _).1 hv i₀
      rwa [hs] at h1
    · intro hx y hy
      have h1 : e.symm (Pi.single i₀ x) ∈ dualLat H Λ := by
        rw [hU.selfDual]
        exact c.single_mem i₀ hx
      obtain ⟨m, hm⟩ := h1 _ (c.single_mem i₀ hy)
      refine ⟨m, ?_⟩
      simp only [altE] at hm ⊢
      rw [hform] at hm
      exact hm
  · intro x hx
    rw [← c.char_single h0 i₀ hx]
    exact hU.semi.1 _ (c.single_mem i₀ hx)
  · intro x hx y hy
    rw [← c.char_single h0 i₀ hx, ← c.char_single h0 i₀ hy, ← c.char_single h0 i₀ (Λ₁.add_mem hx hy), hadd,
      hU.semi.2 _ (c.single_mem i₀ hx) _ (c.single_mem i₀ hy)]
    simp only [altE, hform]
  · intro x hx
    rw [← hαimg x hx]
    exact hU.semi'.1 _ (himg_single x hx)
  · intro x hx y hy
    rw [← hαimg x hx, ← hαimg y hy, ← hαimg (x + y) ((imgLat _ Λ₁).add_mem hx hy), hadd,
      hU.semi'.2 _ (himg_single x hx) _ (himg_single y hy)]
    simp only [altE, hform]
  · exact idx_coord e i₀ c.mem_img c.lat hU.idx₁
  · exact idx_coord e i₀ c.lat c.mem_img hU.idx₂

theorem alpha_mult {H : Sesq V} {Λ : AddSubgroup V} {δ : V ≃ₗ[ℂ] V} {ℓ ℓ' σ : V →ₗ[ℂ] V} {n : ℕ}
    (hM : Multipliers H Λ δ ℓ ℓ' σ n) (c : ℝ) (α : V → ℂ) (hα : ∀ x, α x = (-1 : ℂ) ^ round (c * (H x x).re))
    (hq : ∀ x ∈ Λ, ∃ m : ℤ, c * (H x x).re = (m : ℝ)) {x : V} (hx : x ∈ Λ) : α (ℓ x) = α x := by
  obtain ⟨m1, hm1⟩ := hq x hx
  obtain ⟨m2, hm2⟩ := hq (σ x) (hM.sΛ x hx)
  obtain ⟨m3, hm3⟩ := hq (x + σ x) (Λ.add_mem hx (hM.sΛ x hx))
  have hexp : H (x + σ x) (x + σ x) = H x x + H x (σ x) + H x (σ x) + H (σ x) (σ x) := by
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [hM.sadj x x]
    ring
  have hk : c * (H x (σ x)).re * 2 = ((m3 - m1 - m2 : ℤ) : ℝ) := by
    rw [hexp] at hm3
    simp only [Complex.add_re] at hm3
    push_cast
    linarith
  have hl : H (ℓ x) (ℓ x) = -H x x + ((4 * n : ℕ) : ℂ) * H x (σ x) := by
    rw [hM.adj, hM.rel, map_add (f := _), map_neg, map_nsmul, nsmul_eq_mul]
  have hq' : c * (H (ℓ x) (ℓ x)).re = ((m1 + 2 * (-m1 + (n : ℤ) * (m3 - m1 - m2)) : ℤ) : ℝ) := by
    rw [hl]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    push_cast
    push_cast at hk
    nlinarith [hm1, hk]
  rw [hα, hα, hq', hm1, round_intCast, round_intCast, zpow_add₀ (by norm_num), zpow_mul]
  simp

end Formalism.L2.PairingIndexBounds.Eq.J

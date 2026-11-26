module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem adj_map_ringHom {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (M : M4 R) :
    adj (M.map f) = (adj M).map f := by
  ext i j
  simp [adj, Matrix.map_apply]

private theorem sxPdMap_lemma_2 {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (c : R) (M : M4 R)
    (h : IsGSp c M) : IsGSp (f c) (M.map f) := by
  simp only [IsGSp] at h ⊢
  rw [adj_map_ringHom, ← Matrix.map_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem UpperTheory.V.Ws.sxPdMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R R' : Type} [CommRing R] [CommRing R'] (a : O →+* R) (f : R →+* R') (P : PD Φ.ι Γ R), (∀ v i s, (P.map f).ψ v i s = f (P.ψ v i s)) ∧ (Φ.IsPair a P → Φ.IsPair (f.comp a) (P.map f)) ∧ (Φ.Res a P → Φ.Res (f.comp a) (P.map f)) := by
  intro O Γ _ _ Φ R R' _ _ a f P
  have hr : ∀ s, mapRep f P.r s = (P.r s).map f := fun s => by
    ext i j
    rw [mapRep_apply, Matrix.map_apply]
  have hψ : ∀ v i s, (P.map f).ψ v i s = f (P.ψ v i s) := fun v i s => by
    simp only [PD.map, PD.ψ]
    rw [hr, adj_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
  refine ⟨hψ, fun h => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨fun g => ?_, fun g hg => ?_, ?_, fun v => ?_, fun v s hs => ?_, fun v s hs i => ?_⟩
    · simp only [PD.map, hr]
      exact sxPdMap_lemma_2 f _ _ (h1 g)
    · simp only [PD.map, hr, h2 g hg, Matrix.map_one, map_zero, map_one]
    · simp only [PD.map, hr]
      exact h3.map (map_zero f)
    · have := h4 v
      simp only [IsLow] at this ⊢
      simp only [PD.map]
      have hg := sxPdMap_lemma_2 f _ _ this.1
      rw [map_one] at hg
      refine ⟨hg, fun i => ?_, fun i j hij => ?_⟩
      · rw [Matrix.map_apply, this.2.1 i, map_one]
      · rw [Matrix.map_apply, this.2.2 i j hij, map_zero]
    · have := h5 v s hs
      simp only [IsUp] at this ⊢
      simp only [PD.map, hr]
      intro i j hij
      rw [adj_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, this i j hij, map_zero]
    · rw [hψ, h6 v s hs i, map_one]
  · obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun g i => ?_, fun v s hs i => ?_, ?_⟩
    · show mapRep f P.r g i i = _
      rw [mapRep_apply, h1 g i]
      rfl
    · rw [hψ, h2 v s hs i]
      rfl
    · simp only [Supp, SuppM, PD.map] at h3 ⊢
      rcases h3 with ⟨hA, hB⟩ | hC
      · exact Or.inl ⟨fun g i j h h' => by rw [mapRep_apply, hA g i j h h', map_zero],
          fun v i j h h' => by rw [Matrix.map_apply, hB v i j h h', map_zero]⟩
      · exact Or.inr fun g i j h h' => by rw [mapRep_apply, hC g i j h h', map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicMat
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_mat {Γ S ι : Type} [TopologicalSpace Γ] [Fintype ι] (f : Γ → Matrix ι ι S)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    intro i j
    exact (h i j).eventually_eq x
  exact this.mono fun y hy => Matrix.ext hy

theorem UpperTheory.V.Ws.sxAdicMat :
    ∀ {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (M : Γ → M4 R), (∀ i j, AdicCont I fun g => M g i j) → (∀ n, AdicCont I fun g => (M g).charpoly.coeff n) ∧ ∀ (U V : M4 R) i j, AdicCont I fun g => (U * M g * V) i j := by
  intro Γ R _ _ I M h
  have hl : ∀ N : ℕ, IsLocallyConstant fun g => (M g).map (Ideal.Quotient.mk (I ^ N)) :=
    fun N => lc_mat _ fun i j => h i j N
  refine ⟨fun n N => ?_, fun U V i j N => ?_⟩
  · have := (hl N).comp fun A => A.charpoly.coeff n
    convert this using 2 with g
    simp only [Function.comp, Matrix.charpoly_map, Polynomial.coeff_map]
  · have := (hl N).comp fun A =>
      (U.map (Ideal.Quotient.mk (I ^ N)) * A * V.map (Ideal.Quotient.mk (I ^ N))) i j
    convert this using 2 with g
    simp only [Function.comp, ← Matrix.map_mul, Matrix.map_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearMap
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {τ : ℤ × ℤ →+ ℤ} {D : RD Φ R} (f : R →ₐ[Λ] R'), Φ.Near a τ D → Φ.Near a τ (D.map (f : R →+* R')) := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ R' _ _ _ τ D f hD
  have hr : ∀ g i j, (D.map (f : R →+* R')).r g i j = f (D.r g i j) := by
    intro g i j
    simp [RD.map, mapRep]
  have hψ : ∀ v i s, (D.map (f : R →+* R')).ψ v i s = f (D.ψ v i s) := by
    intro v i s
    simp [RD.map]
  have hm : maximalIdeal R ≤ Ideal.comap (f : R →+* R') (maximalIdeal R') := by
    intro x hx
    rw [Ideal.mem_comap]
    show f x ∈ maximalIdeal R'
    rw [← res_eq_zero_iff Λ R', res_map, res_eq_zero_iff]
    exact hx
  have hadj : ∀ X : M4 R, adj ((f : R →+* R').mapMatrix X) = (f : R →+* R').mapMatrix (adj X) := by
    intro X
    ext i j
    simp [adj_apply, map_zsmul]
  have hrm : ∀ g, (D.map (f : R →+* R')).r g = (f : R →+* R').mapMatrix (D.r g) := by
    intro g
    ext i j
    rw [hr]
    simp
  refine ⟨⟨fun g => ?_, fun g hg => ?_, ?_⟩, fun i j => ?_, fun v i => ?_, fun g i => ?_,
    fun g i j hij hτ => ?_, fun v i s => ?_⟩
  · have hX : adj (D.r g) * D.r g = (algebraMap Λ R) (a ↑(Φ.ν g)) • 1 := hD.rep.mult g
    have h := congrArg (f : R →+* R').mapMatrix hX
    rw [map_mul, ← hadj, ← hrm] at h
    show adj ((D.map (f : R →+* R')).r g) * (D.map (f : R →+* R')).r g =
      ((algebraMap Λ R').comp a) ↑(Φ.ν g) • 1
    rw [h]
    ext i j
    simp [Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
  · rw [hrm, hD.rep.kill g hg, map_one]
  · intro i j hij
    rw [hrm]
    simp [hD.rep.nrm hij]
  · simpa [hr] using adicCont_map (f : R →+* R') hm (hD.cont i j)
  · simpa [hψ] using adicCont_map (f : R →+* R') hm (hD.contψ v i)
  · rw [hr, res_map]
    exact hD.diag g i
  · rw [hr]
    exact hm (hD.off g i j hij hτ)
  · rw [hψ, res_map]
    exact hD.redψ v i s
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxExtGr0
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxExtGr0 :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO Λ (W.gr 0)] (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.gr 0 →ₐ[Λ] R'), (∀ (b : W.gr 0) (n : W.σ →₀ ℕ), Finsupp.weight W.wt n = 0 → ((b : W.A) : R) = (n.prod fun s k => W.z s ^ k) → f b = f' b) → f = f' := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz _ R' _ _ _ f f' h
  obtain ⟨-, u, hu, hm⟩ := UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials Λ X R W hz
  have hloc : ∀ g : W.gr 0 →ₐ[Λ] R', ∀ x ∈ maximalIdeal (W.gr 0), g x ∈ maximalIdeal R' := fun g x hx => by
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hx
  refine UpperTheory.V.Alg.co_ext Λ (W.gr 0) Λ R' (maximalIdeal R') (Algebra.ofId Λ (W.gr 0)) (u : Set (W.gr 0)) ?_ ?_ f f'
    ⟨1, fun x hx => ?_⟩ (Subsingleton.elim _ _) fun s hs => ?_
  · intro b hb
    show b ∈ maximalIdeal (W.gr 0)
    rw [hm]
    exact Ideal.mem_sup_right (Ideal.subset_span hb)
  · refine le_trans (hm.trans (sup_comm _ _)).le ?_
    exact le_sup_left
  · rw [pow_one] at hx
    exact ⟨hloc f x hx, hloc f' x hx⟩
  · obtain ⟨n, -, hn, hb⟩ := hu s hs
    exact h s n hn hb
end

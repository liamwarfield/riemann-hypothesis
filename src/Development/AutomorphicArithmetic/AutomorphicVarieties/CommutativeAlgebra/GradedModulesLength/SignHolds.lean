module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Mprime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.PrimeMaximalOrKernel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SignHolds
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.kill_pow {O B A κ : Type} [CommRing O] [CommRing B] [CommRing A] [Algebra O A]
    [Algebra B A] [Field κ] [Algebra O κ] (ξ : A →ₐ[O] κ) (N : Submodule B A) (hN : ∀ f ∈ N, ξ f = 0)
    (n : ℕ) (hn : n ≠ 0) : ∀ f ∈ N ^ n, ξ f = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  intro f hf
  rw [pow_succ] at hf
  refine Submodule.mul_induction_on hf (fun a _ b hb => ?_) (fun a b ha hb => ?_)
  · rw [map_mul, hN b hb, mul_zero]
  · rw [map_add (f := _), ha, hb, add_zero]

theorem UpperTheory.V.Alg.M.sign_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (κ : Type) [Field κ] [Algebra O κ] (ξ : A →ₐ[O] κ),
      (¬ NegZero 𝒜 ξ ↔ ∃ f ∈ 𝒜 (-2), ξ f ≠ 0) ∧ (¬ PosZero 𝒜 ξ ↔ ∃ g ∈ 𝒜 2, ξ g ≠ 0) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx κ _ _ ξ
  have hp := UpperTheory.V.Alg.M.oz_two_mul_eq_pow O A 𝒜 x hx
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, ?_⟩⟩
  · by_contra hc
    push Not at hc
    refine h fun j hj f hf => ?_
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -j by omega)
    have h2 : f * f ∈ oz 𝒜 (-(2 * (n : ℤ))) := by
      have := SetLike.GradedMul.mul_mem hf hf
      rwa [show j + j = -(2 * (n : ℤ)) by omega] at this
    rw [(hp n).1] at h2
    have h3 := UpperTheory.V.Alg.M.kill_pow ξ (oz 𝒜 (-2)) hc n (by omega) _ h2
    rw [map_mul] at h3
    exact mul_self_eq_zero.1 h3
  · rintro ⟨f, hf, h0⟩ h
    exact h0 (h (-2) (by norm_num) f hf)
  · by_contra hc
    push Not at hc
    refine h fun j hj f hf => ?_
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by omega)
    have h2 : f * f ∈ oz 𝒜 (2 * (n : ℤ)) := by
      have := SetLike.GradedMul.mul_mem hf hf
      rwa [show j + j = 2 * (n : ℤ) by omega] at this
    rw [(hp n).2] at h2
    have h3 := UpperTheory.V.Alg.M.kill_pow ξ (oz 𝒜 2) hc n (by omega) _ h2
    rw [map_mul] at h3
    exact mul_self_eq_zero.1 h3
  · rintro ⟨f, hf, h0⟩ h
    exact h0 (h 2 (by norm_num) f hf)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.TspHolds
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.tsp_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ I : Ideal A, I.IsHomogeneous 𝒜 → ∀ σ : 𝒜 0 →ₐ[O] K, (∀ b : 𝒜 0, (b : A) ∈ I → σ b = 0) →
      ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ res0 𝒜 ξ = σ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW I hI σ hσ
  haveI : Algebra.FiniteType (𝒜 0) A := (ft_holds O A 𝒜 x hW).1
  let p : A →ₗ[O] 𝒜 0 :=
    (DirectSum.component O ℤ (fun i => 𝒜 i) 0).comp (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
  have hpa : ∀ a : A, p a = DirectSum.decompose 𝒜 a 0 := fun a => rfl
  have pz : ∀ {i : ℤ} {u : A}, u ∈ 𝒜 i → i ≠ 0 → p u = 0 := by
    intro i u hu hi
    apply Subtype.ext
    rw [hpa]
    simpa using DirectSum.decompose_of_mem_ne 𝒜 hu hi
  have ps : ∀ {u : A} (hu : u ∈ 𝒜 0), p u = ⟨u, hu⟩ := by
    intro u hu
    apply Subtype.ext
    rw [hpa]
    exact DirectSum.decompose_of_mem_same 𝒜 hu
  set J : Ideal A := I ⊔ Ideal.map (algebraMap (𝒜 0) A) (RingHom.ker σ) with hJ
  have hgen : ∀ c : 𝒜 0, σ c = 0 → ∀ a : A, σ (p (a * (c : A))) = 0 := by
    intro c hc a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous a =>
      have hm : (a : A) * c ∈ 𝒜 (_ + 0) := SetLike.mul_mem_graded a.2 c.2
      rename_i i
      by_cases hi : i = 0
      · subst hi
        have hm' : (a : A) * c ∈ 𝒜 0 := by simpa using hm
        rw [ps hm', show (⟨(a : A) * c, hm'⟩ : 𝒜 0) = ⟨a, a.2⟩ * c from rfl, map_mul, hc, mul_zero]
      · rw [pz hm (by simpa using hi), map_zero]
    | add u v hu hv => rw [add_mul, map_add (f := _), map_add (f := _), hu, hv, add_zero]
  have hJ0 : ∀ y ∈ J, σ (p y) = 0 := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    clear hy
    have h1 : σ (p u) = 0 := by
      apply hσ
      rw [hpa]
      exact hI 0 hu
    have h2 : ∀ a : A, σ (p (a * v)) = 0 := by
      unfold Ideal.map at hv
      induction hv using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨c, hc, rfl⟩ := hw
        exact hgen c hc
      | zero => simp
      | add w w' _ _ hw hw' =>
        intro a
        rw [mul_add, map_add (f := _), map_add (f := _), hw, hw', add_zero]
      | smul a' w _ hw =>
        intro a
        rw [smul_eq_mul, ← mul_assoc]
        exact hw (a * a')
    have h3 := h2 1
    rw [one_mul] at h3
    rw [map_add (f := _), map_add (f := _), h1, h3, add_zero]
  obtain ⟨ξ, hξ1, hξ2, -⟩ := ns_holds O (𝒜 0) A K σ J 1
    (fun b hb => Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb))
    (by
      intro b n hb hmem
      apply hb
      rw [one_pow, mul_one] at hmem
      have := hJ0 _ hmem
      rwa [show (algebraMap (𝒜 0) A b) = (b : A) from rfl, ps b.2] at this)
  refine ⟨ξ, fun u hu => hξ2 u (Ideal.mem_sup_left hu), ?_⟩
  ext b
  exact hξ1 b
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Latfil
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {O A E τ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing E] [Algebra O E]
  (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ E)

private theorem mem_fil_zero (g : MvPowerSeries τ E) : g ∈ fil E wt 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

private theorem fil_mul {a b : ℕ} {g h : MvPowerSeries τ E} (hg : g ∈ fil E wt a) (hh : h ∈ fil E wt b) :
    g * h ∈ fil E wt (a + b) := (fil_holds E τ wt a b g h hg hh).1

private theorem fil_of_wt {j : ℤ} {g : MvPowerSeries τ E} (hg : g ∈ wtPart E wt j) : g ∈ fil E wt (-j).toNat :=
  (fil_holds E τ wt 0 0 g g (mem_fil_zero wt g) (mem_fil_zero wt g)).2 j hg

private def sf (j : ℤ) (n : ℕ) : Submodule (𝒜 0) A where
  carrier := {f | f ∈ 𝒜 j ∧ φ f ∈ fil E wt n}
  add_mem' hf hg := ⟨add_mem hf.1 hg.1, by
    rw [map_add φ]
    exact add_mem hf.2 hg.2⟩
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  smul_mem' c f hf := by
    refine ⟨(oz 𝒜 j).smul_mem c hf.1, ?_⟩
    show φ ((c : A) * f) ∈ fil E wt n
    have := fil_mul wt (mem_fil_zero wt (φ (c : A))) hf.2
    rwa [zero_add, ← map_mul] at this

private theorem sf_mul {j j' : ℤ} {n n' : ℕ} {M M' : Submodule (𝒜 0) A} (h : M ≤ sf 𝒜 wt φ j n)
    (h' : M' ≤ sf 𝒜 wt φ j' n') : M * M' ≤ sf 𝒜 wt φ (j + j') (n + n') := by
  rw [Submodule.mul_le]
  intro a ha b hb
  obtain ⟨ha1, ha2⟩ := h ha
  obtain ⟨hb1, hb2⟩ := h' hb
  refine ⟨SetLike.GradedMul.mul_mem ha1 hb1, ?_⟩
  rw [map_mul]
  exact fil_mul wt ha2 hb2

private theorem sf_pow {j : ℤ} {n : ℕ} {M : Submodule (𝒜 0) A} (h : M ≤ sf 𝒜 wt φ j n) (k : ℕ) :
    M ^ k ≤ sf 𝒜 wt φ (k * j) (k * n) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    rw [Submodule.one_le]
    refine ⟨SetLike.GradedOne.one_mem, ?_⟩
    exact mem_fil_zero wt _
  | succ k ih =>
    have := sf_mul 𝒜 wt φ ih h
    rw [pow_succ]
    convert this using 2 <;> push_cast <;> ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.Alg.M.latfil_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    ∀ F ∈ 𝒜 (-1), F ∈ satSq x → ∀ (μ : Fin 3 →₀ ℕ) (f : A), f ∈ lat (mN 𝒜 F) μ →
      f ∈ 𝒜 (2 * ((μ 1 : ℤ) - μ 0 - μ 2)) ∧ φ f ∈ fil (FractionRing O) wt (2 * μ 0 + 4 * μ 2) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW τ _ wt φ hφ F hF hFs μ f hf
  have h0 : oz 𝒜 (-2) ≤ sf 𝒜 wt φ (-2) 2 := fun g hg => ⟨hg, fil_of_wt wt (hφ.graded (-2) g hg)⟩
  have h1 : oz 𝒜 2 ≤ sf 𝒜 wt φ 2 0 := fun g hg => ⟨hg, mem_fil_zero wt _⟩
  have hF2 : φ F ∈ fil (FractionRing O) wt 2 := (satfil_holds O A 𝒜 x hW τ wt φ hφ).1 F hF hFs
  have h2 : Submodule.span (𝒜 0) {F ^ 2} ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 ≤ sf 𝒜 wt φ (-2) 4 := by
    refine sup_le ?_ (sf_mul 𝒜 wt φ (sf_mul 𝒜 wt φ h0 h0) h1)
    rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨sq_mem_neg 𝒜 hF, ?_⟩
    rw [sq, map_mul]
    exact fil_mul wt hF2 hF2
  rw [lat, Fin.prod_univ_three] at hf
  have key := sf_mul 𝒜 wt φ (sf_mul 𝒜 wt φ (sf_pow 𝒜 wt φ h0 (μ 0)) (sf_pow 𝒜 wt φ h1 (μ 1)))
    (sf_pow 𝒜 wt φ h2 (μ 2)) hf
  have e1 : 2 * ((μ 1 : ℤ) - μ 0 - μ 2) = μ 0 * (-2) + μ 1 * 2 + μ 2 * (-2) := by ring
  have e2 : 2 * μ 0 + 4 * μ 2 = μ 0 * 2 + μ 1 * 0 + μ 2 * 4 := by ring
  rw [e1, e2]
  exact key
end

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CocycleTraceZero
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DerInner
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.der_inner :
    ∀ {K E : Type} [CommRing K] [Ring E] [Algebra K E] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (j : (∀ s, Matrix (d s) (d s) K) →ₐ[K] E) (D : (∀ s, Matrix (d s) (d s) K) →ₗ[K] E), (∀ x y, D (x * y) = D x * j y + j x * D y) → ∃ Y : E, ∀ x, D x = Y * j x - j x * Y := by
  intro K E _ _ _ σ _ _ d _ _ _ j D hD
  let i0 : ∀ s, d s := fun s => Classical.arbitrary (d s)
  let u : ∀ s, d s → d s → (∀ s, Matrix (d s) (d s) K) :=
    fun s p q => Pi.single s (Matrix.single p q (1 : K))
  have hsame : ∀ s (p q r w : d s), u s p q * u s r w = if q = r then u s p w else 0 := by
    intro s p q r w
    simp only [u, ← Pi.single_mul]
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Pi.single_zero]
  have hne : ∀ s t (p q : d s) (r w : d t), s ≠ t → u s p q * u t r w = 0 := by
    intro s t p q r w h
    funext x
    simp only [u, Pi.mul_apply, Pi.zero_apply]
    by_cases hx : x = s
    · subst hx
      rw [Pi.single_eq_of_ne h, mul_zero]
    · rw [Pi.single_eq_of_ne hx, zero_mul]
  have hone : ∑ s, ∑ k, u s k k = 1 := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · rw [Finset.sum_apply]
      ext a b
      simp only [u, Pi.single_eq_same, Matrix.sum_apply, Matrix.single_apply, Pi.one_apply,
        Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Finset.sum_eq_zero fun k _ => if_neg fun h => hab (h.1.symm.trans h.2)]
        simp [hab]
    · intro s _ hs
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => Pi.single_eq_of_ne (Ne.symm hs) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  let a : E := ∑ s, ∑ k, j (u s k (i0 s)) * D (u s (i0 s) k)
  have key : ∀ t (p q : d t), D (u t p q) = j (u t p q) * a - a * j (u t p q) := by
    intro t p q
    have h1 : j (u t p q) * a = j (u t p (i0 t)) * D (u t (i0 t) q) := by
      simp only [a, Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single q]
        · rw [hsame, if_pos rfl]
        · intro k _ hk
          rw [hsame, if_neg (Ne.symm hk), map_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hne t s _ _ _ _ (Ne.symm hs), map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hS1 : ∑ s, ∑ k, j (u s k (i0 s)) * D (u s (i0 s) k * u t p q)
        = j (u t p (i0 t)) * D (u t (i0 t) q) := by
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single p]
        · rw [hsame, if_pos rfl]
        · intro k _ hk
          rw [hsame, if_neg hk, map_zero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hne s t _ _ _ _ hs, map_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hS2 : ∑ s, ∑ k, j (u s k (i0 s)) * j (u s (i0 s) k) = 1 := by
      simp only [← map_mul, hsame, eq_self_iff_true, if_true]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_sum]
      rw [hone, map_one]
    have e : a * j (u t p q) = ∑ s, ∑ k, (j (u s k (i0 s)) * D (u s (i0 s) k * u t p q)
        - j (u s k (i0 s)) * j (u s (i0 s) k) * D (u t p q)) := by
      simp only [a, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hD]
      noncomm_ring
    rw [h1, e]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hS1, hS2, one_mul]
    abel
  refine ⟨-a, fun x => ?_⟩
  have hlin : D = (LinearMap.mulRight K a).comp j.toLinearMap
      - (LinearMap.mulLeft K a).comp j.toLinearMap := by
    refine (Pi.basis fun s => Matrix.stdBasis K (d s) (d s)).ext fun ji => ?_
    obtain ⟨t, p, q⟩ := ji
    rw [Pi.basis_apply, Matrix.stdBasis_eq_single]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
    exact key t p q
  have hx := LinearMap.congr_fun hlin x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply] at hx
  rw [hx]
  noncomm_ring
end

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.cocycle_trace_zero :
    ∀ {K G : Type} [CommRing K] [Group G] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (r : G →* (∀ s, Matrix (d s) (d s) K)) (φ : G → ∀ s, Matrix (d s) (d s) K), Submodule.span K (Set.range r) = ⊤ → (∀ g h, φ (g * h) = φ g + r g * φ h * r g⁻¹) → (∀ g, ∑ s, ((φ g * r g) s).trace = 0) → ∃ Y, ∀ g, φ g = Y - r g * Y * r g⁻¹ := by
  intro K G _ _ σ _ _ d _ _ _ r φ hspan hφ htr
  classical
  let m : G → ∀ s, Matrix (d s) (d s) K := fun g => φ g * r g
  have hinv : ∀ g, r g⁻¹ * r g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : ∀ g, r g * r g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hm : ∀ g h, m (g * h) = m g * r h + r g * m h := by
    intro g h
    simp only [m, hφ, map_mul, add_mul, mul_assoc]
    rw [← mul_assoc (r g⁻¹), hinv, one_mul]
  let T : (∀ s, Matrix (d s) (d s) K) →ₗ[K] K :=
    ∑ s, (Matrix.traceLinearMap (d s) K K) ∘ₗ LinearMap.proj s
  have hT : ∀ x, T x = ∑ s, (x s).trace := by
    intro x
    simp [T, LinearMap.sum_apply]
  have hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0 := by
    intro x hx
    funext s
    rw [Matrix.ext_iff_trace_mul_right]
    intro y
    have := hx (Pi.single s y)
    rw [hT, Finset.sum_eq_single s] at this
    · simpa using this
    · intro t _ ht
      simp [Pi.single_eq_of_ne ht]
    · simp
  have hkey : ∀ g h, T (m g * r h) = - T (r g * m h) := by
    intro g h
    have : T (m (g * h)) = 0 := by rw [hT]; exact htr _
    rw [hm, map_add (f := _)] at this
    exact eq_neg_of_add_eq_zero_left this
  let R := Finsupp.linearCombination K (fun g => r g)
  let M := Finsupp.linearCombination K m
  have hR : Function.Surjective R := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  have hkey2 : ∀ f h, T (M f * r h) = - T (R f * m h) := by
    intro f h
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add (f := _), add_mul, h₁, h₂]; ring
    | single g a =>
      simp only [R, M, Finsupp.linearCombination_single, smul_mul_assoc, map_smul, hkey, smul_neg]
  have hle : LinearMap.ker R ≤ LinearMap.ker M := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply hnd
    intro y
    have hy : y ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hkey2, hf]; simp
    | zero => simp
    | add x y _ _ h₁ h₂ => rw [mul_add, map_add (f := _), h₁, h₂, add_zero]
    | smul a x _ h₁ => rw [mul_smul_comm, map_smul, h₁, smul_zero]
  let D : (∀ s, Matrix (d s) (d s) K) →ₗ[K] (∀ s, Matrix (d s) (d s) K) :=
    (LinearMap.ker R).liftQ M hle ∘ₗ (R.quotKerEquivOfSurjective hR).symm.toLinearMap
  have hDR : ∀ f, D (R f) = M f := by
    intro f
    have : (R.quotKerEquivOfSurjective hR).symm (R f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp [D, this]
  have hDr : ∀ g, D (r g) = m g := by
    intro g
    simpa [R, M] using hDR (Finsupp.single g 1)
  have hder : ∀ x y, D (x * y) = D x * y + x * D y := by
    intro x y
    have hx : x ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    have hy : y ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      rw [← map_mul, hDr, hDr, hDr, hm]
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h₁ h₂ => simp only [add_mul, map_add (f := _), h₁, h₂]; abel
    | add_right x y z _ _ _ h₁ h₂ => simp only [mul_add, map_add (f := _), h₁, h₂]; abel
    | smul_left a x y _ _ h₁ => simp only [smul_mul_assoc, map_smul, h₁, smul_add]
    | smul_right a x y _ _ h₁ => simp only [mul_smul_comm, map_smul, h₁, smul_add]
  obtain ⟨Y, hY⟩ := UpperTheory.V.AlgebraTools.der_inner d (AlgHom.id K _) D hder
  refine ⟨Y, fun g => ?_⟩
  have h1 : φ g = m g * r g⁻¹ := by simp only [m, mul_assoc, hinv', mul_one]
  rw [h1, ← hDr, hY]
  simp only [AlgHom.id_apply, sub_mul]
  rw [mul_assoc Y, hinv', mul_one]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem detG_central {K G : Type} [Field K] [Group G] {n : ℕ}
    (m : G →* Matrix (Fin n) (Fin n) K) (χ : G →* Kˣ) (N : Subgroup G)
    (w : G → Matrix (Fin n) (Fin n) K) (hc : commutator G ≤ N) (hk : N ≤ χ.ker) (hχ : χ ≠ 1)
    (hspan : Submodule.span K (Set.range (m.comp N.subtype)) = ⊤)
    (hw : ∀ g g', w (g * g') = w g + (χ g : K) • (m g * w g' * m g⁻¹))
    (h0 : ∀ g ∈ N, w g = 0) :
    ∃ A, ∀ g, w g = (χ g : K) • (m g * A * m g⁻¹) - A := by
  have hinv : ∀ g, m g⁻¹ * m g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : ∀ g, m g * m g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hcom : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ N := fun g h =>
    hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
  have hone : ∀ x ∈ N, (χ x : K) = 1 := fun x hx => by
    have : χ x = 1 := hk hx
    rw [this, Units.val_one]
  have hconj : ∀ g, ∀ x ∈ N, w g = m x * w g * m x⁻¹ := by
    intro g x hx
    have hy : g⁻¹ * x * g ∈ N := by
      have := N.mul_mem (hcom g⁻¹ x) hx
      simpa [mul_assoc] using this
    have e : x * g = g * (g⁻¹ * x * g) := by simp [mul_assoc]
    have h1 := hw x g
    rw [e, hw, h0 _ hy, h0 _ hx, hone x hx] at h1
    simpa using h1
  have hcen : ∀ g (X : Matrix (Fin n) (Fin n) K), X * w g = w g * X := by
    intro g X
    have hX : X ∈ Submodule.span K (Set.range (m.comp N.subtype)) := hspan ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      change m y * w g = w g * m y
      conv_rhs => rw [hconj g y y.2]
      rw [mul_assoc, hinv, mul_one]
    | zero => simp
    | add x y _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]
    | smul a x _ h₁ => rw [mul_smul_comm, smul_mul_assoc, h₁]
  have hfix : ∀ g h, m g * w h * m g⁻¹ = w h := fun g h => by
    rw [hcen, mul_assoc, hinv', mul_one]
  have hw' : ∀ g h, w (g * h) = w g + (χ g : K) • w h := fun g h => by rw [hw, hfix]
  have hsym : ∀ g h, w (g * h) = w (h * g) := by
    intro g h
    have e : g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by simp [mul_assoc]
    rw [e, hw' (g * h * g⁻¹ * h⁻¹), h0 _ (hcom g h), hone _ (hcom g h), zero_add, one_smul]
  obtain ⟨h, hh⟩ : ∃ h, χ h ≠ 1 := by
    by_contra hn
    exact hχ (MonoidHom.ext fun g => by_contra fun hg => hn ⟨g, hg⟩)
  have hh' : (χ h : K) - 1 ≠ 0 := fun e => hh (Units.ext (by simpa using sub_eq_zero.mp e))
  refine ⟨((χ h : K) - 1)⁻¹ • w h, fun g => ?_⟩
  have h1 := hsym g h
  rw [hw', hw'] at h1
  have h2 : ((χ h : K) - 1) • w g = (χ g : K) • w h - w h := by
    rw [sub_smul, one_smul, sub_eq_sub_iff_add_eq_add, add_comm, ← h1, add_comm]
  rw [mul_smul_comm, smul_mul_assoc, hfix, smul_comm, ← smul_sub, ← h2, smul_smul,
    inv_mul_cancel₀ hh', one_smul]

theorem UpperTheory.V.Th.Det.detG :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) K) (χ : G →* Kˣ) (N : Subgroup G) (z : G → Matrix (Fin n) (Fin n) K), 1 ≤ n → commutator G ≤ N → N ≤ χ.ker → χ ≠ 1 → U3.MatIrr N (W.mat ρ) → (∀ g g', z (g * g') = z g + (χ g : K) • (W.mat ρ g * z g' * W.mat ρ g⁻¹)) → (∀ g ∈ N, (z g * W.mat ρ g).trace = 0) → ∃ Y, ∀ g, z g = (χ g : K) • (W.mat ρ g * Y * W.mat ρ g⁻¹) - Y := by
  intro K G _ _ _ n ρ χ N z hn hc hk hχ hirr hz htr
  generalize W.mat ρ = m at hirr hz htr ⊢
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hone : ∀ x ∈ N, (χ x : K) = 1 := fun x hx => by
    have : χ x = 1 := hk hx
    rw [this, Units.val_one]
  have hspan : Submodule.span K (Set.range (m.comp N.subtype)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun U hU => hirr U fun g hg v hv => hU ⟨g, hg⟩ v hv
  let r : N →* (∀ _ : Unit, Matrix (Fin n) (Fin n) K) := MonoidHom.pi fun _ => m.comp N.subtype
  have hspan' : Submodule.span K (Set.range r) = ⊤ := by
    let L : Matrix (Fin n) (Fin n) K →ₗ[K] (∀ _ : Unit, Matrix (Fin n) (Fin n) K) :=
      LinearMap.pi fun _ => LinearMap.id
    have hL : Function.Surjective L := fun x => ⟨x (), rfl⟩
    have e : Set.range r = L '' Set.range (m.comp N.subtype) := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hL]
  obtain ⟨Y₀, hY₀⟩ := UpperTheory.V.AlgebraTools.cocycle_trace_zero (K := K) (fun _ : Unit => Fin n) r
    (fun g _ => z g) hspan'
    (fun g h => by
      funext s
      have := hz g h
      rw [hone g g.2, one_smul] at this
      exact this)
    (fun g => by
      rw [Fintype.sum_unique]
      exact htr g g.2)
  have hY : ∀ g ∈ N, z g = Y₀ () - m g * Y₀ () * m g⁻¹ := fun g hg => congrFun (hY₀ ⟨g, hg⟩) ()
  have hinv' : ∀ g, m g * m g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨A, hA⟩ := detG_central m χ N
    (fun g => z g + ((χ g : K) • (m g * Y₀ () * m g⁻¹) - Y₀ ())) hc hk hχ hspan
    (fun g h => by
      simp only [hz, map_mul, _root_.mul_inv_rev, Units.val_mul, mul_add, add_mul, mul_sub, sub_mul,
        smul_add, smul_sub, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
      abel)
    (fun g hg => by
      simp only [hY g hg, hone g hg, one_smul]
      abel)
  refine ⟨A - Y₀ (), fun g => ?_⟩
  have := hA g
  simp only [mul_sub, sub_mul, smul_sub]
  rw [eq_sub_of_add_eq this]
  abel

module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OkLinearTorsionCorrespondenceMapsLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OkLinearTorsionCorrespondenceMapsLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

theorem rationalLatticePoint_add {Λ : AddSubgroup ℂ} {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, h⟩ := hx
  obtain ⟨n, hn, h'⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have : ((m * n : ℕ) : ℂ) * (x + y) = n • ((m : ℂ) * x) + m • ((n : ℂ) * y) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [this]
  exact add_mem (nsmul_mem h n) (nsmul_mem h' m)

theorem rationalLatticePoint_neg {Λ : AddSubgroup ℂ} {x : ℂ} (hx : InRationalLattice Λ x) : InRationalLattice Λ (-x) := by
  obtain ⟨m, hm, h⟩ := hx
  exact ⟨m, hm, by rw [mul_neg]; exact neg_mem h⟩

theorem rationalLatticePoint_div_natCast {Λ : AddSubgroup ℂ} {w : ℂ} (hw : w ∈ Λ) {m : ℕ} (hm : 0 < m) : InRationalLattice Λ (w / m) := by
  refine ⟨m, hm, ?_⟩
  have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [mul_div_cancel₀ _ this]; exact hw

theorem Good.embV_nsmul {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ} (k : ℕ)
    (A : Matrix (Fin N') (Fin N) D.host.E) : embV D T (k • A) = (k : ℂ) • embV D T A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact map_nsmul (h.embHom N N') k A

theorem Good.embV_sum {D : D7} {T : Tor D} (h : Good D T) {N N' r : ℕ} (a : Fin r → D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    embV D T (∑ j, a j • b j) = ∑ j, D.host.φ₀ (a j : D.host.E) • embV D T (b j) := by
  have := map_sum (h.embHom N N') (fun j => a j • b j) Finset.univ
  refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
  exact h.embV_smul _ _

theorem Good.smul_embV_mem {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ}
    {Y : Set (Matrix (Fin N') (Fin N) D.host.E)} {w : ℂ} (hw : w ∈ T.abelian₂)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ AddSubgroup.closure Y) :
    w • embV D T y ∈ LaS D T Y := by
  change w • h.embHom N N' y ∈ _
  induction hy using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubgroup.subset_closure ⟨w, hw, x, hx, rfl⟩
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

theorem corr_lattice : ∀ (D : D7) (T T' : Tor D), Good D T → Good D T' → (∀ a : 𝓞 D.host.K, ∀ w ∈ T.abelian₂, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ T.abelian₂) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.Orthonormal D b → ∀ (S : ℂ → ℂ → Prop), (∀ t, InRationalLattice T.abelian₂ t → ∃ t', S t t') → (∀ t t₁ t₂, S t t₁ → S t t₂ → t₁ - t₂ ∈ T'.abelian₂) → (∀ t t' u u', S t t' → S u u' → S (t + u) (t' + u')) → (∀ (a : 𝓞 D.host.K) t t', S t t' → S (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t) (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t')) → (∀ (m : ℕ) t t', S t t' → (m : ℂ) * t ∈ T.abelian₂ → (m : ℂ) * t' ∈ T'.abelian₂) → ∀ (n k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < n → 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧ x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧ ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y) ∧ ∀ c c' : Fin r → ℂ, (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) → ∑ j, c j • embV D T (b j) ∈ LaS D T Y → ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
  intro D T T' hT hT' hO N N' r b hb S hex huniq hadd hmul hint n k Y hn hk hkn hC
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hS0 : S 0 0 := by
    obtain ⟨t', ht'⟩ := hex 0 ⟨1, one_pos, by simp⟩
    simpa using hmul 0 _ _ ht'
  have hneg : ∀ t t', S t t' → S (-t) (-t') := fun t t' h => by
    simpa using hmul (-1) _ _ h
  have first : ∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧
      x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧
      ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, y, hy, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hC.1 y hy
      obtain ⟨u', hu'⟩ := hex _ (rationalLatticePoint_div_natCast hw (Nat.mul_pos hn hk))
      have hnk : ((n * k : ℕ) : ℂ) * u' ∈ T'.abelian₂ := by
        refine hint _ _ _ hu' ?_
        rw [mul_div_cancel₀ _ (by push_cast; exact mul_ne_zero hn0 hk0)]; exact hw
      have e1 := hT.embV_sum (fun j => (a j : D.host.K)) b
      have e2 := hT'.embV_sum (fun j => (a j : D.host.K)) b
      rw [← ha, hT.embV_nsmul] at e1
      rw [← ha, hT'.embV_nsmul] at e2
      refine ⟨fun j => D.host.φ₀ ((a j : D.host.K) : D.host.E) * w / k,
        fun j => n * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u'),
        fun j => rationalLatticePoint_div_natCast (hO _ _ hw) hk, ?_, fun j => ?_, ?_⟩
      · have : w • embV D T y = (w / k) • ((k : ℂ) • embV D T y) := by
          rw [smul_smul, div_mul_cancel₀ _ hk0]
        rw [this, e1, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]; congr 1; ring
      · have := hmul (a j) _ _ hu'
        convert this using 1
        · push_cast; field_simp
        · field_simp
      · have : ∑ j, ((n : ℂ) * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u')) • embV D T' (b j)
            = (((n * k : ℕ) : ℂ) * u') • embV D T' y := by
          have h2 : (((n * k : ℕ) : ℂ) * u') • embV D T' y
              = ((n : ℂ) * u') • ((k : ℂ) • embV D T' y) := by
            rw [smul_smul]; congr 1; push_cast; ring
          rw [h2, e2, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul]; congr 1; ring
        rw [this]
        exact AddSubgroup.subset_closure ⟨_, hnk, y, hy, rfl⟩
    | zero =>
      refine ⟨0, 0, fun j => ⟨1, one_pos, by simp⟩, by simp, fun j => by simpa using hS0, ?_⟩
      simp
    | add x y _ _ hx hy =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      obtain ⟨d, d', g1, g2, g3, g4⟩ := hy
      refine ⟨c + d, c' + d', fun j => rationalLatticePoint_add (h1 j) (g1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, g2, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, add_smul]
      · simp only [Pi.add_apply, add_div]; exact hadd _ _ _ _ (h3 j) (g3 j)
      · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; exact add_mem h4 g4
    | neg x _ hx =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      refine ⟨-c, -c', fun j => rationalLatticePoint_neg (h1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, ← Finset.sum_neg_distrib]; simp only [Pi.neg_apply, neg_smul]
      · simp only [Pi.neg_apply, neg_div]; exact hneg _ _ (h3 j)
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]; exact neg_mem h4
  refine ⟨first, fun c c' hS hc => ?_⟩
  obtain ⟨d, d', -, h2, h3, h4⟩ := first _ hc
  have hcd : c = d := by
    funext j
    rw [← hT.coordB_sum hb c j, h2, hT.coordB_sum hb]
  subst hcd
  obtain ⟨m, hm⟩ := hkn
  have key : ∀ j, (c' j - d' j) • embV D T' (b j) ∈ LaS D T' Y := fun j => by
    have h5 := nsmul_mem (huniq _ _ _ (hS j) (h3 j)) m
    have h6 := hT'.smul_embV_mem h5 (hC.2 j)
    rw [hT'.embV_nsmul, smul_smul] at h6
    convert h6 using 2
    have hm' : (n : ℂ) = k * m := by rw [hm]; push_cast; rfl
    rw [nsmul_eq_mul, ← sub_div, mul_right_comm, mul_comm (m : ℂ), ← hm', mul_div_cancel₀ _ hn0]
  have : ∑ j, c' j • embV D T' (b j)
      = ∑ j, d' j • embV D T' (b j) + ∑ j, (c' j - d' j) • embV D T' (b j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_smul]; congr 1; ring
  rw [this]
  exact add_mem h4 (sum_mem fun j _ => key j)

end GlobalTheory.ThetaConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OkLinearTorsionCorrespondenceMapsLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.okLinear_torsionCorrespondence_maps_lattice : ∀ (D : D7) (T T' : Tor D), Good D T → Good D T' → (∀ a : 𝓞 D.host.K, ∀ w ∈ T.abelian₂, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ T.abelian₂) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.Orthonormal D b → ∀ (S : ℂ → ℂ → Prop), (∀ t, InRationalLattice T.abelian₂ t → ∃ t', S t t') → (∀ t t₁ t₂, S t t₁ → S t t₂ → t₁ - t₂ ∈ T'.abelian₂) → (∀ t t' u u', S t t' → S u u' → S (t + u) (t' + u')) → (∀ (a : 𝓞 D.host.K) t t', S t t' → S (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t) (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t')) → (∀ (m : ℕ) t t', S t t' → (m : ℂ) * t ∈ T.abelian₂ → (m : ℂ) * t' ∈ T'.abelian₂) → ∀ (n k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < n → 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧ x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧ ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y) ∧ ∀ c c' : Fin r → ℂ, (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) → ∑ j, c j • embV D T (b j) ∈ LaS D T Y → ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
  first | exact @GlobalTheory.ThetaConj.corr_lattice | exact GlobalTheory.ThetaConj.corr_lattice | (intros; apply GlobalTheory.ThetaConj.corr_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionMapCarriesTorusLattices
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_coords_of_mem_LaB (D : D7) (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : VC D N N') (hy : y ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, w j ∈ T.abelian₂) ∧ y = ∑ j, w j • embV D T (b j) := by
  unfold LaB at hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, i, rfl⟩ := hz
    refine ⟨Pi.single i w, fun j => ?_, ?_⟩
    · by_cases h : j = i
      · subst h; simpa using hw
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨w, hw, rfl⟩ := hy
    obtain ⟨w', hw', rfl⟩ := hz
    refine ⟨w + w', fun j => add_mem (hw j) (hw' j), ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨fun j => -w j, fun j => neg_mem (hw j), ?_⟩
    simp only [neg_smul, Finset.sum_neg_distrib]

theorem adpB_lattices : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → (∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ n : ℕ, 0 < n → (∀ x x' y y', AdpB D (tor0 D cc δ) M ρ b n x x' → AdpB D (tor0 D cc δ) M ρ b n y y' → AdpB D (tor0 D cc δ) M ρ b n (x - y) (x' - y')) ∧ (∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → ∃ t', AdpB D (tor0 D cc δ) M ρ b n t t') ∧ ∀ (k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D (tor0 D cc δ) Y, ∃ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ (∀ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, ∃ x ∈ LaS D (tor0 D cc δ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ ∀ x x', AdpB D (tor0 D cc δ) M ρ b n x x' → (x ∈ LaS D (tor0 D cc δ) Y ↔ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y) := by
  intro D hG hS cc δ hc M ρ hK hD hM N N' r b hb n hn
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := hS cc δ hc M ρ hK hD.2.1 hD.2.2
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hneg : ∀ t t', StarPt M ρ (lamOf D cc δ) t t' → StarPt M ρ (lamOf D cc δ) (-t) (-t') := by
    intro t t' h
    have := h5 (-1) t t' h
    simpa using this
  have hsub : ∀ t t' u u', StarPt M ρ (lamOf D cc δ) t t' → StarPt M ρ (lamOf D cc δ) u u' →
      StarPt M ρ (lamOf D cc δ) (t - u) (t' - u') := by
    intro t t' u u' h h'
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact h4 _ _ _ _ h (hneg _ _ h')
  have hone : ∀ t t', StarPt M ρ (lamOf D cc δ) t t' →
      (t ∈ lamOf D cc δ ↔ t' ∈ lamConj M ρ (lamOf D cc δ)) := by
    intro t t' h
    simpa using h6 1 t t' h
  have hex : ∀ t, InRationalLattice (lamOf D cc δ) t → ∃ t', StarPt M ρ (lamOf D cc δ) t t' := by
    intro t hq
    refine h1 _ hq ?_
    by_cases h : t ∈ lamOf D cc δ
    · exact Or.inl h
    · exact Or.inr (hM _ hq h)
  have hex' : ∀ t', InRationalLattice (lamConj M ρ (lamOf D cc δ)) t' → ∃ t, StarPt M ρ (lamOf D cc δ) t t' := by
    rintro t' ⟨m, hm, ht'⟩
    obtain ⟨t, -, ht⟩ := h7 m hm (fun t h h' => hM t ⟨m, hm, h⟩ h') t' ht'
    exact ⟨t, ht⟩
  have hst : ∀ a : 𝓞 D.host.K, ∀ w ∈ lamOf D cc δ,
      D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
    intro a w hw
    have := h5 a w 0 (Or.inl ⟨hw, zero_mem _⟩)
    rw [hone _ _ this, mul_zero]; exact zero_mem _
  have hst' : ∀ a : 𝓞 D.host.K, ∀ w ∈ lamConj M ρ (lamOf D cc δ),
      D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamConj M ρ (lamOf D cc δ) := by
    intro a w hw
    have := h5 a 0 w (Or.inl ⟨zero_mem _, hw⟩)
    rw [← hone _ _ this, mul_zero]; exact zero_mem _
  have hT := isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ
  have hT' := good_torConj D hG cc δ M ρ hK hD
  refine ⟨?_, ?_, ?_⟩
  · rintro _ _ _ _ ⟨c, c', hc, rfl, rfl, hcc⟩ ⟨d, d', hd, rfl, rfl, hdd⟩
    refine ⟨c - d, c' - d', fun j => ?_, ?_, ?_, fun j => ?_⟩
    · obtain ⟨m, hm, h⟩ := hc j
      obtain ⟨m', hm', h'⟩ := hd j
      refine ⟨m * m', Nat.mul_pos hm hm', ?_⟩
      have : ((m * m' : ℕ) : ℂ) * (c - d) j = m' • ((m : ℂ) * c j) - m • ((m' : ℂ) * d j) := by
        simp only [nsmul_eq_mul, Pi.sub_apply]; push_cast; ring
      rw [this]
      exact sub_mem (AddSubgroup.nsmul_mem _ h _) (AddSubgroup.nsmul_mem _ h' _)
    · simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    · simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    · show StarPt M ρ (lamOf D cc δ) ((c j - d j) / n) ((c' j - d' j) / n)
      rw [sub_div, sub_div]
      exact hsub _ _ _ _ (hcc j) (hdd j)
  · intro x m hm hmx
    obtain ⟨w, hw, hsum⟩ := exists_coords_of_mem_LaB D _ b _ hmx
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hq : ∀ j, ∃ t', StarPt M ρ (lamOf D cc δ) (w j / m / n) t' := by
      intro j
      refine hex _ ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      have : ((m * n : ℕ) : ℂ) * (w j / m / n) = w j := by push_cast; field_simp
      rw [this]; exact hw j
    choose t' ht' using hq
    refine ⟨_, fun j => w j / m, fun j => (n : ℂ) * t' j, ?_, ?_, rfl, ?_⟩
    · intro j
      refine ⟨m, hm, ?_⟩
      have : (m : ℂ) * (w j / m) = w j := by field_simp
      rw [this]; exact hw j
    · have hx : x = (m : ℂ)⁻¹ • (m • x) := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
      rw [hx, hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← div_eq_inv_mul]
    · intro j
      have : (n : ℂ) * t' j / n = t' j := by field_simp
      show StarPt M ρ (lamOf D cc δ) (w j / m / n) ((n : ℂ) * t' j / n)
      rw [this]; exact ht' j
  · intro k Y hk hkn hY
    obtain ⟨A1, A2⟩ := GlobalTheory.T.okLinear_torsionCorrespondence_maps_lattice D (tor0 D cc δ) (torConj D (tor0 D cc δ) M ρ) hT hT' hst N N' r b hb.1
      (StarPt M ρ (lamOf D cc δ)) hex (fun t t₁ t₂ h h' => (h2 t t₁ t₂ h).1 h') h4 h5
      (fun m t t' h => (h6 m t t' h).1) n k Y hn hk hkn hY
    obtain ⟨B1, B2⟩ := GlobalTheory.T.okLinear_torsionCorrespondence_maps_lattice D (torConj D (tor0 D cc δ) M ρ) (tor0 D cc δ) hT' hT hst' N N' r b hb.1
      (fun t' t => StarPt M ρ (lamOf D cc δ) t t') hex'
      (fun t t₁ t₂ h h' => (hone _ _ (hsub _ _ _ _ h h')).2 (by rw [sub_self]; exact zero_mem _))
      (fun t t' u u' h h' => h4 _ _ _ _ h h') (fun a t t' h => h5 a _ _ h)
      (fun m t t' h => (h6 m _ _ h).2) n k Y hn hk hkn hY
    refine ⟨fun x hx => ?_, fun x' hx' => ?_, ?_⟩
    · obtain ⟨c, c', hc, hxc, hcc, hmem⟩ := A1 x hx
      exact ⟨_, hmem, c, c', hc, hxc, rfl, hcc⟩
    · obtain ⟨c', c, hc', hxc, hcc, hmem⟩ := B1 x' hx'
      refine ⟨_, hmem, c, c', fun j => ?_, rfl, hxc, hcc⟩
      obtain ⟨m, hm, h⟩ := hc' j
      refine ⟨m, hm, ?_⟩
      have h' := (h6 (m * n) _ _ (hcc j)).2 (by
        have : ((m * n : ℕ) : ℂ) * (c' j / n) = m * c' j := by push_cast; field_simp
        rw [this]; exact h)
      have : ((m * n : ℕ) : ℂ) * (c j / n) = m * c j := by push_cast; field_simp
      rw [this] at h'; exact h'
    · rintro _ _ ⟨c, c', -, rfl, rfl, hcc⟩
      exact ⟨A2 c c' hcc, B2 c' c hcc⟩

end GlobalTheory.ThetaConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionMapCarriesTorusLatticesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionMap_carries_torus_lattices : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → (∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ n : ℕ, 0 < n → (∀ x x' y y', AdpB D (tor0 D cc δ) M ρ b n x x' → AdpB D (tor0 D cc δ) M ρ b n y y' → AdpB D (tor0 D cc δ) M ρ b n (x - y) (x' - y')) ∧ (∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → ∃ t', AdpB D (tor0 D cc δ) M ρ b n t t') ∧ ∀ (k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D (tor0 D cc δ) Y, ∃ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ (∀ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, ∃ x ∈ LaS D (tor0 D cc δ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ ∀ x x', AdpB D (tor0 D cc δ) M ρ b n x x' → (x ∈ LaS D (tor0 D cc δ) Y ↔ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y) := by
  first | exact @GlobalTheory.ThetaConj.adpB_lattices | exact GlobalTheory.ThetaConj.adpB_lattices | (intros; apply GlobalTheory.ThetaConj.adpB_lattices <;> assumption)
end

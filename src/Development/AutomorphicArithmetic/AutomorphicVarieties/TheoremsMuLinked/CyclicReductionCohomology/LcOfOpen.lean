module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LcOfOpen
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem adEx_ext {l : ℕ} [Fact l.Prime] (F : GFrame l) {M : Type} [Monoid M] (a : F.G₀ →* M) (t : M)
    (ht : t * t = 1) (hc : ∀ g, t * a g = a (F.conj g) * t) :
    ∃ f : F.Γ →* M, (∀ g : F.G₀, f g = a g) ∧ f F.c = t := by
  classical
  have hcc := F.c_sq
  have hinv : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hm : ∀ γ : F.Γ, γ ∉ F.η.ker → γ * F.c ∈ F.η.ker := by
    intro γ h
    rw [MonoidHom.mem_ker] at h ⊢
    rcases Int.units_eq_one_or (F.η γ) with e | e
    · exact absurd e h
    · rw [map_mul, e, F.η_c]; simp
  have hn : ∀ g : F.G₀, (g : F.Γ) * F.c ∉ F.η.ker := by
    intro g h
    have h2 := g.2
    rw [MonoidHom.mem_ker] at h h2
    rw [map_mul, h2, F.η_c, one_mul] at h
    exact absurd h (by decide)
  let f : F.Γ → M := fun γ => if h : γ ∈ F.η.ker then a ⟨γ, h⟩ else a ⟨γ * F.c, hm γ h⟩ * t
  have f1 : ∀ g : F.G₀, f g = a g := fun g => by simp only [f, dif_pos g.2]
  have f2 : ∀ g : F.G₀, f (g * F.c) = a g * t := fun g => by
    simp only [f, dif_neg (hn g), mul_assoc, hcc, mul_one]
  have cases : ∀ γ : F.Γ, ∃ g : F.G₀, γ = g ∨ γ = g * F.c := by
    intro γ
    by_cases h : γ ∈ F.η.ker
    · exact ⟨⟨γ, h⟩, Or.inl rfl⟩
    · exact ⟨⟨γ * F.c, hm γ h⟩, Or.inr (by simp only [mul_assoc, hcc, mul_one])⟩
  have cj : ∀ g : F.G₀, ((F.conj g : F.G₀) : F.Γ) = F.c * g * F.c := fun g => by
    rw [← congrArg (F.c * (g : F.Γ) * ·) hinv]; rfl
  refine ⟨⟨⟨f, f1 1 |>.trans (map_one a)⟩, fun x y => ?_⟩, f1, ?_⟩
  · obtain ⟨g, rfl | rfl⟩ := cases x <;> obtain ⟨h, rfl | rfl⟩ := cases y
    · show f _ = f _ * f _
      rw [← Subgroup.coe_mul, f1, f1, f1, map_mul]
    · show f _ = f _ * f _
      rw [← mul_assoc, ← Subgroup.coe_mul, f2, f1, f2, map_mul, mul_assoc]
    · show f _ = f _ * f _
      have e : (g : F.Γ) * F.c * h = (g * F.conj h : F.G₀) * F.c := by
        rw [Subgroup.coe_mul, cj]; simp only [mul_assoc, hcc, mul_one]
      rw [e, f2, f2, f1, map_mul, mul_assoc, mul_assoc, hc]
    · show f _ = f _ * f _
      have e : (g : F.Γ) * F.c * (h * F.c) = (g * F.conj h : F.G₀) := by
        rw [Subgroup.coe_mul, cj]; simp only [mul_assoc]
      rw [e, f1, f2, f2, map_mul, mul_assoc, ← mul_assoc t, hc, mul_assoc, ht, mul_one]
  · have := f2 1
    rw [OneMemClass.coe_one, one_mul, map_one, one_mul] at this
    exact this

private theorem lc_of_open {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (h : ∀ m, IsLocallyConstant fun g : H => ρ g m) : LC ρ := by
  intro m
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have h1 : IsOpen {g : H | ρ g (ρ g0 m) = ρ g0 m} := (h (ρ g0 m)).isOpen_fiber _
  have h2 : IsOpen (Subtype.val '' {g : H | ρ g (ρ g0 m) = ρ g0 m}) := hH.isOpenMap_subtype_val _ h1
  have h3 : IsOpen ((fun g : Γ => g * g0⁻¹) ⁻¹' (Subtype.val '' {g : H | ρ g (ρ g0 m) = ρ g0 m})) :=
    h2.preimage (by fun_prop)
  have h4 : g0 ∈ ((fun g : Γ => g * g0⁻¹) ⁻¹' (Subtype.val '' {g : H | ρ g (ρ g0 m) = ρ g0 m})) :=
    ⟨1, by simp, by simp⟩
  filter_upwards [h3.mem_nhds h4] with g hg
  obtain ⟨u, hu, e⟩ := hg
  have e' : g = (u : Γ) * g0 := by rw [e]; simp
  rw [e', map_mul]
  exact hu

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem lc_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (m : ℕ)
    (hl : (l : R) ^ m = 0) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y0
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(m : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds y0 hpos] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨c, hc⟩ := hy
  rw [← sub_eq_zero, ← map_sub, ← hc, map_mul, map_pow, map_natCast, hl, mul_zero]

private theorem adP_ex {l : ℕ} [Fact l.Prime] (F : GFrame l) (A : Type) {R : Type} [CommRing A] [CommRing R] [Algebra A R]
    {n : ℕ} (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (P Q : Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (s : R)
    (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hs : s * s = 1)
    (hP : Pᵀ = s • P) (hf : ∀ g, ∃ u : R, (ρ g)ᵀ * P * ρ (F.conj g) = u • P)
    (c1 : χ 1 = 1) (cm : ∀ g h, χ (g * h) = χ g * χ h) :
    ∃ rep : Representation A F.Γ (Matrix (Fin n) (Fin n) R), IsAdP F ρ P χ rep := by
  have hcc : χ F.c * χ F.c = 1 := by rw [← cm, F.c_sq, c1]
  have hinv : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  have hχ : ∀ g : F.G₀, χ (F.conj g : F.G₀) = χ g := fun g => by
    show χ (F.c * g * F.c⁻¹) = _
    rw [hinv, cm, cm, mul_right_comm, hcc, one_mul]
  have hQ : Qᵀ * P = s • (1 : Matrix (Fin n) (Fin n) R) := by
    have e : Qᵀ * Pᵀ = 1 := by rw [← transpose_mul, hPQ, transpose_one]
    rw [← e, hP, Matrix.mul_smul, smul_smul, hs, one_smul]
  have key : ∀ (g : F.G₀) (Z : Matrix (Fin n) (Fin n) R),
      Q * (ρ g * Z * ρ g⁻¹)ᵀ * P = ρ (F.conj g) * (Q * Zᵀ * P) * ρ (F.conj g)⁻¹ := by
    intro g Z
    obtain ⟨u, hu⟩ := hf g
    have e1 : ρ (F.conj g) * Q = u • (Q * (ρ g⁻¹)ᵀ) := by
      have : (ρ g⁻¹)ᵀ * (ρ g)ᵀ = 1 := by
        rw [← transpose_mul, ← hm, mul_inv_cancel, h1, transpose_one]
      calc ρ (F.conj g) * Q = Q * ((ρ g⁻¹)ᵀ * (ρ g)ᵀ * P) * ρ (F.conj g) * Q := by
            rw [this, Matrix.one_mul, hQP, Matrix.one_mul]
        _ = Q * (ρ g⁻¹)ᵀ * ((ρ g)ᵀ * P * ρ (F.conj g)) * Q := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hu, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc _ P, hPQ, Matrix.mul_one]
    have e2 : (ρ g)ᵀ * P = u • (P * ρ (F.conj g)⁻¹) := by
      calc (ρ g)ᵀ * P = (ρ g)ᵀ * P * ρ (F.conj g) * ρ (F.conj g)⁻¹ := by
            rw [Matrix.mul_assoc _ (ρ _), ← hm, mul_inv_cancel, h1, Matrix.mul_one]
        _ = _ := by rw [hu, Matrix.smul_mul]
    calc Q * (ρ g * Z * ρ g⁻¹)ᵀ * P = Q * (ρ g⁻¹)ᵀ * Zᵀ * ((ρ g)ᵀ * P) := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = (ρ (F.conj g) * Q) * Zᵀ * (P * ρ (F.conj g)⁻¹) := by
          rw [e1, e2]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  let a0 : F.G₀ → Matrix (Fin n) (Fin n) R →ₗ[A] Matrix (Fin n) (Fin n) R := fun g =>
    { toFun := fun Z => χ g • (ρ g * Z * ρ g⁻¹)
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp [smul_comm c] }
  let a : F.G₀ →* (Matrix (Fin n) (Fin n) R →ₗ[A] Matrix (Fin n) (Fin n) R) :=
    { toFun := a0
      map_one' := LinearMap.ext fun Z => by simp [a0, h1, c1]
      map_mul' := fun g h => LinearMap.ext fun Z => by
        show χ ((g : F.Γ) * h) • (ρ (g * h) * Z * ρ (g * h)⁻¹) =
          χ g • (ρ g * (χ h • (ρ h * Z * ρ h⁻¹)) * ρ g⁻¹)
        rw [_root_.mul_inv_rev, hm, hm, cm]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_smul] }
  let t : Matrix (Fin n) (Fin n) R →ₗ[A] Matrix (Fin n) (Fin n) R :=
    { toFun := fun Z => -(χ F.c • (Q * Zᵀ * P))
      map_add' := fun X Y => by simp [transpose_add, add_comm, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp [smul_comm c] }
  obtain ⟨f, f1, f2⟩ := adEx_ext F a t (LinearMap.ext fun Z => by
      show -(χ F.c • (Q * (-(χ F.c • (Q * Zᵀ * P)))ᵀ * P)) = Z
      have e : Q * (Q * Zᵀ * P)ᵀ * P = Z := by
        calc Q * (Q * Zᵀ * P)ᵀ * P = Q * Pᵀ * Z * (Qᵀ * P) := by
              simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
          _ = Z := by
              rw [hQ, hP]
              simp only [Matrix.mul_smul, Matrix.smul_mul, hQP, Matrix.one_mul, Matrix.mul_one, smul_smul, hs, one_smul]
      rw [transpose_neg, transpose_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, e,
        smul_neg, neg_neg, smul_smul, hcc, one_smul]) (fun g => LinearMap.ext fun Z => by
      show -(χ F.c • (Q * (χ g • (ρ g * Z * ρ g⁻¹))ᵀ * P)) = χ (F.conj g : F.G₀) •
        (ρ (F.conj g) * (-(χ F.c • (Q * Zᵀ * P))) * ρ (F.conj g)⁻¹)
      rw [transpose_smul, Matrix.mul_smul, Matrix.smul_mul, key, hχ]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, smul_neg, smul_smul, mul_comm])
  refine ⟨f, fun g Z => ?_, fun Z => ?_⟩
  · rw [f1]; rfl
  · rw [f2]
    show P * -(χ F.c • (Q * Zᵀ * P)) = _
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]

theorem UpperTheory.V.Th.adExP :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ), (∃ rep, IsAd0 h y m rep) ∧ (∃ rep, IsAd1 h y m rep) ∧ ∀ rep, IsAd0 h y m rep ∨ IsAd1 h y m rep → LC rep := by
  intro l _ L G G0 h O _ _ _ _ _ n y m
  have rmul : ∀ X Y : Matrix (Fin n) (Fin n) O, red m (X * Y) = red m X * red m Y := fun X Y => Matrix.map_mul
  have rone : red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have rtr : ∀ X : Matrix (Fin n) (Fin n) O, (red m X)ᵀ = red m Xᵀ := fun X => rfl
  have rsm : ∀ (u : O) (X : Matrix (Fin n) (Fin n) O), red m (u • X) = Ideal.Quotient.mk (maximalIdeal O ^ m) u • red m X :=
    fun u X => Matrix.ext fun i j => map_mul (Ideal.Quotient.mk (maximalIdeal O ^ m)) u (X i j)
  have h1 : y.ρm h m 1 = 1 := by rw [Pt.ρm, map_one, map_one, rone]
  have hm : ∀ g g' : G.G₀, y.ρm h m (g * g') = y.ρm h m g * y.ρm h m g' := fun g g' => by
    rw [Pt.ρm, map_mul, map_mul, rmul]; rfl
  have hc : ∀ g : G.frame.G₀, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
    intro g
    apply Subtype.ext
    simp [GFrame.conj, Glob.Hom.p₀, h.c]
  have hf : ∀ g : G.G₀, ∃ u : Om O m, (y.ρm h m g)ᵀ * red m y.P * y.ρm h m (G.frame.conj g) = u • red m y.P := fun g =>
    ⟨_, by rw [Pt.ρm, Pt.ρm, hc, rtr, ← rmul, ← rmul, y.form (h.p₀ g), rsm]⟩
  have hPQ : red m (y.P : Matrix (Fin n) (Fin n) O) * red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← rmul, Units.mul_inv, rone]
  have hQP : red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * red m (y.P : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← rmul, Units.inv_mul, rone]
  obtain ⟨s, hs, hP⟩ : ∃ s : Om O m, s * s = 1 ∧ (red m (y.P : Matrix (Fin n) (Fin n) O))ᵀ = s • red m y.P := by
    rcases y.sgn with e | e
    · exact ⟨1, one_mul _, by rw [rtr, e, one_smul]⟩
    · refine ⟨-1, by ring, ?_⟩
      rw [rtr, e, neg_smul, one_smul]
      exact Matrix.map_neg _ (map_neg _) _
  refine ⟨adP_ex G.frame O _ _ _ _ s h1 hm hPQ hQP hs hP hf rfl (fun _ _ => (one_mul _).symm),
    adP_ex G.frame O _ _ _ _ s h1 hm hPQ hQP hs hP hf (by simp [epsm]) (fun _ _ => by simp [epsm]), ?_⟩
  have hp : Continuous fun g : G.G₀ => h.p₀ g :=
    Continuous.subtype_mk (h.cont.comp continuous_subtype_val) _
  have h0 : IsLocallyConstant fun g : G0.G₀ => red m (mat y.ρ g) := lc_mat _ fun i j => y.cont i j m
  have l1 : IsLocallyConstant fun g : G.G₀ => y.ρm h m g := h0.comp_continuous hp
  have l2 : IsLocallyConstant fun g : G.G₀ => y.ρm h m g⁻¹ := l1.comp_continuous continuous_inv
  have main : ∀ (χ : G.Γ → Om O m) (rep : Representation O G.Γ (Mm O n m)), IsLocallyConstant χ →
      IsAdP G.frame (y.ρm h m) (red m y.P) χ rep → LC rep := by
    intro χ rep hχ had
    refine lc_of_open rep G.η.ker G.η_open fun Z => ?_
    have l3 : IsLocallyConstant fun g : G.G₀ => χ g := hχ.comp_continuous continuous_subtype_val
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    filter_upwards [l1.eventually_eq g0, l2.eventually_eq g0, l3.eventually_eq g0] with g e1 e2 e3
    refine (had.1 g Z).trans (Eq.trans ?_ (had.1 g0 Z).symm)
    rw [e1, e2, e3]
  rintro rep (had | had)
  · exact main _ rep (IsLocallyConstant.const _) had
  · refine main _ rep ?_ had
    have hl : (l : Om O m) ^ m = 0 := by
      have := ((omFacts l O).2 m).2.2.1 1
      rwa [nsmul_eq_mul, mul_one, Nat.cast_pow] at this
    have hc : Continuous fun g : G.Γ => (G.ε g : ℤ_[l]) := Units.continuous_val.comp G.ε_cont
    exact (lc_padic ((algebraMap O (Om O m)).comp (algebraMap ℤ_[l] O)) m hl).comp_continuous hc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PairOLin
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem pairO_lin (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (φ : ℤ_[l] →+* R) (k : ℕ)
    (hk : ∀ x : R, l ^ k • x = 0) (τ : R →+ ZMod (l ^ k)) (a : ℤ_[l]) (x : R) :
    τ (φ a * x) = PadicInt.toZModPow k a * τ x := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set n : ℕ := (PadicInt.toZModPow k a).val with hn
  have h1 : a - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hn, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  obtain ⟨b, hb⟩ := h1
  have h2 : a = (n : ℤ_[l]) + (l : ℤ_[l]) ^ k * b := by rw [← hb]; ring
  have h3 : φ a * x = n • x := by
    have := hk (φ b * x)
    rw [nsmul_eq_mul, Nat.cast_pow] at this
    rw [h2, map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_mul, mul_assoc, this, add_zero, nsmul_eq_mul]
  rw [h3, map_nsmul, nsmul_eq_mul, hn, ZMod.natCast_zmod_val]

private theorem pairO_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : Irreducible t)
    (m : ℕ) (x : Om O (m + 1)) (hx : x ≠ 0) : ∃ z, x * z = Ideal.Quotient.mk _ (t ^ m) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy ht
  have hn : n ≤ m := by
    by_contra h
    apply hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_left (pow_dvd_pow t (by omega)) _
  refine ⟨Ideal.Quotient.mk _ ((u⁻¹ : Oˣ) * t ^ (m - n)), ?_⟩
  rw [← map_mul]
  congr 1
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add]
  congr 1
  omega

theorem UpperTheory.V.Th.pairO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (m : ℕ), ∃ (k : ℕ) (τ : Om O m →+ ZMod (l ^ k)), 0 < k ∧ (∀ x, (∀ z, τ (x * z) = 0) → x = 0) ∧ ∀ (a : ℤ_[l]) x, τ (algebraMap O (Om O m) (algebraMap ℤ_[l] O a) * x) = PadicInt.toZModPow k a * τ x := by
  intro l _ O _ _ _ _ _ m
  obtain ⟨hfin, -, hkill, -⟩ := (UpperTheory.V.Th.omFacts l O).2 m
  have hk : ∀ x : Om O m, l ^ (m + 1) • x = 0 := fun x => by
    rw [pow_succ, mul_smul, hkill]
  have main : ∃ τ : Om O m →+ ZMod (l ^ (m + 1)), ∀ x, (∀ z, τ (x * z) = 0) → x = 0 := by
    cases m with
    | zero =>
      refine ⟨0, fun x _ => ?_⟩
      simpa using hkill x
    | succ m =>
      obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible O
      haveI : NeZero (l ^ (m + 1 + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      letI : Module (ZMod (l ^ (m + 1 + 1))) (Om O (m + 1)) := AddCommGroup.zmodModule hk
      have h0 : (Ideal.Quotient.mk _ (t ^ m) : Om O (m + 1)) ≠ 0 := by
        rw [Ne, Ideal.Quotient.eq_zero_iff_mem, ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
          pow_dvd_pow_iff ht.ne_zero ht.not_isUnit]
        omega
      have h1 := (UpperTheory.V.Th.dualZ (l ^ (m + 1 + 1)) (Om O (m + 1))).2.1 (Ideal.Quotient.mk _ (t ^ m))
      obtain ⟨f, hf⟩ := not_forall.mp (mt h1 h0)
      refine ⟨f.toAddMonoidHom, fun x hx => ?_⟩
      by_contra hx0
      obtain ⟨z, hz⟩ := pairO_dvd O t ht m x hx0
      have := hx z
      rw [hz] at this
      exact hf this
  obtain ⟨τ, hτ⟩ := main
  exact ⟨m + 1, τ, Nat.succ_pos m, hτ, fun a x =>
    pairO_lin l (Om O m) ((algebraMap O (Om O m)).comp (algebraMap ℤ_[l] O)) (m + 1) hk τ a x⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.BorCard
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem card_lt' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
  rw [Fintype.card_subtype]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  simpa using this

private theorem card_le' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 ≤ p.2} = n + n.choose 2 := by
  rw [← card_lt' n]
  have e : {p : Fin n × Fin n // p.1 ≤ p.2} ≃ Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2} :=
    { toFun := fun p => if h : p.1.1 < p.1.2 then .inr ⟨p.1, h⟩ else .inl p.1.1
      invFun := Sum.elim (fun i => ⟨(i, i), le_rfl⟩) fun p => ⟨p.1, p.2.le⟩
      left_inv := fun p => by
        by_cases h : p.1.1 < p.1.2
        · simp [h]
        · simp only [h, dite_false, Sum.elim_inl]
          exact Subtype.ext (Prod.ext rfl (le_antisymm p.2 (not_lt.1 h)))
      right_inv := by
        rintro (i | p)
        · simp
        · simp [p.2] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) : red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

private theorem card_up (X : Type) [Zero X] (n : ℕ) :
    Nat.card {Z : Matrix (Fin n) (Fin n) X // ∀ i j, j < i → Z i j = 0} = Nat.card X ^ (n + n.choose 2) := by
  rw [← card_le', ← Nat.card_eq_fintype_card, ← Nat.card_fun]
  exact Nat.card_congr
    { toFun := fun Z p => Z.1 p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0, fun i j h => by simp [not_le.2 h]⟩
      left_inv := fun Z => Subtype.ext (Matrix.ext fun i j => by
        by_cases h : i ≤ j
        · simp [h]
        · simp [h, Z.2 i j (not_le.1 h)])
      right_inv := fun f => funext fun p => by simp [p.2] }

theorem UpperTheory.V.Th.borCard :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (v : L.Vl), Nat.card (bor y m v) = Nat.card (ResidueField O) ^ (m * (n + n.choose 2)) := by
  intro l _ L G0 O _ _ _ _ _ n y m v
  have i1 : red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * red m (y.w v : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← red_mul, Units.inv_mul, red_one]
  have i2 : red m (y.w v : Matrix (Fin n) (Fin n) O) * red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← red_mul, Units.mul_inv, red_one]
  rw [pow_mul, ← ((omFacts l O).2 m).2.1, ← card_up]
  generalize hw : red m (y.w v : Matrix (Fin n) (Fin n) O) = w at i1 i2
  generalize hwi : red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = wi at i1 i2
  have hm : ∀ Z, Z ∈ bor y m v ↔ ∀ i j, j < i → (wi * Z * w) i j = 0 := fun Z => by rw [← hw, ← hwi]; rfl
  exact Nat.card_congr
    { toFun := fun Z => ⟨wi * Z.1 * w, (hm _).1 Z.2⟩
      invFun := fun U => ⟨w * U.1 * wi, (hm _).2 (by
        rw [← mul_assoc, ← mul_assoc, i1, one_mul, mul_assoc, i1, mul_one]; exact U.2)⟩
      left_inv := fun Z => Subtype.ext (by
        show w * (wi * Z.1 * w) * wi = Z.1
        rw [← mul_assoc, ← mul_assoc, i2, one_mul, mul_assoc, i2, mul_one])
      right_inv := fun U => Subtype.ext (by
        show wi * (w * U.1 * wi) * w = U.1
        rw [← mul_assoc, ← mul_assoc, i1, one_mul, mul_assoc, i1, mul_one]) }
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedSmul
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B := by
  ext i j
  simp [red]

private theorem red_smul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (a : O) (A : Matrix (Fin n) (Fin n) O) :
    red m (a • A) = algebraMap O (Om O m) a • red m A := by
  ext i j
  simp [red]

theorem UpperTheory.V.Th.h0v0O :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (D : Subgroup G0.G₀), y.N4 D → ∃ C : ℕ, ∀ m, {Y : Mm O n m | ∀ g ∈ D, epsm O G0 m (g : G0.G₀) • (y.ρ0 m g * Y * y.ρ0 m g⁻¹) = Y}.ncard ≤ Nat.card (ResidueField O) ^ C := by
  intro l _ L G0 O _ _ _ _ _ n y D hN
  let M : G0.G₀ → Matrix (Fin n) (Fin n) O := fun g => mat y.ρ g
  let e : G0.G₀ → O := fun g => algebraMap ℤ_[l] O (G0.ε (g : G0.Γ))
  let Φ : D → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O := fun s =>
    e s • LinearMap.mulLeft O (M s) - LinearMap.mulRight O (M s)
  have hΦ : ∀ s Z, Φ s Z = e s • (M s * Z) - Z * M s := fun s Z => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n D Φ
  have hker : (⨅ s, (Φ s).ker) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_iInf] at hZ
    rw [Submodule.mem_bot]
    apply hN Z
    intro g hg
    have h1 := hZ ⟨g, hg⟩
    rw [LinearMap.mem_ker, hΦ, sub_eq_zero] at h1
    exact h1
  have hfin : Module.finrank O ↥(⨅ s, (Φ s).ker) = 0 := by
    rw [hker]
    exact finrank_bot O _
  refine ⟨C, fun m => ?_⟩
  have hone : red m (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    unfold red
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hinv : ∀ g : G0.G₀, y.ρ0 m g * y.ρ0 m g⁻¹ = 1 ∧ y.ρ0 m g⁻¹ * y.ρ0 m g = 1 := by
    intro g
    simp only [Pt.ρ0, ← red_mul', ← map_mul, mul_inv_cancel, inv_mul_cancel, map_one, hone, and_self]
  have hred : ∀ (g : G0.G₀) (Z : Matrix (Fin n) (Fin n) O),
      red m (e g • (M g * Z) - Z * M g) = epsm O G0 m g • (y.ρ0 m g * red m Z) - red m Z * y.ρ0 m g := by
    intro g Z
    rw [red_sub', red_smul', red_mul', red_mul']
    rfl
  have hset : {Y : Mm O n m | ∀ g ∈ D, epsm O G0 m (g : G0.G₀) • (y.ρ0 m g * Y * y.ρ0 m g⁻¹) = Y} =
      {Y : Mm O n m | ∃ Y' : Matrix (Fin n) (Fin n) O, red m Y' = Y ∧ ∀ s, red m (Φ s Y') = 0} := by
    ext Y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨Y.map (Function.surjInv Ideal.Quotient.mk_surjective), ?_, fun s => ?_⟩
      · ext i j
        simp [red, Function.surjInv_eq]
      · have hY : red m (Y.map (Function.surjInv Ideal.Quotient.mk_surjective)) = Y := by
          ext i j
          simp [red, Function.surjInv_eq]
        rw [hΦ, hred, hY, sub_eq_zero]
        have h1 := h s s.2
        calc epsm O G0 m (s : G0.G₀) • (y.ρ0 m s * Y)
            = (epsm O G0 m (s : G0.G₀) • (y.ρ0 m s * Y * y.ρ0 m (s : G0.G₀)⁻¹)) * y.ρ0 m s := by
              rw [Matrix.smul_mul, mul_assoc (y.ρ0 m s * Y), (hinv s).2, mul_one]
          _ = Y * y.ρ0 m s := by rw [h1]
    · rintro ⟨Y', rfl, h⟩ g hg
      have h1 := h ⟨g, hg⟩
      rw [hΦ, hred, sub_eq_zero] at h1
      calc epsm O G0 m g • (y.ρ0 m g * red m Y' * y.ρ0 m g⁻¹)
          = (epsm O G0 m g • (y.ρ0 m g * red m Y')) * y.ρ0 m g⁻¹ := by rw [Matrix.smul_mul]
        _ = red m Y' * y.ρ0 m g * y.ρ0 m g⁻¹ := by rw [h1]
        _ = red m Y' := by rw [mul_assoc, (hinv g).1, mul_one]
  rw [hset]
  have h2 := hC m
  rw [hfin, mul_zero, zero_add] at h2
  exact h2
end

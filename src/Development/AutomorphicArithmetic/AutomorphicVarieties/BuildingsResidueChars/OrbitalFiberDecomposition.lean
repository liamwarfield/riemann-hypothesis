module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDecomposition
open MulAction

private theorem fib_abs {O I : Type} {P : I → Type} (F : ∀ i, P i → O) (S : ∀ i, Set (P i)) (B : Set O) (hB : B.Finite)
    (w : O → ℂ) (wi : ∀ i, P i → ℂ) (hw : ∀ o, o ∉ B → w o = 0) (hwi : ∀ i p, p ∉ S i → wi i p = 0)
    (hF : ∀ i, ∀ p ∈ S i, F i p ∈ B ∧ wi i p = w (F i p)) (hs : ∀ o ∈ B, ∃ i, ∃ p ∈ S i, F i p = o)
    (hij : ∀ i j, ∀ p ∈ S i, ∀ q ∈ S j, F i p = F j q → i = j) (hinj : ∀ i, Set.InjOn (F i) (S i)) :
    ∑ᶠ o, w o = ∑ᶠ i, ∑ᶠ p, wi i p := by
  classical
  have h1 : ∀ i, ∑ᶠ p, wi i p = ∑ᶠ o ∈ F i '' S i, w o := by
    intro i
    rw [finsum_mem_image (hinj i), finsum_mem_def]
    congr 1
    funext p
    by_cases hp : p ∈ S i
    · rw [Set.indicator_of_mem hp, (hF i p hp).2]
    · rw [Set.indicator_of_notMem hp, hwi i p hp]
  have hsub : ∀ i, F i '' S i ⊆ B := by
    rintro i _ ⟨p, hp, rfl⟩
    exact (hF i p hp).1
  have hI : {i | (S i).Nonempty}.Finite := by
    let g : {i | (S i).Nonempty} → B := fun i => ⟨F i.1 i.2.some, (hF _ _ i.2.some_mem).1⟩
    have hg : Function.Injective g := fun i j h =>
      Subtype.ext (hij _ _ _ i.2.some_mem _ j.2.some_mem (congrArg Subtype.val h))
    haveI := hB.to_subtype
    exact Set.finite_coe_iff.1 (Finite.of_injective g hg)
  have hU : B = ⋃ i ∈ {i | (S i).Nonempty}, F i '' S i := by
    ext o
    simp only [Set.mem_iUnion]
    constructor
    · intro ho
      obtain ⟨i, p, hp, rfl⟩ := hs o ho
      exact ⟨i, ⟨p, hp⟩, p, hp, rfl⟩
    · rintro ⟨i, _, ho⟩
      exact hsub i ho
  have h2 : ∑ᶠ o, w o = ∑ᶠ o ∈ B, w o := by
    rw [finsum_mem_def]
    congr 1
    funext o
    by_cases ho : o ∈ B
    · rw [Set.indicator_of_mem ho]
    · rw [Set.indicator_of_notMem ho, hw o ho]
  rw [h2, hU, finsum_mem_biUnion _ hI (fun i _ => hB.subset (hsub i)), finsum_mem_def]
  · congr 1
    funext i
    by_cases hi : i ∈ {i | (S i).Nonempty}
    · rw [Set.indicator_of_mem hi, h1]
    · rw [Set.indicator_of_notMem hi, h1]
      have : S i = ∅ := Set.not_nonempty_iff_eq_empty.1 hi
      rw [this, Set.image_empty, finsum_mem_empty]
  · intro i _ j _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, h⟩
    exact hne (hij i j p hp q hq h.symm)

private theorem rel_smul {H X : Type} [Group H] [MulAction H X] (H₀ : Subgroup H) (hn : H₀.Normal) (h : H) (x : X) :
    H₀.relIndex (stabilizer H (h • x)) = H₀.relIndex (stabilizer H x) := by
  have h0 : H₀.map (MulAut.conj h).toMonoidHom = H₀ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hn.conj_mem y hy h
    · intro hz
      refine ⟨h⁻¹ * z * h, ?_, ?_⟩
      · simpa using hn.conj_mem z hz h⁻¹
      · simp [mul_assoc]
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← h0]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective

private theorem out_mk {H X : Type} [Group H] [MulAction H X] (x : X) :
    ∃ h : H, (Quotient.mk (orbitRel H X) x).out = h • x := by
  have : (Quotient.mk (orbitRel H X) x).out ∈ orbit H x :=
    orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel H X) x)))
  obtain ⟨h, hh⟩ := this
  exact ⟨h, hh.symm⟩

private theorem mk_smul {H X : Type} [Group H] [MulAction H X] (h : H) (x : X) :
    Quotient.mk (orbitRel H X) (h • x) = Quotient.mk (orbitRel H X) x :=
  Quotient.sound (orbitRel_apply.2 ⟨h, rfl⟩)

theorem UpperTheory.orbitalFiber_decomposition :
    UpperTheory.V.Z.Sym.Glob.Fib.Decomp := by
  intro H X I _ _ H₀ k Hi Yi _ _ φ e ki hn hk hT he hinj hki hke hs hu
  unfold UpperTheory.V.Z.Sym.gq
  have hex : ∀ x x' : X, Quotient.mk (orbitRel H X) x' = Quotient.mk (orbitRel H X) x → ∃ h : H, h • x = x' :=
    fun x x' h => orbitRel_apply.1 (Quotient.exact h)
  refine fib_abs (fun i (p : orbitRel.Quotient (Hi i) (Yi i)) => (Quotient.mk (orbitRel H X) (e i p.out) : orbitRel.Quotient H X))
    (fun i => {p | ki i p.out ≠ 0}) {o | k o.out ≠ 0} ?_ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨T, hT⟩ := hT
    refine (T.finite_toSet.image (Quotient.mk (orbitRel H X))).subset fun o ho => ?_
    obtain ⟨h, s, hs, ho⟩ := hT _ ho
    refine ⟨s, hs, ?_⟩
    rw [← mk_smul h s, ← ho]
    exact Quotient.out_eq o
  · intro o ho
    have : k o.out = 0 := not_not.1 ho
    rw [this, zero_div]
  · intro i p hp
    have : ki i p.out = 0 := not_not.1 hp
    rw [this, zero_div]
  · intro i p hp
    have hp' : ki i p.out ≠ 0 := hp
    obtain ⟨h, hh⟩ := out_mk (H := H) (e i p.out)
    have hv : k (Quotient.mk (orbitRel H X) (e i p.out)).out = ki i p.out := by rw [hh, hk, hke i _ hp']
    refine ⟨fun h0 => hp' (hv ▸ h0), ?_⟩
    have hst : (stabilizer (Hi i) p.out).map (φ i) = stabilizer H (e i p.out) := by
      ext g
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [mem_stabilizer_iff, ← he, mem_stabilizer_iff.1 ha]
      · intro hg
        obtain ⟨_, a, rfl⟩ := hu i i _ _ g hp' hp' hg
        refine ⟨a, hinj i ?_, rfl⟩
        rw [he]
        exact hg
    show _ = k (Quotient.mk (orbitRel H X) (e i p.out)).out /
      (H₀.relIndex (stabilizer H (Quotient.mk (orbitRel H X) (e i p.out)).out) : ℂ)
    rw [hv, hh, rel_smul H₀ hn, Subgroup.relIndex_comap, hst]
  · intro o ho
    obtain ⟨i, y, h, hy, hx⟩ := hs _ ho
    obtain ⟨a, ha⟩ := out_mk (H := Hi i) y
    refine ⟨i, Quotient.mk (orbitRel (Hi i) (Yi i)) y, ?_, ?_⟩
    · show ki i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out ≠ 0
      rwa [ha, hki]
    · show Quotient.mk (orbitRel H X) (e i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out) = o
      rw [ha, he, mk_smul, ← mk_smul h, ← hx]
      exact Quotient.out_eq o
  · intro i j p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ hpq.symm
    exact (hu i j _ _ h hp hq hh).1
  · intro i p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ (Eq.symm hpq)
    obtain ⟨_, a, rfl⟩ := hu i i _ _ h hp hq hh
    rw [← he] at hh
    have h3 := hinj i hh
    rw [← Quotient.out_eq p, ← Quotient.out_eq q, ← h3]
    exact (mk_smul a _).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberOfBot
open MulAction in
theorem UpperTheory.orbitalFiber_of_bot :
    UpperTheory.V.Z.Sym.Glob.Fib.Bot := by
  intro H Y _ _ H₀ k
  have hmul : ∀ (a : ℂ) (g : orbitRel.Quotient H Y → ℂ), ∑ᶠ o, a * g o = a * ∑ᶠ o, g o :=
    fun a g => by simpa only [smul_eq_mul] using (smul_finsum a g).symm
  refine ⟨fun a => ?_, fun hc htriv => ?_⟩
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    exact finsum_congr fun o => mul_div_assoc _ _ _
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    refine finsum_congr fun o => ?_
    have hle : H₀ ≤ stabilizer H o.out := fun z hz => htriv z hz _
    have h := Subgroup.relIndex_mul_relIndex ⊥ H₀ (stabilizer H o.out) bot_le hle
    rw [Subgroup.relIndex_bot_left] at h
    have hc' : (Nat.card H₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
    rw [← h, Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hc']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompactTorusUnitsEqTopOfNonsplit
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem int_of_norm_one {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] {Δ τ : K} (h : IsLoc O Δ) (hτ : ¬ IsSquare (τ ^ 2 - 4)) (e : Etau K τ)
    (hn : QuadraticAlgebra.norm e = 1) : IsIntegral O e := by
  classical
  haveI := h.frac
  have hN : e.re * e.re + τ * e.re * e.im - (-1) * e.im * e.im = 1 := by
    have h' := hn
    rw [QuadraticAlgebra.norm_def] at h'
    exact h'
  by_cases hq : e.im = 0
  · have hp : (e.re - 1) * (e.re + 1) = 0 := by
      rw [hq] at hN
      linear_combination hN
    rcases mul_eq_zero.mp hp with h1 | h1
    · have he : e = 1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one
    · have he : e = -1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one.neg
  · have h2K : (2 : K) ≠ 0 := by
      have h2 := h.two.map (algebraMap O K)
      rw [map_ofNat] at h2
      exact h2.ne_zero
    have nz : ∀ x y : K, y ≠ 0 → x * x + τ * x * y + y * y ≠ 0 := by
      intro x y hy hxy
      apply hτ
      refine ⟨2 * x / y + τ, ?_⟩
      field_simp
      linear_combination (-4) * hxy
    obtain ⟨t, ht⟩ : ∃ t : O, algebraMap O K t = QuadraticAlgebra.trace e := by
      by_contra hne
      push_neg at hne
      have hTd : QuadraticAlgebra.trace e = 2 * e.re + τ * e.im := QuadraticAlgebra.trace_def e
      set T := QuadraticAlgebra.trace e with hTdef
      have hT0 : T ≠ 0 := fun h0 => hne 0 (by rw [map_zero, h0])
      rcases ValuationRing.isInteger_or_isInteger O T with ⟨t, ht⟩ | ⟨s, hs⟩
      · exact hne t ht
      · have hsm : s ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hu
          obtain ⟨u, rfl⟩ := hu
          apply hne (↑u⁻¹)
          rw [map_units_inv, hs, inv_inv]
        obtain ⟨r, hr, -⟩ := sqrtO O K Δ h (1 - 4 * s ^ 2) 1 isUnit_one (by
          have e' : (1 - 4 * s ^ 2) - 1 ^ 2 = s * (-(4 * s)) := by ring
          rw [e']
          exact Ideal.mul_mem_right _ _ hsm)
        have hTS : T * algebraMap O K s = 1 := by
          rw [hs]
          exact mul_inv_cancel₀ hT0
        have hR : (algebraMap O K r) ^ 2 = 1 - 4 * (algebraMap O K s) ^ 2 := by
          rw [← map_pow, hr, map_sub, map_one, map_mul, map_pow, map_ofNat]
        apply nz (-τ * e.im - T * algebraMap O K r) (2 * e.im) (mul_ne_zero h2K hq)
        linear_combination T ^ 2 * hR - 4 * (T * algebraMap O K s + 1) * hTS + 4 * hN +
          (T + 2 * e.re + τ * e.im) * hTd
    exact isIntegral_of_trace_norm t 1 ht.symm (by rw [hn, map_one])

private theorem norm_quo {K : Type} [Field K] {τ : K} (z : (Etau K τ)ˣ) : QuadraticAlgebra.norm (quo z) = 1 := by
  simp only [quo, map_mul, QuadraticAlgebra.norm_star]
  rw [← map_mul, Units.mul_inv, map_one]

theorem UpperTheory.compactTorusUnits_eq_top_of_nonsplit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ¬ IsSquare (τ ^ 2 - 4) → Cint O τ = ⊤ := by
  intro O K _ _ _ _ _ Δ τ h _ hτ
  rw [eq_top_iff]
  intro z _
  exact ⟨int_of_norm_one h hτ _ (norm_quo z), int_of_norm_one h hτ _ (norm_quo z⁻¹)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsLatticeIffFixedPointQuadraticTorus
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem im_form {K : Type} [Field K] {τ : K} (x y : Etau K τ) :
    (x * star y).im = x.im * y.re - x.re * y.im := by
  simp; ring

private theorem smul_im' {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (r : O)
    (x : Etau K τ) : (r • x).im = algebraMap O K r * x.im := by
  rw [QuadraticAlgebra.im_smul, Algebra.smul_def]

private theorem smul_re' {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (r : O)
    (x : Etau K τ) : (r • x).re = algebraMap O K r * x.re := by
  rw [QuadraticAlgebra.re_smul, Algebra.smul_def]

private theorem fix_lat {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {τ t : K} {S : Set (Etau K τ)} (h : IsFixP O τ t S) : IsLat O τ S := by
  classical
  obtain ⟨s, hs⟩ := h.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (s.image (fun x : Etau K τ => t * x.im) ∪ s.image (fun x : Etau K τ => t * x.re))
  set B : K := algebraMap O K (b : O) with hBdef
  have hB : B ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have key : ∀ x ∈ Submodule.span O (s : Set (Etau K τ)),
      t * x.im * B ∈ (algebraMap O K).range ∧ t * x.re * B ∈ (algebraMap O K).range := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r1, hr1⟩ := hb (t * x.im) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
      obtain ⟨r2, hr2⟩ := hb (t * x.re) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
      refine ⟨⟨r1, ?_⟩, ⟨r2, ?_⟩⟩
      · rw [hr1, Algebra.smul_def, hBdef]
        ring
      · rw [hr2, Algebra.smul_def, hBdef]
        ring
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · have e := add_mem hx.1 hy.1
        convert e using 1
        simp only [QuadraticAlgebra.im_add]
        ring
      · have e := add_mem hx.2 hy.2
        convert e using 1
        simp only [QuadraticAlgebra.re_add]
        ring
    | smul r x _ hx =>
      rw [smul_im', smul_re']
      refine ⟨?_, ?_⟩
      · have e := mul_mem (RingHom.mem_range_self (algebraMap O K) r) hx.1
        convert e using 1
        ring
      · have e := mul_mem (RingHom.mem_range_self (algebraMap O K) r) hx.2
        convert e using 1
        ring
  have m1 : B • (1 : Etau K τ) ∈ S := by
    rw [h.dual]
    intro x hx
    rw [hs] at hx
    have e : (x * star (B • (1 : Etau K τ))).im = x.im * B := by
      rw [im_form]
      simp
    rw [e, ← mul_assoc]
    exact (key x hx).1
  have m2 : B • (ω : Etau K τ) ∈ S := by
    rw [h.dual]
    intro x hx
    rw [hs] at hx
    have e : (x * star (B • (ω : Etau K τ))).im = -(x.re * B) := by
      rw [im_form]
      simp
    rw [e, mul_neg, ← mul_assoc]
    exact neg_mem (key x hx).2
  refine ⟨h.fg, ?_⟩
  rw [eq_top_iff]
  intro y _
  have e : y = (y.re / B) • (B • (1 : Etau K τ)) + (y.im / B) • (B • (ω : Etau K τ)) := by
    ext <;> simp <;> field_simp
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span m1))
    (Submodule.smul_mem _ _ (Submodule.subset_span m2))

private theorem dual_pair {O K : Type} [CommRing O] [Field K] [Algebra O K]
    {τ : K} (u v : Etau K τ) (hd : u.im * v.re - u.re * v.im ≠ 0) (y : Etau K τ) :
    y ∈ (Submodule.span O {u, v} : Submodule O (Etau K τ)) ↔
      ∀ x ∈ (Submodule.span O {u, v} : Submodule O (Etau K τ)),
        (u.im * v.re - u.re * v.im)⁻¹ * (x * star y).im ∈ (algebraMap O K).range := by
  constructor
  · intro hy x hx
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.1 hy
    obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.1 hx
    refine ⟨p * s - q * r, ?_⟩
    rw [im_form]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, smul_im', smul_re',
      map_sub, map_mul]
    field_simp
    ring
  · intro H
    obtain ⟨β, hβ⟩ := H u (Submodule.subset_span (by simp))
    obtain ⟨α, hα⟩ := H v (Submodule.subset_span (by simp))
    rw [im_form] at hα hβ
    refine Submodule.mem_span_pair.2 ⟨-α, β, ?_⟩
    ext
    · simp only [QuadraticAlgebra.re_add, smul_re', map_neg, hα, hβ]
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_add, smul_im', map_neg, hα, hβ]
      field_simp
      ring

theorem UpperTheory.isLattice_iff_fixedPoint_quadraticTorus :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ S : Set (Etau K τ), (∀ t : K, IsFixP O τ t S → IsLat O τ S) ∧ (IsLat O τ S → (∀ y ∈ S, ω * y ∈ S) → ∃ t : K, t ≠ 0 ∧ IsFixP O τ t S) := by
  intro O K _ _ _ _ _ Δ τ hL hτ S
  haveI := hL.frac
  refine ⟨fun t h => fix_lat h, fun hS hst => ?_⟩
  obtain ⟨y, x, hx, -, -, e⟩ := latCls O K Δ τ hL hτ S hS
  have e' : S = (Submodule.span O {(y : Etau K τ), (y : Etau K τ) * x} : Submodule O (Etau K τ)) := by
    rw [e]
    ext w
    simp only [SetLike.mem_coe, Submodule.mem_span_pair, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨p, q, rfl⟩, rfl⟩
      exact ⟨p, q, by simp [mul_add]⟩
    · rintro ⟨p, q, rfl⟩
      exact ⟨_, ⟨p, q, rfl⟩, by simp [mul_add]⟩
  have hn : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := (isUnit_iff_norm_isUnit.1 y.isUnit).ne_zero
  have hd : (y : Etau K τ).im * ((y : Etau K τ) * x).re - (y : Etau K τ).re * ((y : Etau K τ) * x).im ≠ 0 := by
    have : (y : Etau K τ).im * ((y : Etau K τ) * x).re - (y : Etau K τ).re * ((y : Etau K τ) * x).im =
        -(QuadraticAlgebra.norm (y : Etau K τ) * x.im) := by
      simp [norm_def]; ring
    rw [this]
    exact neg_ne_zero.2 (mul_ne_zero hn hx)
  refine ⟨_, inv_ne_zero hd, hS.fg, fun w => ?_, hst⟩
  rw [e']
  exact dual_pair _ _ hd w
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EvenValuationNormCompactUnitsOfSplit
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {τ r r' : K}

private def phiK (τ r : K) (h : r * r = -1 + τ * r) : Etau K τ →ₐ[K] K where
  toFun x := x.re + x.im * r
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination (-(x.im * y.im)) * h
  map_zero' := by simp
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]; ring
  commutes' a := by
    simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, zero_mul,
      add_zero, Algebra.algebraMap_self_apply]

private lemma phiK_apply (h : r * r = -1 + τ * r) (x : Etau K τ) : phiK τ r h x = x.re + x.im * r := rfl

private lemma phiK_star (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (x : Etau K τ) :
    phiK τ r h (star x) = phiK τ r' h' x := by
  simp only [phiK_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  linear_combination (-x.im) * hs

private lemma phiK_norm (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (hp : r * r' = 1)
    (x : Etau K τ) : QuadraticAlgebra.norm x = phiK τ r h x * phiK τ r' h' x := by
  simp only [phiK_apply, QuadraticAlgebra.norm_def]
  linear_combination (-(x.re * x.im)) * hs - x.im ^ 2 * hp

private lemma phiK_ne (h : r * r = -1 + τ * r) (x : (Etau K τ)ˣ) : phiK τ r h (x : Etau K τ) ≠ 0 :=
  (x.isUnit.map (phiK τ r h)).ne_zero

private lemma phiK_inv (h : r * r = -1 + τ * r) (x : (Etau K τ)ˣ) :
    phiK τ r h ((x⁻¹ : (Etau K τ)ˣ) : Etau K τ) = (phiK τ r h (x : Etau K τ))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, Units.inv_mul, map_one]

private lemma phiK_quo (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (x : (Etau K τ)ˣ) :
    phiK τ r h (quo x) = phiK τ r h (x : Etau K τ) * (phiK τ r' h' (x : Etau K τ))⁻¹ := by
  rw [quo, map_mul, phiK_star h h' hs, phiK_inv]

private lemma phiK_inj (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') :
    Function.Injective ((phiK τ r h).prod (phiK τ r' h')) := by
  intro x y hxy
  have h1 : x.re + x.im * r = y.re + y.im * r := congrArg Prod.fst hxy
  have h2 : x.re + x.im * r' = y.re + y.im * r' := congrArg Prod.snd hxy
  have h3 : x.im = y.im := by
    have : (x.im - y.im) * (r - r') = 0 := by linear_combination h1 - h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne))
  ext
  · rw [h3] at h1; exact add_right_cancel h1
  · exact h3

private lemma phiK_surj (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (a b : K) :
    ∃ x : Etau K τ, phiK τ r h x = a ∧ phiK τ r' h' x = b := by
  have := sub_ne_zero.2 hne
  refine ⟨⟨a - (a - b) / (r - r') * r, (a - b) / (r - r')⟩, ?_, ?_⟩
  · simp [phiK_apply]
  · simp only [phiK_apply]; field_simp; ring

private lemma phiK_surjU (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x : (Etau K τ)ˣ, phiK τ r h x = a ∧ phiK τ r' h' x = b := by
  obtain ⟨x, hx1, hx2⟩ := phiK_surj h h' hne a b
  obtain ⟨y, hy1, hy2⟩ := phiK_surj h h' hne a⁻¹ b⁻¹
  have hxy : x * y = 1 := by
    apply phiK_inj h h' hne
    refine Prod.ext ?_ ?_
    · simp only [AlgHom.prod_apply, map_mul, map_one, hx1, hy1]
      exact mul_inv_cancel₀ ha
    · simp only [AlgHom.prod_apply, map_mul, map_one, hx2, hy2]
      exact mul_inv_cancel₀ hb
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, hx1, hx2⟩

private lemma phiK_int (O : Type) [CommRing O] [Algebra O K]
    (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (x : Etau K τ) :
    IsIntegral O x ↔ IsIntegral O (phiK τ r h x) ∧ IsIntegral O (phiK τ r' h' x) := by
  constructor
  · intro hx
    exact ⟨hx.map ((phiK τ r h).restrictScalars O), hx.map ((phiK τ r' h').restrictScalars O)⟩
  · rintro ⟨ha, hb⟩
    set a := phiK τ r h x
    set b := phiK τ r' h' x
    let f : K →ₐ[O] Etau K τ := IsScalarTower.toAlgHom O K (Etau K τ)
    have ha' : IsIntegral O (algebraMap K (Etau K τ) a) := ha.map f
    have hb' : IsIntegral O (algebraMap K (Etau K τ) b) := hb.map f
    have hroot : (x - algebraMap K (Etau K τ) a) * (x - algebraMap K (Etau K τ) b) = 0 := by
      apply phiK_inj h h' hne
      refine Prod.ext ?_ ?_
      · simp only [AlgHom.prod_apply, map_mul, map_sub, AlgHom.commutes, map_zero, Prod.fst_zero]
        simp [a]
      · simp only [AlgHom.prod_apply, map_mul, map_sub, AlgHom.commutes, map_zero, Prod.snd_zero]
        simp [b]
    let C := integralClosure O (Etau K τ)
    have hxC : IsIntegral C x := by
      refine ⟨(Polynomial.X - Polynomial.C (⟨_, ha'⟩ : C)) * (Polynomial.X - Polynomial.C (⟨_, hb'⟩ : C)),
        (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _), ?_⟩
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
      exact hroot
    exact isIntegral_trans x hxC

end SlopeTestRemainingChoices

theorem UpperTheory.evenValuation_norm_compactUnits_of_split :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → IsSquare (τ ^ 2 - 4) → (∀ c ∈ Cint O τ, EvenVal O (QuadraticAlgebra.norm ((c : (Etau K τ)ˣ) : Etau K τ))) ∧ ∀ y : (Etau K τ)ˣ, EvenVal O (QuadraticAlgebra.norm (y : Etau K τ)) → ∃ z : (Etau K τ)ˣ, ∃ c ∈ Cint O τ, y = c * z ^ 2 := by
  intro O K _ _ _ _ _ Δ τ hL hτ hsq
  haveI := hL.frac
  have h2 : (2 : K) ≠ 0 := by
    have e := (hL.two).map (algebraMap O K)
    rw [map_ofNat] at e
    exact e.ne_zero
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hs, mul_zero]
  set r : K := (τ + s) / 2 with hrE
  set r' : K := (τ - s) / 2 with hr'E
  have hr : r * r = -1 + τ * r := by
    rw [hrE]
    field_simp
    linear_combination (-1 : K) * hs
  have hr' : r' * r' = -1 + τ * r' := by
    rw [hr'E]
    field_simp
    linear_combination (-1 : K) * hs
  have hsum : r + r' = τ := by
    rw [hrE, hr'E]
    field_simp
    ring
  have hsum' : r' + r = τ := by rw [add_comm]; exact hsum
  have hprod : r * r' = 1 := by
    rw [hrE, hr'E]
    field_simp
    linear_combination hs
  have hne : r ≠ r' := by
    intro e
    apply hs0
    have e2 : r - r' = s := by
      rw [hrE, hr'E]
      field_simp
      ring
    rw [← e2, e, sub_self]
  have hint : ∀ v : K, (∃ w : O, algebraMap O K w = v) → IsIntegral O v := by
    rintro v ⟨w, rfl⟩
    exact isIntegral_algebraMap
  have huv : ∀ (u : Oˣ) (v : K), v = algebraMap O K (u : O) → IsIntegral O v ∧ IsIntegral O v⁻¹ := by
    intro u v hv
    refine ⟨hint v ⟨u, hv.symm⟩, hint v⁻¹ ⟨(u⁻¹ : Oˣ), ?_⟩⟩
    rw [hv, map_units_inv]
  have hcint : ∀ (c : (Etau K τ)ˣ) (u : Oˣ),
      phiK τ r hr (c : Etau K τ) * (phiK τ r' hr' (c : Etau K τ))⁻¹ = algebraMap O K (u : O) →
      c ∈ Cint O τ := by
    intro c u hu
    obtain ⟨i1, i2⟩ := huv u _ hu
    have e2 : phiK τ r' hr' (c : Etau K τ) * (phiK τ r hr (c : Etau K τ))⁻¹
        = (phiK τ r hr (c : Etau K τ) * (phiK τ r' hr' (c : Etau K τ))⁻¹)⁻¹ := by
      rw [mul_inv, inv_inv, mul_comm]
    refine ⟨?_, ?_⟩
    · rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum', e2]
      exact ⟨i1, i2⟩
    · rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum', phiK_inv, phiK_inv,
        inv_inv, inv_inv]
      refine ⟨?_, ?_⟩
      · rw [mul_comm, e2]
        exact i2
      · rw [mul_comm]
        exact i1
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨hc1, -⟩ := hc
    rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum'] at hc1
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc1.1
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc1.2
    have hA := phiK_ne hr c
    have hB := phiK_ne hr' c
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one]
      field_simp
    refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, phiK τ r' hr' (c : Etau K τ), hB, ?_⟩
    rw [phiK_norm hr hr' hsum hprod, Units.val_mk, ha]
    field_simp
  · rintro y ⟨u, t, ht, hy⟩
    have hA := phiK_ne hr y
    have hB := phiK_ne hr' y
    obtain ⟨z, hz1, hz2⟩ := phiK_surjU hr hr' hne 1 (phiK τ r' hr' (y : Etau K τ) / t) one_ne_zero
      (div_ne_zero hB ht)
    refine ⟨z, y * (z ^ 2)⁻¹, ?_, (inv_mul_cancel_right y (z ^ 2)).symm⟩
    apply hcint _ u
    rw [Units.val_mul, map_mul, map_mul, phiK_inv, phiK_inv, Units.val_pow_eq_pow_val, map_pow,
      map_pow, hz1, hz2]
    have hn := phiK_norm hr hr' hsum hprod (y : Etau K τ)
    rw [hy] at hn
    field_simp
    linear_combination (-1 : K) * hn
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemilinearCoordsEqMulVecStar
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private lemma star_mulVec_fin_three {L : Type} [CommRing L] [StarRing L] (N : Matrix (Fin 3) (Fin 3) L) (v : Fin 3 → L) :
    star (N *ᵥ v) = N.map star *ᵥ star v := by
  funext i
  have h := RingHom.map_mulVec (starRingEnd L) N v i
  exact h

theorem UpperTheory.semilinear_coords_eq_mulVec_star :
    ∀ (K : Type) [Field K] (Δ τ : K) (d : EL Δ τ) (A N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (e v : Fin 3 → Lsq K Δ),
        A * N.map star = N * A → A *ᵥ star e = e → A *ᵥ star v = d.re • v + d.im • (N *ᵥ v) →
        N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v → ∀ x : Sp Δ τ,
        (semi d x).1 • e + (semi d x).2.re • v + (semi d x).2.im • (N *ᵥ v) = A *ᵥ star (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) := by
  intro K _ Δ τ d A N e v hAN he hv hN x
  have hNv : A *ᵥ star (N *ᵥ v) = d.re • (N *ᵥ v) + d.im • (algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v) := by
    rw [star_mulVec_fin_three, Matrix.mulVec_mulVec, hAN, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hN]
  have hs : star (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) =
      star x.1 • star e + star x.2.re • star v + star x.2.im • star (N *ᵥ v) := by
    funext i
    simp [mul_comm]
  rw [hs, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, he, hv, hNv]
  funext i
  simp only [semi, sigL, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  simp
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SigLEqOfHermSemilinearEqStar
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {Δ τ : K}

private theorem sigL_mul' (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL]

private theorem sigL_sigL' (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sigL_one' : sigL (1 : EL Δ τ) = 1 := by
  ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem trace_sigL (x : EL Δ τ) : QuadraticAlgebra.trace (sigL x) = star (QuadraticAlgebra.trace x) := by
  have e : star (algebraMap K (Lsq K Δ) τ) = algebraMap K (Lsq K Δ) τ := by
    ext <;> simp
  simp [QuadraticAlgebra.trace_def, sigL, e]

private theorem eq_zero_of_trace (hτ : τ ^ 2 - 4 ≠ 0) {w : EL Δ τ}
    (h : ∀ x, QuadraticAlgebra.trace (w * x) = 0) : w = 0 := by
  have h1 := h 1
  have h2 := h QuadraticAlgebra.omega
  simp [QuadraticAlgebra.trace_def] at h1 h2
  have hu : IsUnit (algebraMap K (Lsq K Δ) (τ ^ 2 - 4)) := (IsUnit.mk0 _ hτ).map _
  rw [map_sub, map_pow, map_ofNat] at hu
  refine QuadraticAlgebra.ext ?_ ?_
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * h1 - (algebraMap K (Lsq K Δ) τ) * h2
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination 2 * h2 - (algebraMap K (Lsq K Δ) τ) * h1

end SlopeTestRemainingChoices

theorem UpperTheory.sigL_eq_of_herm_semilinear_eq_star :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ c : K) (d m : EL Δ τ), τ ^ 2 - 4 ≠ 0 →
        (∀ x y : Sp Δ τ, herm c m (semi d x) (semi d y) = star (herm c m x y)) → sigL m = m * d * star (sigL d) := by
  intro K _ _ Δ τ c d m hτ h
  have key : ∀ a : EL Δ τ, QuadraticAlgebra.trace ((m * d * star (sigL d) - sigL m) * a) = 0 := fun a => by
    have e := h (0, sigL a) (0, 1)
    simp only [herm, semi, star_zero, mul_zero, zero_mul, zero_add, sigL_sigL', sigL_one', mul_one, star_one,
      sigL_mul'] at e
    rw [← trace_sigL, sigL_mul', sigL_sigL'] at e
    rw [sub_mul, map_sub, sub_eq_zero, ← e]
    congr 1
    ring
  exact (sub_eq_zero.1 (eq_zero_of_trace hτ key)).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsHermitianFormOfUnitaryRotationBasis
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

namespace UpperTheory.V.Z.Sym.Glob

variable {K : Type} [Field K] {Δ τ : K}

private def hh (x y : Fin 3 → Lsq K Δ) : Lsq K Δ := ∑ i, x i * star (y i)

private theorem hh_star (x y : Fin 3 → Lsq K Δ) : star (hh x y) = hh y x := by
  simp only [hh, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem hh_unitary {N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (hN : N ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ))
    (x y : Fin 3 → Lsq K Δ) : hh (N *ᵥ x) (N *ᵥ y) = hh x y := by
  change (N *ᵥ x) ⬝ᵥ star (N *ᵥ y) = x ⬝ᵥ star y
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    (Matrix.mem_unitaryGroup_iff').1 hN, Matrix.one_mulVec, dotProduct_comm]

private theorem hh_right (x y z : Fin 3 → Lsq K Δ) (r : Lsq K Δ) :
    hh x (r • y - z) = star r * hh x y - hh x z := by
  simp only [hh, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub, star_mul']
  ring

private theorem hh_left (x y z : Fin 3 → Lsq K Δ) (r : Lsq K Δ) :
    hh (r • y - z) x = r * hh y x - hh z x := by
  simp only [hh, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem hh_expand (e v w : Fin 3 → Lsq K Δ) (x0 p q y0 r s : Lsq K Δ) :
    hh (x0 • e + p • v + q • w) (y0 • e + r • v + s • w) =
      x0 * star y0 * hh e e + x0 * star r * hh e v + x0 * star s * hh e w +
      p * star y0 * hh v e + p * star r * hh v v + p * star s * hh v w +
      q * star y0 * hh w e + q * star r * hh w v + q * star s * hh w w := by
  simp only [hh, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul']
  ring

private theorem trace_form (m x y : EL Δ τ) :
    QuadraticAlgebra.trace (m * x * star (sigL y)) =
      x.re * star y.re * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) +
      x.re * star y.im * (algebraMap K (Lsq K Δ) τ * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im)
        - (algebraMap K (Lsq K Δ) τ * m.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * m.im)) +
      x.im * star y.re * (algebraMap K (Lsq K Δ) τ * m.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * m.im) +
      x.im * star y.im * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) := by
  simp only [QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL]
  ring

private theorem gram_unit {M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (h : IsUnit M.det) :
    IsUnit (M * Mᴴ).det := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  exact h.mul (h.star)

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.exists_hermitian_form_of_unitary_rotation_basis :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K), τ ^ 2 - 4 ≠ 0 → ∀ N : Matrix (Fin 3) (Fin 3) (Lsq K Δ), N ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) →
        ∀ e v : Fin 3 → Lsq K Δ, N *ᵥ e = e → N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v →
        IsUnit (Matrix.of ![e, v, N *ᵥ v]).det →
        ∃ (c : Kˣ) (m : EL Δ τ), IsUnit m ∧ star (sigL m) = m ∧ ∀ x y : Sp Δ τ,
          herm (c : K) m x y = ∑ i, (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) i * star ((y.1 • e + y.2.re • v + y.2.im • (N *ᵥ v)) i) := by
  intro K _ _ Δ τ hτ N hN e v hNe hNv hdet
  obtain ⟨w, hw⟩ : ∃ w, w = N *ᵥ v := ⟨_, rfl⟩
  rw [← hw] at hNv hdet ⊢
  obtain ⟨t, ht⟩ : ∃ t, t = algebraMap K (Lsq K Δ) τ := ⟨_, rfl⟩
  have hst : star t = t := by
    rw [ht]; ext <;> simp
  obtain ⟨u, hu⟩ : ∃ u, u = algebraMap K (Lsq K Δ) (τ ^ 2 - 4)⁻¹ := ⟨_, rfl⟩
  have hsu : star u = u := by
    rw [hu]; ext <;> simp
  have hut : u * (t ^ 2 - 4) = 1 := by
    have : algebraMap K (Lsq K Δ) ((τ ^ 2 - 4)⁻¹ * (τ ^ 2 - 4)) = 1 := by
      rw [inv_mul_cancel₀ hτ, map_one]
    rw [map_mul, map_sub, map_pow, map_ofNat] at this
    rw [hu, ht]; exact this
  have h2t : IsUnit (2 - t) := by
    refine IsUnit.of_mul_eq_one (-(2 + t) * u) ?_
    linear_combination hut

  have hvw : hh e v = hh e w := by
    conv_lhs => rw [← hh_unitary hN e v, hNe, ← hw]
  have hew0 : hh e w = hh e (t • w - v) := by
    conv_lhs => rw [← hh_unitary hN e w, hNe, hNv, ← ht]
  rw [hh_right, hst] at hew0
  have hew : hh e w = 0 := by
    have : (2 - t) * hh e w = 0 := by linear_combination hew0 - hvw
    exact (h2t.mul_right_eq_zero).1 this
  have hev : hh e v = 0 := hvw.trans hew
  have hwe : hh w e = 0 := by rw [← hh_star, hew, star_zero]
  have hve : hh v e = 0 := by rw [← hh_star, hev, star_zero]
  have hww : hh w w = hh v v := by rw [hw, hh_unitary hN]
  have hsa : star (hh v v) = hh v v := hh_star _ _
  have hsc : star (hh e e) = hh e e := hh_star _ _
  have hb : hh w v = t * hh w w - hh v w := by
    have h := hh_unitary hN w v
    rw [← hw, hNv, ← ht, hh_left] at h
    exact h.symm

  have hG : IsUnit (hh e e * (hh v v * hh v v - hh v w * hh w v)) := by
    have h := gram_unit hdet
    have e1 : (Matrix.of ![e, v, w] * (Matrix.of ![e, v, w])ᴴ) =
        !![hh e e, hh e v, hh e w; hh v e, hh v v, hh v w; hh w e, hh w v, hh w w] := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, hh, Fin.sum_univ_three, Matrix.conjTranspose_apply]
    rw [e1, Matrix.det_fin_three] at h
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.cons_val_fin_one, hev, hew, hve, hwe, hww] at h
    convert h using 1
    ring
  have hc : IsUnit (hh e e) := isUnit_of_mul_isUnit_left hG
  have hq : IsUnit (hh v v * hh v v - hh v w * hh w v) := isUnit_of_mul_isUnit_right hG

  have him : (hh e e).im = 0 := by
    have h := congrArg QuadraticAlgebra.im hsc
    rw [QuadraticAlgebra.im_star] at h
    have h2 : (2 : K) * (hh e e).im = 0 := by linear_combination -h
    simpa using h2
  have hce : hh e e = algebraMap K (Lsq K Δ) (hh e e).re := by
    ext <;> simp [him]
  have hc0 : (hh e e).re ≠ 0 := by
    intro h0
    rw [hce, h0, map_zero] at hc
    exact not_isUnit_zero hc
  obtain ⟨a, ha⟩ : ∃ a, a = hh v v := ⟨_, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b, b = hh w v := ⟨_, rfl⟩
  have hvw' : hh v w = t * a - b := by
    rw [hww, ← ha, ← hb'] at hb
    linear_combination hb
  have hsb : star b = t * a - b := by
    rw [hb', hh_star, ← hb', hvw']
  have hsa' : star a = a := by rw [ha, hsa]
  obtain ⟨m, hm⟩ : ∃ m : EL Δ τ, m = ⟨u * ((t ^ 2 - 2) * a - t * b), u * (2 * b - t * a)⟩ := by
    rw [ht]; exact ⟨_, rfl⟩
  subst ht
  have hm0 : m.re = u * (((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * a - algebraMap K (Lsq K Δ) τ * b) := by rw [hm]
  have hm1 : m.im = u * (2 * b - algebraMap K (Lsq K Δ) τ * a) := by rw [hm]
  have hT0 : 2 * m.re + algebraMap K (Lsq K Δ) τ * m.im = a := by
    rw [hm0, hm1]; linear_combination a * hut
  have hT1 : algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im = b := by
    rw [hm0, hm1]; linear_combination b * hut
  have hs0 : star m.re = u * (algebraMap K (Lsq K Δ) τ * b - 2 * a) := by
    rw [hm0]
    simp only [star_mul', star_sub, star_pow, hsu, hst, hsa', hsb, star_ofNat]
    ring
  have hs1 : star m.im = u * (algebraMap K (Lsq K Δ) τ * a - 2 * b) := by
    rw [hm1]
    simp only [star_mul', star_sub, hsu, hst, hsa', hsb, star_ofNat]
    ring
  refine ⟨Units.mk0 _ hc0, m, ?_, ?_, ?_⟩
  · rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
    have hn : (4 - (algebraMap K (Lsq K Δ) τ) ^ 2) * QuadraticAlgebra.norm m = a * a - (algebraMap K (Lsq K Δ) τ * a - b) * b := by
      rw [QuadraticAlgebra.norm_def, hm0, hm1]
      linear_combination (u * ((algebraMap K (Lsq K Δ) τ) ^ 2 - 4) + 1) * (a * a - (algebraMap K (Lsq K Δ) τ * a - b) * b) * hut
    rw [hvw', ← hb', ← ha] at hq
    rw [← hn] at hq
    exact isUnit_of_mul_isUnit_right hq
  · refine QuadraticAlgebra.ext ?_ ?_
    · rw [QuadraticAlgebra.re_star]
      change star m.re + algebraMap K (Lsq K Δ) τ * star m.im = m.re
      rw [hs0, hs1, hm0]
      ring
    · rw [QuadraticAlgebra.im_star]
      change -star m.im = m.im
      rw [hs1, hm1]
      ring
  · intro x y
    change herm _ m x y = hh _ _
    rw [hh_expand, herm, trace_form, hT0, hT1, hev, hew, hve, hwe, hww, hvw', ← ha, ← hb', Units.val_mk0, ← hce]
    ring
end

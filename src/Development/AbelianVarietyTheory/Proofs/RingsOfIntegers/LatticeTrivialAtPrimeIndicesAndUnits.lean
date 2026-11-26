module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMul
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
public import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.LatticeIndex

namespace GlobalTheory.TrivLattice

private theorem isAddTorsion_quotient_of_nsmul_mem {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ b ∈ B, m • b ∈ A) : IsAddTorsion (B ⧸ A.addSubgroupOf B) := by
  intro x
  refine QuotientAddGroup.induction_on x (fun b => ?_)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  simpa using h b b.2

theorem relIndex_ne_zero_of_fg {G : Type} [AddCommGroup G] (A B : AddSubgroup G) [AddGroup.FG B] (m : ℕ) (hm : m ≠ 0)
    (h : ∀ b ∈ B, m • b ∈ A) : A.relIndex B ≠ 0 := by
  haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective (A.addSubgroupOf B))
  haveI := AddCommGroup.finite_of_fg_isAddTorsion _ (isAddTorsion_quotient_of_nsmul_mem A B m hm h)
  exact AddSubgroup.index_ne_zero_of_finite

section
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem nsmul_mem_of_le {A B : Submodule (𝓞 E) (Fin n → E)} {k : ℕ} (h : Ideal.span {(k : 𝓞 E)} • A ≤ B)
    {v : Fin n → E} (hv : v ∈ A) : k • v ∈ B := by
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact h (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv)

theorem fg_of_nsmul_mem (A : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (hk : k ≠ 0) (h : ∀ v ∈ A, k • v ∈ stdLat E n) :
    AddGroup.FG A.toAddSubgroup := by
  let f : (Fin n → E) →ₗ[ℤ] (Fin n → E) := (k : ℤ) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h0 : (k : ℤ) • (x - y) = 0 := by
      simp only [f, LinearMap.smul_apply, LinearMap.id_apply] at hxy
      rw [smul_sub, hxy, sub_self]
    rcases smul_eq_zero.1 h0 with h0 | h0
    · exact absurd (by exact_mod_cast h0) hk
    · exact sub_eq_zero.1 h0
  let T : Submodule ℤ (Fin n → E) := LinearMap.range ((GlobalTheory.LatticeIndex.incl E n).restrictScalars ℤ)
  have hT : T.FG := by
    simp only [T, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  haveI := isNoetherian_of_fg_of_noetherian T hT
  have hle : (A.restrictScalars ℤ).map f ≤ T := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu⟩ := GlobalTheory.LatticeIndex.mem_std.1 (h v hv)
    refine ⟨u, ?_⟩
    simp only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]
    exact hu
  have hA : (A.restrictScalars ℤ).FG :=
    Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le_of_isNoetherian hle)
  exact (AddGroup.fg_iff_addSubgroup_fg _).2 ((Submodule.fg_iff_addSubgroup_fg _).1 hA)

theorem index_part (Λ : GenLat E n) (N M ℓ k : ℕ) (hL : Λ.LevOK N M) (hl : ℓ.Prime) (hk : Nat.Coprime k ℓ)
    (h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n) (r : ℕ) :
    (Λ.zCard N r).factorization ℓ = (Λ.mIdx N r).factorization ℓ ∧ Λ.mIdx N r ≠ 0 := by
  obtain ⟨hNodd, -, hNle⟩ := hL
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hl.ne_one ((Nat.coprime_zero_left ℓ).1 hk)
  have memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n := fun x => by
    unfold GenLat.Ln
    exact Submodule.mem_inf
  have hS : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup := fun x hx => hNle hx
  have hLn : Λ.Ln.toAddSubgroup ≤ Λ.La.toAddSubgroup := fun x hx => ((memLn x).1 hx).1
  haveI := fg_of_nsmul_mem Λ.La hk0 h1
  haveI := fg_of_nsmul_mem Λ.Ln one_ne_zero (fun v hv => by rw [one_smul]; exact ((memLn v).1 hv).2)
  have hkLn : ∀ b ∈ Λ.La.toAddSubgroup, k • b ∈ Λ.Ln.toAddSubgroup := fun b hb =>
    (memLn _).2 ⟨nsmul_mem hb k, h1 b hb⟩
  have ha : Λ.Ln.toAddSubgroup.relIndex Λ.La.toAddSubgroup ≠ 0 :=
    relIndex_ne_zero_of_fg _ _ k hk0 hkLn
  have hnd := GlobalTheory.LatticeIndex.not_dvd_relIndex _ _ k ℓ hl hk ha hkLn
  have hb : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ≠ 0 := by
    refine relIndex_ne_zero_of_fg _ _ N hNodd.pos.ne' (fun b hb => ?_)
    show N • b ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ((memLn b).1 hb).2
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hS hLn
  change ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup ^ r).factorization ℓ =
      ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ^ r).factorization ℓ ∧
    (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ^ r ≠ 0
  refine ⟨?_, pow_ne_zero _ hb⟩
  rw [← hmul, mul_pow, Nat.factorization_mul (pow_ne_zero _ hb) (pow_ne_zero _ ha)]
  simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]

theorem detSet_max {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation E Γ)
    (hw : ∀ r : 𝓞 E, w (algebraMap (𝓞 E) E r) ≤ 1) (A : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (hk : w (k : E) = 1)
    (h1 : ∀ v ∈ A, k • v ∈ stdLat E n) (h2 : ∀ v ∈ stdLat E n, k • v ∈ A) :
    (∀ y ∈ detSet A, w y ≤ 1) ∧ ∃ y ∈ detSet A, w y = 1 := by
  constructor
  · rintro y ⟨v, hv, rfl⟩
    have hc := GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E)) (v := v)
      (u := fun i => k • v i) (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul])
    obtain ⟨r, hr⟩ := GlobalTheory.LatticeIndex.det_std (u := fun i => k • v i) (fun i => h1 _ (hv i))
    rw [Matrix.det_one, _root_.one_mul, ← hr] at hc
    have hwc := congrArg w hc
    rw [map_mul, map_pow, hk, one_pow, _root_.one_mul] at hwc
    rw [hwc]
    exact hw r
  · refine ⟨(k : E) ^ n, ⟨fun i => k • (Pi.single i 1 : Fin n → E),
      fun i => h2 _ (GlobalTheory.LatticeIndex.single_std i), ?_⟩, ?_⟩
    · have hc := GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E))
        (v := fun i => (Pi.single i 1 : Fin n → E)) (u := fun i => k • (Pi.single i 1 : Fin n → E))
        (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul])
      beta_reduce at hc
      rw [GlobalTheory.LatticeIndex.det_single, _root_.mul_one, Matrix.det_one, _root_.one_mul] at hc
      exact hc
    · rw [map_pow, hk, one_pow]

private theorem valuation_beta_of_lattice_commensurable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (k : ℕ) (h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n)
    (h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La) {K : Type} [Field K] (io : c.F →+* K) (v0 : Valuation K (WithZero (Multiplicative ℤ)))
    (hint : ∀ x : K, IsIntegral ℤ x → v0 x ≤ 1) (hnat : v0 (k : K) = 1) (β : c.F)
    (hB : BetaIs (Dw := Dw) c Λ β) : v0 (io β) = 1 := by
  let w : Valuation c.F (WithZero (Multiplicative ℤ)) := v0.comap io
  have hwR : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r =>
    hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map io.toIntAlgHom)
  have hA : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      ∀ τ : E →+* ℂ, GlobalTheory.LatticeIndex.HasMax w (idealAt c A τ) 1 := by
    intro A hA1 hA2 τ
    let wτ : Valuation E (WithZero (Multiplicative ℤ)) := w.comap (embF c τ)
    have hwE : ∀ r : 𝓞 E, wτ (algebraMap (𝓞 E) E r) ≤ 1 := fun r =>
      hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map (io.comp (embF c τ)).toIntAlgHom)
    have hkE : wτ (k : E) = 1 := by
      simp only [wτ, w, Valuation.comap_apply, map_natCast]
      exact hnat
    have hm := detSet_max wτ hwE A hkE hA1 hA2
    unfold idealAt
    refine GlobalTheory.LatticeIndex.hasMax_span hwR ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact hm.1 d hd
    · obtain ⟨d, hd, hd1⟩ := hm.2
      exact ⟨_, ⟨d, hd, rfl⟩, hd1⟩
  have hprod : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      GlobalTheory.LatticeIndex.HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1 := by
    intro A hA1 hA2
    have := GlobalTheory.LatticeIndex.hasMax_prod hwR Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1)
      (fun τ => by simpa using (hA A hA1 hA2 τ).pow hwR (Dw.mult τ))
    simpa using this
  have memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n := fun x => by
    unfold GenLat.Ln
    exact Submodule.mem_inf
  have hLa := hprod Λ.La h1 h2
  have hLn := hprod Λ.Ln (fun v hv => nsmul_mem ((memLn v).1 hv).2 k)
    (fun v hv => (memLn _).2 ⟨h2 v hv, nsmul_mem hv k⟩)
  have hβ : GlobalTheory.LatticeIndex.HasMax w (𝓞 c.F ∙ β) (w β) :=
    GlobalTheory.LatticeIndex.hasMax_span hwR (by rintro y rfl; exact le_rfl) ⟨β, Set.mem_singleton β, rfl⟩
  have hm := hβ.mul hLa
  unfold BetaIs at hB
  rw [hB] at hm
  have hu := hm.unique hLn
  rw [_root_.mul_one] at hu
  exact hu

end

theorem trivAt_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → Λ.TrivAt ℓ → (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ = (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) ≠ 0 ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → (∀ β : c.F, β ≠ 0 → BetaIs (Dw := Dw) c Λ β → vV T.V (io β) = 0) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map io P ∈ FFV (Dw := Dw) T w n := by
  intro E _ _ _ H Dw l c n Λ N M ℓ _ hL hl hT
  obtain ⟨k, hk, hk1, hk2⟩ := hT
  have h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n := fun v hv => nsmul_mem_of_le hk1 hv
  have h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La := fun v hv => nsmul_mem_of_le hk2 hv
  obtain ⟨hidx, hne⟩ := index_part Λ N M ℓ k hL hl hk h1 (Dw.p + Dw.q)
  refine ⟨hidx, hne, fun T io hlT => ⟨?_, ?_⟩⟩
  · intro β _ hB
    have key : valV T.V (io β) = 1 := by
      have hint : ∀ x : T.Fr, IsIntegral ℤ x → valV T.V x ≤ 1 := fun x hx => GlobalTheory.LatticeIndex.valV_integral T hx
      have hnat := GlobalTheory.LatticeIndex.valV_nat T hk hlT
      unfold valV at hint hnat ⊢
      refine valuation_beta_of_lattice_commensurable c Λ k h1 h2 io _ ?_ ?_ β hB
      · intro x hx
        refine hint x ?_
        convert hx
        all_goals first
          | rfl
          | exact rfl
          | exact Subsingleton.elim _ _
          | (apply Algebra.algebra_ext; intro r; simp)
      · first
          | exact hnat
          | convert hnat using 2
    unfold vV
    rw [key]
    simp
  · intro w P hP
    have hunit : IsUnit (k : T.V) := by
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hk).map (Int.castRingHom T.V)
      have hab' : a * (k : T.V) + b * (ℓ : T.V) = 1 := by simpa using hab
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab' with h | h
      · exact isUnit_of_mul_isUnit_right h
      · exact absurd (isUnit_of_mul_isUnit_right h) hlT
    have hunitary : ∀ i j : Fin n, ∑ b, IsCMField.complexConj E ((1 : Matrix (Fin n) (Fin n) E) b i) *
        (1 : Matrix (Fin n) (Fin n) E) b j = if i = j then 1 else 0 := by
      intro i j
      rw [Finset.sum_eq_single i]
      · simp [Matrix.one_apply]
      · intro b _ hb
        simp [Matrix.one_apply_ne hb]
      · intro h
        exact absurd (Finset.mem_univ i) h
    obtain ⟨hmem, hone, -⟩ := GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io k 1 hunit hunitary
      (fun v hv => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]; exact h1 v hv)
    rwa [hone] at hmem

end GlobalTheory.TrivLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_trivial_at_prime_indices_and_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → Λ.TrivAt ℓ → (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ = (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) ≠ 0 ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → (∀ β : c.F, β ≠ 0 → BetaIs (Dw := Dw) c Λ β → vV T.V (io β) = 0) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map io P ∈ FFV (Dw := Dw) T w n := by
  first | exact @GlobalTheory.TrivLattice.trivAt_units | exact GlobalTheory.TrivLattice.trivAt_units | (intros; apply GlobalTheory.TrivLattice.trivAt_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralPointEqValueOnBiextensionCo
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralPointEqValueOnBiextensionCo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

def letterEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ) :
    Lt1 Dw × Fin n ≃ LtN Dw n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun ℓ := (⟨ℓ.1, ℓ.2.1⟩, ℓ.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem toK_prod_evV (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] (K : Type) [CommRing K] [Algebra V K] {d n : ℕ}
    (f : Fin n → PS V 1 d) :
    FB.toK K (∏ b, evV (n := n) ![pt V d b] (f b)) =
      GlobalTheory.PowGerm.boxSer (fun b => MvPowerSeries.map (algebraMap V K) (f b)) := by
  have key : ∀ b : Fin n, evV (n := n) ![pt V d b] (f b) =
      MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) (f b) := by
    intro b
    have hX : ∀ j : Fin 1 × Fin d,
        MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d))
          (MvPowerSeries.X j : MvPowerSeries (Fin 1 × Fin d) V) =
        (fun p : Fin 1 × Fin d => (![pt V d b] : Fin 1 → Pt V n d) p.1 p.2) j := by
      rintro ⟨i, j⟩
      rw [Fin.fin_one_eq_zero i, MvPowerSeries.rename_X]
      simp [pt]
    show evC _ (f b) = _
    exact evC_eq_algHom _ (fun j => by
      have h := (hX j).symm
      simp only at h
      rw [h, MvPowerSeries.rename_X]
      simp) _ hX (f b)
  simp only [FB.toK, key, map_prod, GlobalTheory.PowGerm.boxSer, MvPowerSeries.rename_map]

theorem nabValN_boxSer_eq_chartVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {S : Type} [Field S] [Algebra c.F S] [Algebra ℚ S]
    {y : FrPt Xo c S} (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (g : Fin n → PS S 1 C.d)
    (P : MvPolynomial (LtN Dw n) c.F) :
    chartVal C k g P = nabValN C.B S C.h H.w0 k (GlobalTheory.PowGerm.boxSer g) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map (algebraMap c.F S) P) := by
  classical
  have hcc : MvPowerSeries.constantCoeff C.h = 0 := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.11
  have hcol : ∀ (m : LtN Dw n →₀ ℕ) (b : Fin n),
      ReciprocityTheory.ChartRestriction.G.TB.colM (Finsupp.mapDomain (letterEquiv Dw n).symm m) b = colOf m b := by
    intro m b
    unfold ReciprocityTheory.ChartRestriction.G.TB.colM colOf
    congr 1
    funext ℓ
    have hℓ : ((ℓ, b) : Lt1 Dw × Fin n) = (letterEquiv Dw n).symm ⟨ℓ.1, (ℓ.2, b)⟩ := rfl
    rw [hℓ, Finsupp.mapDomain_apply_of_injective (letterEquiv Dw n).symm.injective]
  have hP : MvPolynomial.map (algebraMap c.F S) P = MvPolynomial.rename (letterEquiv Dw n)
      (MvPolynomial.rename (letterEquiv Dw n).symm (MvPolynomial.map (algebraMap c.F S) P)) := by
    rw [MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id_apply]
  rw [hP, GlobalTheory.nabValN_boxSer S C.d (𝓞 E) C.B S C.h H.w0 hcc k n g (Lt1 Dw) (LtN Dw n) (letterEquiv Dw n)
    (fun ℓ => ℓ.2.2) C.uvec (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (fun _ => rfl) (fun _ => rfl),
    GlobalTheory.NabCol.sum_support_rename]
  unfold chartVal
  rw [MvPolynomial.support_map_of_injective _ (algebraMap c.F S).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  simp only [hcol]

theorem hv_eq_nabValN : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (k n : ℕ) (F : Fin n → SecN Xo (xOf y) k) (f : Fin n → PS T.V 1 (chD C.ch)), (∀ b, GermIs C k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → letI := io.toAlgebra; hv Xo c nab y.1 k F P = nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C nab hnab B hB k n F f hF w P hP
  letI := io.toAlgebra
  obtain ⟨hG, hAct, -⟩ := hB
  have hgen := C.gen.1
  have hFK : B.FK T.Fr = C.ch.B.FK T.Fr := by
    unfold FB.FK FGLaw.mapF
    funext i
    simp [hG, hgen.1 i]
  have hAK : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    unfold FB.actK
    funext i
    simp [hAct, hgen.2.1 a i]
  have h1 := GlobalTheory.T.harmonicValue_eq_chart_value E H Dw l Xo c hstar nab hnab T.Fr y.1 C.ch k n F
    (fun b => MvPowerSeries.map (algebraMap T.V T.Fr) (f b)) (fun b => hF b) w P hP
  rw [h1, nabValN_boxSer_eq_chartVal C.ch k _ P, ← toK_prod_evV T.V T.Fr f]
  exact GlobalTheory.ChartCmp.nabValN_congr_FK C.ch.B B T.Fr hFK hAK _ _ _ _ _ _ _

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralPointEqValueOnBiextensionCoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_integralPoint_eq_value_on_biextensionCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (k n : ℕ) (F : Fin n → SecN Xo (xOf y) k) (f : Fin n → PS T.V 1 (chD C.ch)), (∀ b, GermIs C k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → letI := io.toAlgebra; hv Xo c nab y.1 k F P = nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  first | exact @GlobalTheory.PlaceInt.hv_eq_nabValN | exact GlobalTheory.PlaceInt.hv_eq_nabValN | (intros; apply GlobalTheory.PlaceInt.hv_eq_nabValN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MaximalIdealFormalPointsFormModule
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MaximalIdealFormalPointsFormModule
set_option autoImplicit false
noncomputable section
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.PlaceInt.FormalPts

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {d : ℕ}

def SmallPt {n : ℕ} (x : Pt V n d) : Prop := ∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V

def subPt {m n : ℕ} (a : Fin m → Pt V n d) (p : Pt V m d) : Pt V n d := fun i => evV a (p i)

theorem small_one {n : ℕ} {x : Pt V n d} (hx : SmallPt x) : ∀ j, SmallPt (![x] j) := by
  intro j
  fin_cases j
  simpa using hx

theorem small_two {n : ℕ} {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) : ∀ j, SmallPt (![x, y] j) := by
  intro j
  fin_cases j
  · simpa using hx
  · simpa using hy

theorem small_three {n : ℕ} {x y z : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) (hz : SmallPt z) :
    ∀ j, SmallPt (![x, y, z] j) := by
  intro j
  fin_cases j
  · simpa using hx
  · simpa using hy
  · simpa using hz

variable [IsAdicComplete (maximalIdeal V) V] [CharZero V]

theorem small_evV {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (f : PS V m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (evV a f) ∈ maximalIdeal V := by
  have S := evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  exact S.2.1 f (by rw [hf]; exact zero_mem _)

theorem evV_ev {l m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (b : Fin l → Pt V m d)
    (hb : ∀ j, GP (b j)) (f : PS V l d) : evV a (ev b f) = evV (fun j => subPt a (b j)) f := by
  have hb' : ∀ p : Fin l × Fin d, MvPowerSeries.constantCoeff (b p.1 p.2) ∈ maximalIdeal V := fun p => by
    rw [hb p.1 p.2]
    exact zero_mem _
  have S := evC_spec V (Fin l × Fin d) (Fin m × Fin d) (Fin n × Fin d) (fun p => b p.1 p.2) hb'
  have e1 : ev b f = evC (fun p : Fin l × Fin d => b p.1 p.2) f := (S.2.2.1 (fun p => hb p.1 p.2) f).symm
  rw [e1]
  exact S.2.2.2 (fun p => a p.1 p.2) (fun p => ha p.1 p.2) f

theorem subPt_pt {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (j : Fin m) :
    subPt a (pt V d j) = a j := by
  funext i
  obtain ⟨⟨ψ, hX, hψ⟩, -⟩ :=
    evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  show evC (fun p : Fin m × Fin d => a p.1 p.2) (MvPowerSeries.X (j, i)) = a j i
  rw [hψ, hX]

theorem subPt_zero {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) :
    subPt a (0 : Pt V m d) = 0 := by
  funext i
  obtain ⟨⟨ψ, -, hψ⟩, -⟩ :=
    evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  show evC (fun p : Fin m × Fin d => a p.1 p.2) 0 = 0
  rw [hψ, map_zero]

theorem subPt_addOf {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (F : Fin d → PS V 2 d)
    (p q : Pt V m d) (hp : GP p) (hq : GP q) :
    subPt a (addOf F p q) = addV F (subPt a p) (subPt a q) := by
  funext i
  show evV a (ev ![p, q] (F i)) = evV ![subPt a p, subPt a q] (F i)
  rw [evV_ev a ha ![p, q] (pair_points_zero_constant hp hq) (F i)]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem subPt_comp1 {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (φ : Pt V 1 d)
    (p : Pt V m d) (hp : GP p) : subPt a (comp1 φ p) = compV φ (subPt a p) := by
  funext i
  show evV a (ev ![p] (φ i)) = evV ![subPt a p] (φ i)
  rw [evV_ev a ha ![p] (single_point_zero_constant hp) (φ i)]
  congr 1
  funext j
  fin_cases j
  rfl

variable (G : FGLaw V d) {n : ℕ}

theorem addV_comm {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) : addV G.F x y = addV G.F y x := by
  funext i
  have h2 := small_two hx hy
  have g0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have key := congrArg (evV ![x, y]) (G.comm i)
  rw [evV_ev _ h2 _ (pair_points_zero_constant g1 g0)] at key
  refine key.symm.trans ?_
  show evV (fun j => subPt ![x, y] (![pt V (n := 2) d 1, pt V (n := 2) d 0] j)) (G.F i) = evV ![y, x] (G.F i)
  congr 1
  funext j
  fin_cases j
  · exact subPt_pt _ h2 1
  · exact subPt_pt _ h2 0

theorem addV_assoc {x y z : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) (hz : SmallPt z) :
    addV G.F (addV G.F x y) z = addV G.F x (addV G.F y z) := by
  funext i
  have h3 := small_three hx hy hz
  have g0 : GP (pt V (n := 3) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 3) d 1) := gp_pt 1
  have g2 : GP (pt V (n := 3) d 2) := gp_pt 2
  have e0 : subPt ![x, y, z] (pt V (n := 3) d 0) = x := subPt_pt _ h3 0
  have e1 : subPt ![x, y, z] (pt V (n := 3) d 1) = y := subPt_pt _ h3 1
  have e2 : subPt ![x, y, z] (pt V (n := 3) d 2) = z := subPt_pt _ h3 2
  have key := congrArg (evV ![x, y, z]) (G.assoc i)
  have hl : evV ![x, y, z] (ev ![addOf G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1), pt V (n := 3) d 2] (G.F i)) =
      addV G.F (addV G.F x y) z i := by
    rw [evV_ev _ h3 _ (pair_points_zero_constant (gp_addOf G.F G.const _ _ g0 g1) g2)]
    show evV _ (G.F i) = evV ![addV G.F x y, z] (G.F i)
    congr 1
    funext j
    fin_cases j
    · show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1)) = addV G.F x y
      rw [subPt_addOf _ h3 _ _ _ g0 g1, e0, e1]
    · exact e2
  have hr : evV ![x, y, z] (ev ![pt V (n := 3) d 0, addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)] (G.F i)) =
      addV G.F x (addV G.F y z) i := by
    rw [evV_ev _ h3 _ (pair_points_zero_constant g0 (gp_addOf G.F G.const _ _ g1 g2))]
    show evV _ (G.F i) = evV ![x, addV G.F y z] (G.F i)
    congr 1
    funext j
    fin_cases j
    · exact e0
    · show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)) = addV G.F y z
      rw [subPt_addOf _ h3 _ _ _ g1 g2, e1, e2]
  exact hl.symm.trans (key.trans hr)

theorem zero_addV {x : Pt V n d} (hx : SmallPt x) : addV G.F 0 x = x := by
  funext i
  have h1 := small_one hx
  have g0 : GP (pt V (n := 1) d 0) := gp_pt 0
  have e : subPt ![x] (pt V (n := 1) d 0) = x := subPt_pt _ h1 0
  have key := congrArg (evV ![x]) (G.unit i)
  rw [evV_ev _ h1 _ (pair_points_zero_constant gp_zero₂ g0)] at key
  refine Eq.trans ?_ (key.trans (congrFun e i))
  show evV ![0, x] (G.F i) = _
  congr 1
  funext j
  fin_cases j
  · exact (subPt_zero _ h1).symm
  · exact e.symm

theorem addV_zero {x : Pt V n d} (hx : SmallPt x) : addV G.F x 0 = x := by
  have h0 : SmallPt (0 : Pt V n d) := fun i => by
    show MvPowerSeries.constantCoeff (0 : PS V n d) ∈ maximalIdeal V
    rw [map_zero]
    exact zero_mem _
  rw [addV_comm G hx h0]
  exact zero_addV G hx

variable {O : Type} [CommRing O] {G} (A : OAct O G)

theorem act_addV (a : O) {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) :
    compV (A.act a) (addV G.F x y) = addV G.F (compV (A.act a) x) (compV (A.act a) y) := by
  have h2 := small_two hx hy
  have g0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have e0 : subPt ![x, y] (pt V (n := 2) d 0) = x := subPt_pt _ h2 0
  have e1 : subPt ![x, y] (pt V (n := 2) d 1) = y := subPt_pt _ h2 1
  have hφ : GP (A.act a) := A.const a
  have key := congrArg (subPt ![x, y]) (A.hom a)
  unfold FGLaw.add at key
  rw [subPt_comp1 _ h2 _ _ (gp_addOf _ G.const _ _ g0 g1), subPt_addOf _ h2 _ _ _ g0 g1,
    subPt_addOf _ h2 _ _ _ (gp_comp1 _ _ hφ g0) (gp_comp1 _ _ hφ g1), subPt_comp1 _ h2 _ _ g0,
    subPt_comp1 _ h2 _ _ g1, e0, e1] at key
  exact key

theorem add_actV (a b : O) {x : Pt V n d} (hx : SmallPt x) :
    compV (A.act (a + b)) x = addV G.F (compV (A.act a) x) (compV (A.act b) x) := by
  show subPt ![x] (A.act (a + b)) = addV G.F (subPt ![x] (A.act a)) (subPt ![x] (A.act b))
  rw [A.add_act a b]
  unfold FGLaw.add
  exact subPt_addOf _ (small_one hx) _ _ _ (A.const a) (A.const b)

theorem mul_actV (a b : O) {x : Pt V n d} (hx : SmallPt x) :
    compV (A.act (a * b)) x = compV (A.act a) (compV (A.act b) x) := by
  show subPt ![x] (A.act (a * b)) = compV (A.act a) (subPt ![x] (A.act b))
  rw [A.mul_act a b]
  exact subPt_comp1 _ (small_one hx) _ _ (A.const b)

theorem one_actV {x : Pt V n d} (hx : SmallPt x) : compV (A.act 1) x = x := by
  show subPt ![x] (A.act 1) = x
  rw [A.one_act]
  exact subPt_pt _ (small_one hx) 0

theorem zero_actV {x : Pt V n d} (hx : SmallPt x) : compV (A.act 0) x = 0 := by
  show subPt ![x] (A.act 0) = 0
  rw [GlobalTheory.FourierChainCompare.act_zero A]
  exact subPt_zero _ (small_one hx)

theorem addV_neg_actV {x : Pt V n d} (hx : SmallPt x) : addV G.F x (compV (A.act (-1)) x) = 0 := by
  have h := add_actV A 1 (-1) hx
  rw [one_actV A hx, add_neg_cancel, zero_actV A hx] at h
  exact h.symm

end GlobalTheory.PlaceInt.FormalPts

namespace GlobalTheory.PlaceInt
open FormalPts

theorem smallPts_module : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (x y z : Pt V n d), (∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (y i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (z i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (addV B.G.F x y i) ∈ maximalIdeal V) ∧ addV B.G.F x y = addV B.G.F y x ∧ addV B.G.F (addV B.G.F x y) z = addV B.G.F x (addV B.G.F y z) ∧ addV B.G.F x 0 = x ∧ addV B.G.F x (compV (B.A.act (-1)) x) = 0 ∧ compV (B.A.act 1) x = x ∧ compV (B.A.act 0) x = 0 ∧ ∀ a b : O, (∀ i, MvPowerSeries.constantCoeff (compV (B.A.act a) x i) ∈ maximalIdeal V) ∧ compV (B.A.act a) (addV B.G.F x y) = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act a) y) ∧ compV (B.A.act (a + b)) x = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act b) x) ∧ compV (B.A.act (a * b)) x = compV (B.A.act a) (compV (B.A.act b) x) := by
  intro V _ _ _ _ _ d O _ _ B n x y z hx hy hz
  refine ⟨fun i => small_evV ![x, y] (small_two hx hy) (B.G.F i) (B.G.const i), addV_comm B.G hx hy,
    addV_assoc B.G hx hy hz, addV_zero B.G hx, addV_neg_actV B.A hx, one_actV B.A hx, zero_actV B.A hx,
    fun a b => ⟨fun i => small_evV ![x] (small_one hx) (B.A.act a i) (B.A.const a i), act_addV B.A a hx hy,
      add_actV B.A a b hx, mul_actV B.A a b hx⟩⟩

end GlobalTheory.PlaceInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MaximalIdealFormalPointsFormModuleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_ideal_formal_points_form_module : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (x y z : Pt V n d), (∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (y i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (z i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (addV B.G.F x y i) ∈ maximalIdeal V) ∧ addV B.G.F x y = addV B.G.F y x ∧ addV B.G.F (addV B.G.F x y) z = addV B.G.F x (addV B.G.F y z) ∧ addV B.G.F x 0 = x ∧ addV B.G.F x (compV (B.A.act (-1)) x) = 0 ∧ compV (B.A.act 1) x = x ∧ compV (B.A.act 0) x = 0 ∧ ∀ a b : O, (∀ i, MvPowerSeries.constantCoeff (compV (B.A.act a) x i) ∈ maximalIdeal V) ∧ compV (B.A.act a) (addV B.G.F x y) = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act a) y) ∧ compV (B.A.act (a + b)) x = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act b) x) ∧ compV (B.A.act (a * b)) x = compV (B.A.act a) (compV (B.A.act b) x) := by
  first | exact @GlobalTheory.PlaceInt.smallPts_module | exact GlobalTheory.PlaceInt.smallPts_module | (intros; apply GlobalTheory.PlaceInt.smallPts_module <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RamifiedPrimeLossLeValuationPrimePower
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RamifiedPrimeLossLeValuationPrimePower
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlaceTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie

theorem ramLoss_le_vLa_pPow (D : D7) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (j : ℕ)
    (w : WeightFamilies.Wt D j) (a b : ℕ) (ha : c2 D w ≤ a) (hb : Formalism.MainNotions.DIV.Cons.cHalf w ≤ b) :
    ramLoss D la w ≤ ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) := by
  have hqp : D.host.q.Prime := D.host.hyp.1
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  obtain ⟨hs, hq, hd, -, -⟩ := UpperTheory.cmDatum_discriminantDepth_bounds D.host.toHostAx
  have hN : pPow D a b b ≠ 0 := by
    unfold pPow
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hqp.ne_zero)) (pow_ne_zero _ hdp.ne_zero)
  have hl := Crude.resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hl⟩
  have ha' : (DF w : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (DF w : ℝ) / 2 ≤ b := Nat.ceil_le.1 hb
  have hD : (0 : ℝ) ≤ (DF w : ℝ) := Nat.cast_nonneg _
  have he : (0 : ℝ) ≤ (ramOverZ la : ℝ) := Nat.cast_nonneg _
  have hR : ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) = (padicValNat (resCharOf la) (pPow D a b b) : ℝ) * ramOverZ la := by
    rw [Crude.crv_vLa_natCast la hN, Int.cast_natCast, Nat.cast_mul]
  have hz : ∀ p ∈ D.host.condN.primeFactors, p ≠ resCharOf la →
      ((vLa la (p : K) : ℤ) : ℝ) * D.host.vdH p * (DF w : ℝ) / 2 = 0 := fun p hp hne => by
    have hpp := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    rw [Crude.crv_vLa_natCast la hpp.ne_zero, Nat.padicValNat_def, multiplicity_primes hne.symm]; simp
  rw [ramLoss, hR]
  by_cases hm : resCharOf la ∈ D.host.condN.primeFactors
  · rw [Finset.sum_eq_single_of_mem _ hm hz, Crude.crv_vLa_natCast la hl.ne_zero, Nat.padicValNat_def, Nat.Prime.multiplicity_self]
    have key : D.host.vdH (resCharOf la) * (DF w : ℝ) / 2 ≤ (padicValNat (resCharOf la) (pPow D a b b) : ℝ) := by
      have hv0 := D.host.vdH_nonneg (resCharOf la)
      have hle : ∀ k : ℕ, resCharOf la ^ k ∣ pPow D a b b → (k : ℝ) ≤ (padicValNat (resCharOf la) (pPow D a b b) : ℝ) :=
        fun k hk => by exact_mod_cast ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hN).1 hk
      rcases (D.host.dvd_condN_iff_small hl).1 (Nat.dvd_of_mem_primeFactors hm) with h | h | h
      · have h1 := hle (padicValNat (resCharOf la) D.host.QS * a) (by
          rw [pow_mul]; exact ((pow_dvd_pow_of_dvd (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)) a).mul_right _).mul_right _)
        have h2 := (hs _ h).1
        push_cast at h1
        nlinarith [mul_le_mul h2 ha' hD (Nat.cast_nonneg _), mul_nonneg hv0 hD]
      · have h1 := hle b (by rw [h]; exact (Dvd.intro_left _ rfl).mul_right _)
        rw [h] at hv0 ⊢; rw [h] at h1
        nlinarith [mul_le_mul_of_nonneg_right hq hD]
      · have h1 := hle b (by rw [h]; exact Dvd.intro_left _ rfl)
        rw [h] at hv0 ⊢; rw [h] at h1
        nlinarith [mul_le_mul_of_nonneg_right hd hD]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right key he]
  · rw [Finset.sum_eq_zero fun p hp => hz p hp fun h => hm (h ▸ hp)]
    positivity

end GlobalTheory.PlaceTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RamifiedPrimeLossLeValuationPrimePowerStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power : ∀ (D : D7) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (j : ℕ) (w : WeightFamilies.Wt D j) (a b : ℕ), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → ramLoss D la w ≤ ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) := by
  first | exact @GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | exact GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | (intros; apply GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow <;> assumption)
end
end

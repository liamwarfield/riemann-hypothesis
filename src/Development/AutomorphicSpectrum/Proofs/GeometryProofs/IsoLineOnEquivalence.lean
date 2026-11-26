module

public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JPull
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalence
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.IcLineIsoIff
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

set_option linter.unusedSectionVars false

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def icEv (z : (Σ k, ι k) → ℂ) : MRing ι →+* ℂ :=
  (eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))

theorem icEv_eq (z : (Σ k, ι k) → ℂ) (f : MRing ι) : evC z f = icEv z f := rfl

def IcGood (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)) (d : K → ℤ) (r : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∃ f g : MRing ι, IsLineIso P d 0 f g ∧ ∀ z ∈ Xo, ∃ u v : MRing ι, u * f - v * g ∈ P ∧ icEv z u ≠ 0 ∧
    icEv z v ≠ 0 ∧ ‖icEv z v‖ * r z = ‖icEv z u‖

theorem ic_lineIso_iff (P : Ideal (MRing ι)) (a b : K → ℤ) (f g : MRing ι) :
    IsLineIso P a b f g ↔ IsLineIso P (a - b) 0 f g := by
  simp [IsLineIso]

theorem ic_iff {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) (hX : Xo ⊆ mcPts P)
    (A B : HermLine ι) : IsoLineOn P Xo A B ↔ IcGood P Xo (A.a - B.a) (fun z => B.h z / A.h z) := by
  constructor
  · rintro ⟨f, g, h, hd⟩
    refine ⟨f, g, (ic_lineIso_iff _ _ _ _ _).1 h, fun z hz => ?_⟩
    have hz' := hX hz
    obtain ⟨u, v, hu, hv, huv⟩ := h.2.2.2 (RingHom.ker (icEv z)) (RingHom.ker_isPrime _)
      (fun s hs => hz'.2 s hs) (fun k => by
        obtain ⟨i, hi⟩ := hz'.1 k
        refine ⟨i, fun hh => hi ?_⟩
        simpa [icEv, RingHom.mem_ker] using hh)
    rw [RingHom.mem_ker] at hu hv
    refine ⟨u, v, huv, hu, hv, ?_⟩
    have h0 := hd z hz u v huv hu
    simp only [icEv_eq] at h0
    have hA := A.pos z hz'.1
    have hB := B.pos z hz'.1
    have hu' : 0 < ‖icEv z u‖ := norm_pos_iff.2 hu
    have hv' : 0 < ‖icEv z v‖ := norm_pos_iff.2 hv
    have h1 := Real.eq_one_of_pos_of_log_eq_zero (by positivity) h0.symm
    field_simp at h1 ⊢
    linarith
  · rintro ⟨f, g, h, hd⟩
    refine ⟨f, g, (ic_lineIso_iff _ _ _ _ _).2 h, fun z hz u' v' huv' hu' => ?_⟩
    have hz' := hX hz
    obtain ⟨u, v, huv, hu, hv, he⟩ := hd z hz
    have h1 : (u * v' - u' * v) * g ∈ P := by
      have := P.sub_mem (P.mul_mem_left u' huv) (P.mul_mem_left u huv')
      convert this using 1
      ring
    have h2 : u * v' - u' * v ∈ P := (hP.1.mem_or_mem h1).resolve_right h.2.2.1
    have h3 : icEv z (u * v' - u' * v) = 0 := hz'.2 _ h2
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h3
    have h4 : ‖icEv z u‖ * ‖icEv z v'‖ = ‖icEv z u'‖ * ‖icEv z v‖ := by
      rw [← norm_mul, ← norm_mul, h3]
    simp only [icEv_eq] at hu' ⊢
    have hA := A.pos z hz'.1
    have hB := B.pos z hz'.1
    have hu1 : 0 < ‖icEv z u‖ := norm_pos_iff.2 hu
    have hu2 : 0 < ‖icEv z u'‖ := norm_pos_iff.2 hu'
    have hv1 : 0 < ‖icEv z v‖ := norm_pos_iff.2 hv
    have h5 : ‖icEv z v'‖ / ‖icEv z u'‖ = ‖icEv z v‖ / ‖icEv z u‖ := by
      rw [div_eq_div_iff hu2.ne' hu1.ne']
      linarith
    have h6 : ‖icEv z v'‖ / ‖icEv z u'‖ * B.h z / A.h z = 1 := by
      rw [h5, ← he]
      field_simp
    rw [h6, Real.log_one]

theorem ic_one {P : Ideal (MRing ι)} (Xo : Set ((Σ k, ι k) → ℂ)) (hP : IsMultiProjPrime P) :
    IcGood P Xo 0 1 :=
  ⟨1, 1, (i_algebra K ι P hP).1 0, fun z _ => ⟨1, 1, by simp, by simp, by simp, by simp⟩⟩

theorem ic_mul {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d d' : K → ℤ}
    {r r' : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (h' : IcGood P Xo d' r') :
    IcGood P Xo (d + d') (r * r') := by
  obtain ⟨f, g, h, hd⟩ := h
  obtain ⟨f', g', h', hd'⟩ := h'
  refine ⟨f * f', g * g', by simpa using (i_algebra K ι P hP).2.2.2.1 _ _ _ _ _ _ _ _ h h', fun z hz => ?_⟩
  obtain ⟨u, v, huv, hu, hv, he⟩ := hd z hz
  obtain ⟨u', v', huv', hu', hv', he'⟩ := hd' z hz
  refine ⟨u * u', v * v', ?_, by simp [hu, hu'], by simp [hv, hv'], ?_⟩
  · have := P.add_mem (P.mul_mem_left (u' * f') huv) (P.mul_mem_left (v * g) huv')
    convert this using 1
    ring
  · rw [map_mul, map_mul, norm_mul, norm_mul, ← he, ← he', Pi.mul_apply]
    ring

theorem ic_inv {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d : K → ℤ}
    {r : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) : IcGood P Xo (-d) r⁻¹ := by
  obtain ⟨f, g, h, hd⟩ := h
  refine ⟨g, f, ?_, fun z hz => ?_⟩
  · have := (ic_lineIso_iff _ _ _ _ _).1 ((i_algebra K ι P hP).2.1 _ _ _ _ h)
    simpa using this
  obtain ⟨u, v, huv, hu, hv, he⟩ := hd z hz
  refine ⟨v, u, by simpa using P.neg_mem huv, hv, hu, ?_⟩
  have hr : r z ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at he
    exact hu (norm_eq_zero.1 he.symm)
  rw [← he, Pi.inv_apply]
  field_simp

theorem ic_congr {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} {d d' : K → ℤ}
    {r r' : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (hd : d = d') (hr : ∀ z ∈ Xo, r z = r' z) :
    IcGood P Xo d' r' := by
  subst hd
  obtain ⟨f, g, h, hd⟩ := h
  refine ⟨f, g, h, fun z hz => ?_⟩
  rw [← hr z hz]
  exact hd z hz

theorem ic_pow {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d : K → ℤ}
    {r : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (n : ℕ) : IcGood P Xo (n • d) (r ^ n) := by
  induction n with
  | zero => simpa using ic_one Xo hP
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact ic_mul hP ih h

theorem ic_zpow {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d : K → ℤ}
    {r : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (n : ℤ) : IcGood P Xo (n • d) (r ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using ic_pow hP h m
  · simpa using ic_inv hP (ic_pow hP h m)

theorem ic_prod {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {J : Type}
    (s : Finset J) (d : J → K → ℤ) (r : J → ((Σ k, ι k) → ℂ) → ℝ) (h : ∀ j, IcGood P Xo (d j) (r j)) :
    IcGood P Xo (∑ j ∈ s, d j) (∏ j ∈ s, r j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ic_one Xo hP
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact ic_mul hP (h j) ih

end

theorem i_comb : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) := by
  intro K _ ι _ P Xo hP hX
  refine ⟨fun J _ ℓ ℓ' n h => ?_, fun A B C h h' => ?_, fun A B h => ?_, ?_⟩
  · rw [ic_iff hP hX]
    refine ic_congr (ic_prod hP Finset.univ _ _ fun j => ic_zpow hP ((ic_iff hP hX _ _).1 (h j)) (n j)) ?_ ?_
    · simp [Top.combLine, smul_sub, Finset.sum_sub_distrib]
    · intro z _
      simp [Top.combLine, div_zpow, Finset.prod_div_distrib]
  · rw [ic_iff hP hX] at h h' ⊢
    refine ic_congr (ic_mul hP h h') (by abel) fun z hz => ?_
    have hB := (B.pos z (hX hz).1).ne'
    have hA := (A.pos z (hX hz).1).ne'
    simp only [Pi.mul_apply]
    field_simp
  · rw [ic_iff hP hX] at h ⊢
    refine ic_congr (ic_inv hP h) (by abel) fun z _ => ?_
    simp
  · intro K₁ _ ι₁ _ κ v J _ ℓ ℓ' n hv h
    refine ⟨?_, fun z' => ?_⟩
    · funext k
      simp only [Top.combLine, Finset.sum_apply, Pi.smul_apply, fun j => (h j).1, pullDeg]
      by_cases hk : ∃ k₁, κ k₁ = k
      · obtain ⟨k₁, rfl⟩ := hk
        simp only [hv.1.extend_apply, Finset.sum_apply, Pi.smul_apply]
      · simp [Function.extend_apply' _ _ _ hk]
    · simp only [Top.combLine, fun j => (h j).2 z']

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalence
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines

theorem isoLineOn_comb_trans_symm_pull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) :=
  @PositivityTheory.UnitarySelfGeneration.i_comb

end GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalenceStatement
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_line_on_equivalence : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull | exact GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentResidueIntegrality
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentResidueIntegrality
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTStalk

section Lattices

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem mem_htW_iff (M : LieModel G ξ V) (L : Semi.LB G.left) (n : ℕ) {R : Type} [CommRing R]
    (ρ : R →+* Module.End Ω V) (σ : R →+* Ω) (𝔡 : Ideal R) (q : Cpt ξ) (e : V) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨Submodule.zero_mem _, fun d _ => by simp⟩
    | add x y _ _ hx hy =>
      refine ⟨Submodule.add_mem _ hx.1 hy.1, fun d hd => ?_⟩
      rw [smul_add]
      exact Submodule.add_mem _ (hx.2 d hd) (hy.2 d hd)
    | smul c x _ hx =>
      refine ⟨(GlobalTheory.CompanionTheory.Ar.eigSp ρ σ).smul_mem (c : Ω) hx.1, fun d hd => ?_⟩
      have h : σ d • c • x = c • σ d • x := smul_comm _ _ _
      rw [h]
      exact Submodule.smul_mem _ c (hx.2 d hd)
  · exact fun h => Submodule.subset_span h

theorem mem_htW_iff_forms (M : LieModel G ξ V) (L : Semi.LB G.left) (n : ℕ) {R : Type} [CommRing R]
    (ρ : R →+* Module.End Ω V) (σ : R →+* Ω) (𝔡 : Ideal R) (q : Cpt ξ) (e : V) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔
      e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, ∀ d ∈ 𝔡, σ d * w e ∈ regAt ξ q := by
  rw [mem_htW_iff]
  refine and_congr_right fun he => ⟨fun h w hw d hd => ?_, fun h d hd => ?_⟩
  · have := ((M.mem_htDual_iff L n ρ σ q _).1 (h d hd)).2 w hw
    simpa [map_smul, smul_eq_mul] using this
  · refine (M.mem_htDual_iff L n ρ σ q _).2 ⟨(GlobalTheory.CompanionTheory.Ar.eigSp ρ σ).smul_mem _ he, fun w hw => ?_⟩
    simpa [map_smul, smul_eq_mul] using h w hw d hd

end Lattices

theorem forall_different_iff {o Ω E : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field E] [NumberField E]
    (A : Subalgebra o Ω) (B : Subring Ω) (hA : ∀ a : A, (a : Ω) ∈ B) (σ : E →+* Ω) (ds : A)
    (hds : GeneratesDiff σ ds) (t : Ω) :
    (∀ x ∈ differentIdeal ℤ (𝓞 E), σ (x : E) * t ∈ B) ↔ (ds : Ω) * t ∈ B := by
  constructor
  · intro h
    have h1 : algebraMap A Ω ds ∈ Submodule.span A {algebraMap A Ω ds} :=
      Submodule.subset_span rfl
    rw [hds] at h1
    have h2 : ∀ z ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)}, z * t ∈ B := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        exact h x hx
      | zero => simpa using B.zero_mem
      | add u v _ _ hu hv =>
        rw [add_mul]
        exact B.add_mem hu hv
      | smul a u _ hu =>
        have : (a • u) * t = (a : Ω) * (u * t) := by
          rw [Algebra.smul_def, mul_assoc]
          rfl
        rw [this]
        exact B.mul_mem (hA a) hu
    exact h2 _ h1
  · intro h x hx
    have h1 : σ (x : E) ∈ Submodule.span A {y : Ω | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [← hds, Submodule.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    have : σ (x : E) * t = (a : Ω) * ((ds : Ω) * t) := by
      rw [← ha, Algebra.smul_def, mul_assoc]
      rfl
    rw [this]
    exact B.mul_mem (hA a) h

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem inv_natCast_mem {p : ℕ} (hp : p.Prime) {q : Cpt 𝔐.ξ} (hq : InFibre 𝔐.ξ p q) (b : ℕ) (hb : ¬ p ∣ b) :
    ((b : Ω))⁻¹ ∈ regAt 𝔐.ξ q := by
  have hZ : OverZp 𝔐 p q := by
    intro r hr hrq
    by_contra hne
    have hloc : IsLocalRing (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) :=
      IsLocalRing.of_surjective' (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict
        (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict_surjective
    have key : ∀ m : ℕ, GlobalTheory.CompanionTheory.Ar.InFibre 𝔐.ξ m q → ¬ IsUnit ((m : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)) := by
      intro m hm hu
      apply hm
      obtain ⟨u, hu'⟩ := hu
      have h1 : (m : Ω) * (((u⁻¹ : (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)ˣ) : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) : Ω) = 1 := by
        have h2 := congrArg (fun x : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
        simpa [hu'] using h2
      have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
      refine ⟨h0, natCast_mem _ m, ?_⟩
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact SetLike.coe_mem _
    have hcop : Nat.Coprime r p := (Nat.coprime_primes hr hp).2 hne
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q))
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
    · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)
  induction b using Nat.recOnMul with
  | zero => exact absurd (dvd_zero p) hb
  | one => simpa using (regAt 𝔐.ξ q).one_mem
  | prime r hr =>
    have hne : r ≠ p := by
      rintro rfl
      exact hb dvd_rfl
    have hu : unitAt 𝔐.ξ q (r : Ω) := by
      by_contra hnot
      exact hne (hZ r hr hnot)
    exact hu.2.2
  | mul a b ha hb' =>
    have h1 : ¬ p ∣ a := fun h => hb (h.mul_right b)
    have h2 : ¬ p ∣ b := fun h => hb (h.mul_left a)
    rw [Nat.cast_mul, mul_inv]
    exact (regAt 𝔐.ξ q).mul_mem (ha h1) (hb' h2)

theorem chart_mem_regAt {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {s : ∀ k, J k} {q : Cpt 𝔐.ξ} (hs : InChart 𝔐.ξ (mseg y) s q) (hq : InFibre 𝔐.ξ p q)
    (a : chartRing o (mseg y) s) : (a : Ω) ∈ regAt 𝔐.ξ q := by
  obtain ⟨a, ha⟩ := a
  change a ∈ regAt 𝔐.ξ q
  change a ∈ Algebra.adjoin o _ at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hs.2 j
  | algebraMap r =>
    obtain ⟨u, b, hb, h⟩ := (ho _).1 ⟨r, rfl⟩
    rw [h, div_eq_mul_inv]
    exact (regAt 𝔐.ξ q).mul_mem (intCast_mem _ u) (inv_natCast_mem 𝔐 hp hq b hb)
  | add u v _ _ hu hv => exact (regAt 𝔐.ξ q).add_mem hu hv
  | mul u v _ _ hu hv => exact (regAt 𝔐.ξ q).mul_mem hu hv

end Model

theorem mem_V_inl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (ds : chartRing o (mseg y) s.1), GeneratesDiff σ ds → ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inl τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho Dc hD hpS τ σ hσ s ds hds q hs hq e
  have hp : p.Prime := Fact.out
  have hZ : OverZp 𝔐 p q := by
    intro r hr hrq
    by_contra hne
    have hloc : IsLocalRing (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) :=
      IsLocalRing.of_surjective' (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict
        (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict_surjective
    have key : ∀ m : ℕ, GlobalTheory.CompanionTheory.Ar.InFibre 𝔐.ξ m q → ¬ IsUnit ((m : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)) := by
      intro m hm hu
      apply hm
      obtain ⟨u, hu'⟩ := hu
      have h1 : (m : Ω) * (((u⁻¹ : (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)ˣ) : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) : Ω) = 1 := by
        have h2 := congrArg (fun x : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
        simpa [hu'] using h2
      have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
      refine ⟨h0, natCast_mem _ m, ?_⟩
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact SetLike.coe_mem _
    have hcop : Nat.Coprime r p := (Nat.coprime_primes hr hp).2 hne
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q))
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
    · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)
  have hV : 𝔐.V (Sum.inl τ) q = 𝔐.HT p (Sum.inl τ) q :=
    Lat.patch_of_unique S _ _ hpS hq fun p' hp' h =>
      hZ p' (𝔐.S_prime p' hp') h
  have hE : e ∈ GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ (𝔐.emb (Sum.inl τ)) ↔ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ := by
    rw [LatBasic.mem_eigSp]
    simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hσ]
  have hA := chart_mem_regAt 𝔐 hp ho hs hq
  have hO : omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om' : Set (Module.Dual Ω 𝔐.Li)) :=
    hD.om'_loc s q hs hq
  rw [hV]
  change e ∈ 𝔐.M.htW _ _ _ _ _ q ↔ _
  rw [mem_htW_iff_forms, hE]
  refine and_congr_right fun _ => ?_
  have hT : ∀ w : Module.Dual Ω 𝔐.Li,
      (∀ d ∈ differentIdeal ℤ (𝓞 E), 𝔐.emb (Sum.inl τ) d * w e ∈ regAt 𝔐.ξ q) ↔
        (ds : Ω) * w e ∈ regAt 𝔐.ξ q := fun w => by
    rw [← forall_different_iff _ _ hA σ ds hds]
    simp only [hσ]
  constructor
  · intro h w hw
    have hw' : w ∈ omP 𝔐 p q := by
      rw [hO]
      exact Submodule.subset_span hw
    exact (hT w).1 (h w hw')
  · intro h w hw
    rw [show 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q = omP 𝔐 p q from rfl, hO] at hw
    refine (hT w).2 ?_
    induction hw using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simpa using (regAt 𝔐.ξ q).zero_mem
    | add u v _ _ hu hv =>
      have : (ds : Ω) * (u + v) e = (ds : Ω) * u e + (ds : Ω) * v e := by
        rw [LinearMap.add_apply, mul_add]
      rw [this]
      exact (regAt 𝔐.ξ q).add_mem hu hv
    | smul a u _ hu =>
      have : (ds : Ω) * (a • u) e = (a : Ω) * ((ds : Ω) * u e) := by
        change (ds : Ω) * ((a : Ω) • u) e = _
        rw [LinearMap.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact (regAt 𝔐.ξ q).mul_mem a.2 hu

end GlobalTheory.CompanionTheory.Ar.Flat.HTStalk
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentResidueIntegralityStatement
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_residue_integrality : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (ds : chartRing o (mseg y) s.1), GeneratesDiff σ ds → ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inl τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) (regAt 𝔐.ξ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HTStalk.mem_V_inl_iff | exact GlobalTheory.CompanionTheory.Ar.Flat.HTStalk.mem_V_inl_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HTStalk.mem_V_inl_iff <;> assumption)
end
end

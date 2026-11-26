module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicNormTransitionDetOne
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XCkFlagSum
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticePermuted

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleFrames
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleFrames
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.CkFlagSum

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B B' : ChartBundle O (mseg x) N V), SameGeneric O x B B' → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ), IsFlagFrame x B w b → IsFlagFrame x B' w' b' → (∀ i j : Fin N, i < j → w.repr (w' i) j = 0) → ∀ A A' : Fin N → ChartBundle O (mseg x) 1 Ω, (∀ i, IsLine O x 1 (b i) (A i).lat ∧ IsLine O x (w.repr (w' i) i) (b' i) (A' i).lat) → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N B B' k L Q = ∑ i, ck O x d 1 (A i) (A' i) k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM N V _ _ B B' hS w w' b b' hF hF' hw A A' hA k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hK, hW⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
  have hW' : GroundTheory.Heights₂.Heights.NumbersDVR.IsModelOver (pointIdeal O x) d := hW
  obtain ⟨hG, f, g, hP⟩ :=
    GlobalTheory.T.same_generic_flag_comparison O Ω K ι x ϖ hϖ d hW' N V B B' hS w w' b b' hF hF' hw
  have h1 := (GlobalTheory.T.chern_class_on_flag_pair O ϖ hϖ Ω K ι x d hK hW' N V B B' hG w w' b b' f g hP).1 k hk1 hk2
    (psumExpansion N k) (isPairExpansion_psum N k) q L Q hQ
  have h2 : ∀ i, ck O x d 1 (A i) (A' i) k L Q = _ := fun i =>
    (GlobalTheory.T.line_bundle_model_degree O Ω K ι x ϖ hϖ d hM (A i) (A' i) 1 (w.repr (w' i) i) (b i) (b' i)
      (hA i).1 (hA i).2 (f i) (g i) (hP.vertical i)
      (by rw [mul_one, mul_comm]; exact hP.generic i)).2 k hk1 hk2 q L Q hQ
  refine h1.trans ?_
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [PositivityTheory.Xgn.A_ck_flag_sum.pairNum_psum, Finset.mul_sum]

end GlobalTheory.CompanionTheory.Ar.CkFlagSum
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleFramesStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ck_eq_sum_ck_line_summands : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (B B' : ChartBundle O (mseg x) N V), SameGeneric O x B B' → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ), IsFlagFrame x B w b → IsFlagFrame x B' w' b' → (∀ i j : Fin N, i < j → w.repr (w' i) j = 0) → ∀ A A' : Fin N → ChartBundle O (mseg x) 1 Ω, (∀ i, IsLine O x 1 (b i) (A i).lat ∧ IsLine O x (w.repr (w' i) i) (b' i) (A' i).lat) → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N B B' k L Q = ∑ i, ck O x d 1 (A i) (A' i) k L Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CkFlagSum.main | exact GlobalTheory.CompanionTheory.Ar.CkFlagSum.main | (intros; apply GlobalTheory.CompanionTheory.Ar.CkFlagSum.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeCoordinateGenerator
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeCoordinateGenerator
namespace GlobalTheory.CompanionTheory.Ar.Num.HhGraded

open GlobalTheory.CompanionTheory.Ar.Num

theorem mem_dotDual_iff {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ}
    (L : AddSubgroup (Fin n → Ω)) (v : Fin n → Ω) : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem mem_annSub_iff {Ω : Type} [Field Ω] {n k : ℕ} (l : Fin n → Ω) :
    l ∈ annSub Ω n k ↔ ∀ j : Fin n, (j : ℕ) < k → l j = 0 := by
  simp [annSub, Submodule.mem_pi]

theorem single_mem_annSub {Ω : Type} [Field Ω] {n k : ℕ} (j : Fin n) (hj : k ≤ (j : ℕ)) :
    (Pi.single j 1 : Fin n → Ω) ∈ annSub Ω n k := by
  rw [mem_annSub_iff]
  intro m hm
  have : m ≠ j := fun h => by subst h; omega
  simp [Pi.single_apply, this]

theorem map_eq_sum {Ω : Type} [Field Ω] {n : ℕ} (ρ : (Fin n → Ω) →ₗ[Ω] (Fin n → Ω)) (l : Fin n → Ω) :
    ρ l = ∑ j, l j • ρ (Pi.single j 1) := by
  have h : l = ∑ j, l j • (Pi.single j 1 : Fin n → Ω) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [h, map_sum]
  simp only [map_smul]

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (n : ℕ)
    (L : AddSubgroup (Fin n → Ω)), LocFree R n L → (∀ i, Summand L (annSub Ω n i)) →
    ∀ (i : Fin n) (u : Ω), u ≠ 0 →
    (∀ c, c ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) ↔
      ∃ a ∈ R, c = a * u) →
    ∀ t : Ω, (∃ v ∈ dotDual R L, (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  intro o Ω _ _ _ R n L _ hS i u hu hc t
  constructor
  · rintro ⟨v, hv, hz, rfl⟩
    obtain ⟨l, hl, hlu⟩ := (hc u).2 ⟨1, R.one_mem, (one_mul u).symm⟩
    have hlL : l ∈ L := (AddSubgroup.mem_inf.1 hl).1
    have hlA : l ∈ annSub Ω n i := (AddSubgroup.mem_inf.1 hl).2
    have hlu' : l i = u := hlu
    have h2 : l ⬝ᵥ v = u * v i := by
      rw [dotProduct, Finset.sum_eq_single i, hlu']
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with h | h
        · rw [(mem_annSub_iff l).1 hlA j h, zero_mul]
        · rw [hz j h, mul_zero]
      · simp
    refine ⟨u * v i, ?_, ?_⟩
    · rw [← h2]
      exact (mem_dotDual_iff R L v).1 hv l hlL
    · field_simp
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ρ, hρU, hρid, hρL⟩ := hS i
    have hfix : ∀ j : Fin n, i ≤ j → ρ (Pi.single j 1) = Pi.single j 1 := fun j hj =>
      hρid _ (single_mem_annSub j hj)
    refine ⟨fun j => (a * u⁻¹) * ρ (Pi.single j 1) i, ?_, ?_, ?_⟩
    · rw [mem_dotDual_iff]
      intro l hl
      have key : l ⬝ᵥ (fun j => (a * u⁻¹) * ρ (Pi.single j 1) i) = (a * u⁻¹) * ρ l i := by
        rw [map_eq_sum ρ l, dotProduct, Finset.sum_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      have hl' : ρ l i ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map
          (Pi.evalAddMonoidHom (fun _ => Ω) i) :=
        ⟨ρ l, AddSubgroup.mem_inf.2 ⟨hρL l hl, hρU l⟩, rfl⟩
      obtain ⟨b, hb, hbe⟩ := (hc _).1 hl'
      have h3 : a * u⁻¹ * (b * u) = a * b := by field_simp
      rw [key, hbe, h3]
      exact R.mul_mem ha hb
    · intro j hj
      have hne : i ≠ j := ne_of_lt hj
      simp only [hfix j hj.le, Pi.single_apply, hne, if_false, mul_zero]
    · simp only [hfix i le_rfl, Pi.single_eq_same, mul_one]

end GlobalTheory.CompanionTheory.Ar.Num.HhGraded
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeCoordinateGeneratorStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_coordinate_generator : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (n : ℕ) (L : AddSubgroup (Fin n → Ω)), LocFree R n L → (∀ i, Summand L (annSub Ω n i)) → ∀ (i : Fin n) (u : Ω), u ≠ 0 → (∀ c, c ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) ↔ ∃ a ∈ R, c = a * u) → ∀ t : Ω, (∃ v ∈ dotDual R L, (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main | exact GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeCharacter
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.RelH

section Chart

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat' (R : Subalgebra o Ω) {n : ℕ} {v : Fin n → Ω} :
    v ∈ stdLat R (Fin n) ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_dotDual' (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} {v : Fin n → Ω} :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

theorem std_le_dual (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)}
    (hL : L ≤ stdLat R (Fin n)) : stdLat R (Fin n) ≤ dotDual R L := by
  intro v hv
  refine (mem_dotDual' R).2 fun l hl => ?_
  have h1 := (mem_stdLat' R).1 (hL hl)
  have h2 := (mem_stdLat' R).1 hv
  exact sum_mem fun i _ => mul_mem (h1 i) (h2 i)

theorem smul_mem_of_dual (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} {w : Ω}
    (hL : mulLat w (stdLat R (Fin n)) ≤ L) {v : Fin n → Ω} (hv : v ∈ dotDual R L) :
    w • v ∈ stdLat R (Fin n) := by
  refine (mem_stdLat' R).2 fun i => ?_
  have h1 : w • (Pi.single i 1 : Fin n → Ω) ∈ L := by
    refine hL ⟨Pi.single i 1, (mem_stdLat' R).2 fun j => ?_, rfl⟩
    by_cases h : j = i
    · subst h; simpa using one_mem R
    · simpa [h] using zero_mem R
  have h2 := (mem_dotDual' R).1 hv _ h1
  simpa [dotProduct, Pi.single_apply] using h2

theorem coord_mem_of_le (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)}
    (hL : L ≤ stdLat R (Fin n)) (i : Fin n) {t : Ω}
    (ht : t ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i)) :
    t ∈ R := by
  obtain ⟨v, hv, rfl⟩ := ht
  exact (mem_stdLat' R).1 (hL hv.1) i

theorem mul_mem_coord (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} {w : Ω}
    (hL : mulLat w (stdLat R (Fin n)) ≤ L) (i : Fin n) {a : Ω} (ha : a ∈ R) :
    w * a ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) := by
  refine ⟨w • (Pi.single i a : Fin n → Ω), ⟨hL ⟨Pi.single i a, (mem_stdLat' R).2 fun j => ?_, rfl⟩, ?_⟩, ?_⟩
  · by_cases h : j = i
    · subst h; simpa using ha
    · simpa [h] using zero_mem R
  · show _ ∈ annSub Ω n i
    simp only [annSub, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]
    intro j hj
    have : j ≠ i := fun h => by subst h; exact lt_irrefl _ hj
    simp [this]
  · simp

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

theorem chart_facts (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω)
    (φ : Equiv.Perm Sg) (hcd : CharData R p w χ) (hb : D.Base R p w) (h1 : D.Good₁ R p χ)
    (h2 : D.Good₂ R p χ) (hf : D.Facts R p w χ φ) (τ : Sg) :
    stdLat R (Fin n) ≤ D.hh R p (χ τ) ∧ (∀ v ∈ D.hh R p (χ τ), w • v ∈ stdLat R (Fin n)) ∧
      ∀ i : Fin n, (∀ t ∈ D.xId (χ τ) i, t ∈ R) ∧ (∀ a ∈ R, w * a ∈ D.xId (χ τ) i) ∧
        ∀ u : Ω, u ≠ 0 → (∀ c, c ∈ D.xId (χ τ) i ↔ ∃ a ∈ R, c = a * u) →
          ∀ t, (∃ v ∈ D.hh R p (χ τ), (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  obtain ⟨hfree, -⟩ := GlobalTheory.T.lattice_good_base_change D R p w χ hcd hb h1
  obtain ⟨hLF, -, hle, -⟩ := hfree τ
  have hle' : mulLat w (stdLat R _) ≤ D.af R p (χ τ) := hf.le_af τ
  refine ⟨std_le_dual R hle, fun v hv => smul_mem_of_dual R hle' hv, fun i => ⟨?_, ?_, ?_⟩⟩
  · intro t ht
    rw [← hf.dx τ i] at ht
    exact coord_mem_of_le R hle i ht
  · intro a ha
    rw [← hf.dx τ i]
    exact mul_mem_coord R hle' i ha
  · intro u hu hc t
    refine GlobalTheory.T.dual_lattice_coordinate_generator R n (D.af R p (χ τ)) hLF (h2.ann τ) i u hu (fun c => ?_) t
    have := hc c
    rw [← hf.dx τ i] at this
    exact this

end Chart

section Model

variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] {ι : K → Type}

theorem coord_ne_zero {x : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : mseg x c ≠ 0) (k : K) :
    x ⟨k, c k⟩ ≠ 0 := fun h => hc (Finset.prod_eq_zero (Finset.mem_univ k) h)

theorem chartMon_ne_zero' {x : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : mseg x c ≠ 0) (b : K → ℤ) :
    chartMon x c b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (coord_ne_zero hc k)

theorem chartMon_neg' (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (b : K → ℤ) :
    chartMon x c (-b) = (chartMon x c b)⁻¹ := by
  simp [chartMon, Finset.prod_inv_distrib, zpow_neg]

theorem chartMon_zero' (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : chartMon x c (0 : K → ℤ) = 1 := by
  simp [chartMon]

theorem inv_line {u : Ω} (hu : u ≠ 0) (v r m : Ω) :
    u⁻¹ * v = r * (u⁻¹ * m) ↔ v = r * (1 * m) := by
  rw [show r * (u⁻¹ * m) = u⁻¹ * (r * (1 * m)) by ring, mul_right_inj' (inv_ne_zero hu)]

theorem inv_line' {u : Ω} (hu : u ≠ 0) (v r m : Ω) :
    u⁻¹ * v = r * (1 * m) ↔ v = r * (u * m) := by
  rw [show r * (u * m) = u * (r * (1 * m)) by ring, inv_mul_eq_iff_eq_mul₀ hu]

end Model

theorem relH_main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Xb : Sg → Fin n → ChartBundle O (mseg x) 1 Ω) (T : ChartBundle O (mseg x) 1 Ω), (∀ τ i c, mseg x c ≠ 0 → (Xb τ i).lat c = (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → IsLine O x 1 0 T.lat → ∀ τ (H Tn : ChartBundle O (mseg x) n (Fin n → Ω)), (∀ c, mseg x c ≠ 0 → H.lat c = (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) ∧ Tn.lat c = stdLat (chartRing O (mseg x) c) (Fin n)) → SameGeneric O x H Tn ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d n H Tn k L Q = (-1) ^ k * ∑ i, ck O x d 1 (Xb τ i) T k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hmodel F _ _ _ n Sg _ r s p hp w χ φ D hfam hg1 hg2 hfacts hline
    Xb T hXb hT τ H Tn hHT
  have hinj : ∀ a : O, algebraMap O Ω a = 0 → a = 0 := by
    intro a ha
    have h1 : (MvPolynomial.C a : MvPolynomial (Σ k, ι k) O) ∈ mcIdeal O x := by
      show GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (MvPolynomial.C a) = 0
      have h2 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (MvPolynomial.C a) =
          algebraMap O (MvPolynomial K Ω) a :=
        (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x).commutes a
      rw [h2, MvPolynomial.algebraMap_apply, ha, map_zero]
    have h2 : a ∈ ((mcIdeal O x).comap (MvPolynomial.C : O →+* MvPolynomial (Σ k, ι k) O)) := h1
    rw [hmodel.2.2.1] at h2
    simpa using h2
  obtain ⟨hp0, ⟨u0, hu0, hwu⟩, -, h01, hχ⟩ := hfam.char
  have hp2 : 2 ≤ p := hp.two_le
  have hpΩ : (p : Ω) ≠ 0 := by
    intro h
    exact hp0 (hinj _ (by simpa using h))
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hwu
    rcases mul_eq_zero.1 hwu.symm with h | h
    · exact hu0.ne_zero h
    · exact hp0 h
  obtain ⟨b, hb⟩ : ∃ b : O, (p : O) = b * w := by
    obtain ⟨v, rfl⟩ := hu0
    refine ⟨↑v⁻¹ * w ^ (p - 2), ?_⟩
    have h1 : w ^ (p - 1) = w ^ (p - 2) * w := by
      rw [← pow_succ]
      congr 1
      omega
    calc (p : O) = ↑v⁻¹ * (↑v * (p : O)) := by simp
      _ = _ := by rw [← hwu, h1, mul_assoc]
  have hcd : ∀ c, CharData (chartRing O (mseg x) c) p (algebraMap O Ω w)
      (fun τ a => algebraMap O Ω (χ τ a)) := fun c =>
    ⟨hpΩ, Subalgebra.algebraMap_mem _ w,
      ⟨algebraMap O Ω b, Subalgebra.algebraMap_mem _ b, by rw [← map_mul, ← hb, map_natCast]⟩, h01,
      fun τ => ⟨by simp [(hχ τ).1], by simp [(hχ τ).2], fun a => Subalgebra.algebraMap_mem _ _⟩⟩
  have CF : ∀ c, mseg x c ≠ 0 →
      stdLat (chartRing O (mseg x) c) (Fin n) ≤ H.lat c ∧
      (∀ v ∈ H.lat c, algebraMap O Ω w • v ∈ stdLat (chartRing O (mseg x) c) (Fin n)) ∧
      ∀ i : Fin n, (∀ t ∈ (D c).xId (fun a => algebraMap O Ω (χ τ a)) i, t ∈ chartRing O (mseg x) c) ∧
        (∀ a ∈ chartRing O (mseg x) c,
          algebraMap O Ω w * a ∈ (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧
        ∀ u : Ω, u ≠ 0 → (∀ c', c' ∈ (D c).xId (fun a => algebraMap O Ω (χ τ a)) i ↔
            ∃ a ∈ chartRing O (mseg x) c, c' = a * u) →
          ∀ t, (∃ v ∈ H.lat c, (∀ j, i < j → v j = 0) ∧ v i = t) ↔
            ∃ a ∈ chartRing O (mseg x) c, t = a * u⁻¹ := by
    intro c hc
    rw [(hHT c hc).1]
    exact chart_facts (D c) (chartRing O (mseg x) c) p _ _ φ (hcd c) (hfam.base c hc) (hg1 c hc)
      (hg2 c hc) (hfacts c hc) τ
  choose u a hu hl using hline
  have hgR : ∀ (i : Fin n) c, mseg x c ≠ 0 → u τ i * chartMon x c (a τ i) ∈ chartRing O (mseg x) c ∧
      ∃ e ∈ chartRing O (mseg x) c, algebraMap O Ω w = e * (u τ i * chartMon x c (a τ i)) := by
    intro i c hc
    refine ⟨((CF c hc).2.2 i).1 _ ((hl τ i c hc _).2 ⟨1, one_mem _, by simp⟩), ?_⟩
    have h1 := ((CF c hc).2.2 i).2.1 1 (one_mem _)
    rw [mul_one] at h1
    exact (hl τ i c hc _).1 h1
  have hgne : ∀ (i : Fin n) c, mseg x c ≠ 0 → u τ i * chartMon x c (a τ i) ≠ 0 := fun i c hc =>
    mul_ne_zero (hu τ i) (chartMon_ne_zero' hc _)
  have hgm : ∀ (i : Fin n) c, mseg x c ≠ 0 →
      (u τ i * chartMon x c (a τ i)) * chartMon x c (-a τ i) = u τ i := by
    intro i c hc
    rw [chartMon_neg', mul_assoc, mul_inv_cancel₀ (chartMon_ne_zero' hc _), mul_one]
  have hSG : SameGeneric O x H Tn := by
    intro c hc
    refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
    · rw [(hHT c hc).2]
      exact (CF c hc).2.1 v hv
    · rw [map_one, one_smul]
      rw [(hHT c hc).2] at hv
      exact (CF c hc).1 hv
  let wB : Module.Basis (Fin n) Ω (Fin n → Ω) :=
    (Pi.basisFun Ω (Fin n)).unitsSMul fun i => Units.mk0 (u τ i)⁻¹ (inv_ne_zero (hu τ i))
  have hrepr : ∀ (v : Fin n → Ω) i, wB.repr v i = u τ i * v i := by
    intro v i
    simp [wB, Units.smul_def]
  have hflagH : IsFlagFrame x H wB (fun i => -a τ i) := by
    refine ⟨fun c hc i => ?_⟩
    have hc' : mseg x c ≠ 0 := hc
    have key := ((CF c hc').2.2 i).2.2 _ (hgne i c hc') (hl τ i c hc')
    ext z
    constructor
    · rintro ⟨v, hv, hz, rfl⟩
      have h0 : ∀ j, i < j → v j = 0 := fun j hj => by
        have h1 := hz j hj
        rw [hrepr] at h1
        exact (mul_eq_zero.1 h1).resolve_left (hu τ j)
      obtain ⟨e, he, hev⟩ := (key (v i)).1 ⟨v, hv, h0, rfl⟩
      refine ⟨e, he, ?_⟩
      show wB.repr v i = e * chartMon x c (-a τ i)
      rw [hrepr, hev, chartMon_neg', mul_inv]
      field_simp [hu τ i]
    · rintro ⟨e, he, rfl⟩
      obtain ⟨v, hv, h0, hvi⟩ := (key (e * (u τ i * chartMon x c (a τ i))⁻¹)).2 ⟨e, he, rfl⟩
      refine ⟨v, hv, fun j hj => by rw [hrepr, h0 j hj, mul_zero], ?_⟩
      show wB.repr v i = e * chartMon x c (-a τ i)
      rw [hrepr, hvi, chartMon_neg', mul_inv]
      field_simp [hu τ i]
  have hflagT : IsFlagFrame x Tn (Pi.basisFun Ω (Fin n)) 0 := by
    refine ⟨fun c hc i => ?_⟩
    have hc' : mseg x c ≠ 0 := hc
    ext z
    constructor
    · rintro ⟨v, hv, -, rfl⟩
      rw [(hHT c hc').2] at hv
      refine ⟨v i, (mem_stdLat' _).1 hv i, ?_⟩
      simp
    · rintro ⟨e, he, rfl⟩
      refine ⟨Pi.single i e, ?_, fun j hj => ?_, ?_⟩
      · rw [(hHT c hc').2]
        refine (mem_stdLat' _).2 fun j => ?_
        by_cases h : j = i
        · subst h
          have he' : e ∈ chartRing O (mseg x) c := he
          simpa using he'
        · simpa [h] using zero_mem (chartRing O (mseg x) c)
      · simp [(ne_of_lt hj).symm]
      · simp
  have htri : ∀ i j : Fin n, i < j → wB.repr (Pi.basisFun Ω (Fin n) i) j = 0 := by
    intro i j hij
    rw [hrepr]
    simp [(ne_of_lt hij).symm]
  have ops := GlobalTheory.T.chart_bundle_product O Ω K ι x
  have e1 : ∀ i, ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x 1 (-a τ i) A.lat :=
    fun i => ops.2.2.1 1 _ one_ne_zero
  have e2 : ∀ i, ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x (u τ i) 0 A.lat :=
    fun i => ops.2.2.1 _ _ (hu τ i)
  have e3 : ∀ i, ∃ A : ChartBundle O (mseg x) 1 Ω,
      IsLine O x (u τ i ^ (-1 : ℤ)) ((-1 : ℤ) • a τ i) A.lat :=
    fun i => ops.2.2.1 _ _ (zpow_ne_zero _ (hu τ i))
  choose A1 hA1 using e1
  choose A2 hA2 using e2
  choose A3 hA3 using e3
  have hlX : ∀ i, IsLine O x (u τ i) (a τ i) (Xb τ i).lat := by
    intro i c hc v
    rw [hXb τ i c hc]
    exact hl τ i c hc v
  have hSG12 : ∀ i, SameGeneric O x (A1 i) (A2 i) := by
    intro i c hc
    obtain ⟨hg, e, he, hwe⟩ := hgR i c hc
    refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
    · obtain ⟨ρ, hρ, rfl⟩ := (hA1 i c hc v).1 hv
      refine (hA2 i c hc _).2 ⟨ρ * e, mul_mem hρ he, ?_⟩
      rw [chartMon_zero', smul_eq_mul, hwe]
      have h1 := hgm i c hc
      calc e * (u τ i * chartMon x c (a τ i)) * (ρ * (1 * chartMon x c (-a τ i)))
          = ρ * e * ((u τ i * chartMon x c (a τ i)) * chartMon x c (-a τ i)) := by ring
        _ = _ := by rw [h1, mul_one]
    · obtain ⟨ρ, hρ, rfl⟩ := (hA2 i c hc v).1 hv
      rw [map_one, one_smul]
      refine (hA1 i c hc _).2 ⟨ρ * (u τ i * chartMon x c (a τ i)), mul_mem hρ hg, ?_⟩
      rw [chartMon_zero', one_mul, mul_one, mul_assoc, hgm i c hc]
  have hSGX : ∀ i, SameGeneric O x (Xb τ i) T := by
    intro i c hc
    obtain ⟨hg, e, he, hwe⟩ := hgR i c hc
    refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨w, hw0, ?_⟩⟩
    · obtain ⟨ρ, hρ, rfl⟩ := (hlX i c hc v).1 hv
      rw [map_one, one_smul]
      refine (hT c hc _).2 ⟨ρ * (u τ i * chartMon x c (a τ i)), mul_mem hρ hg, ?_⟩
      rw [chartMon_zero']
      ring
    · obtain ⟨ρ, hρ, rfl⟩ := (hT c hc v).1 hv
      refine (hlX i c hc _).2 ⟨ρ * e, mul_mem hρ he, ?_⟩
      rw [chartMon_zero', smul_eq_mul, hwe]
      ring
  refine ⟨hSG, fun k hk1 hk2 q L Q hQ => ?_⟩
  have hsum := GlobalTheory.T.ck_eq_sum_ck_line_summands O Ω K ι x d hmodel n (Fin n → Ω) H Tn hSG wB (Pi.basisFun Ω (Fin n))
    (fun i => -a τ i) 0 hflagH hflagT htri A1 A2
    (fun i => ⟨hA1 i, by
      have h1 : wB.repr (Pi.basisFun Ω (Fin n) i) i = u τ i := by
        rw [hrepr]
        simp
      rw [h1]
      exact hA2 i⟩) k hk1 hk2 q L Q hQ
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hP := (GlobalTheory.T.line_bundle_chart_generic_comparison O Ω K ι x d hmodel (Xb τ i) T (A3 i) (u τ i) (a τ i) (-1) (hu τ i) (hlX i)
    hT (hSGX i) (hA3 i)).2 k hk1 hk2 q L Q hQ
  have hTr := (GlobalTheory.T.same_generic_linear_equiv O Ω K ι x d hmodel 1 Ω Ω
    (LinearEquiv.smulOfNeZero Ω Ω (u τ i)⁻¹ (inv_ne_zero (hu τ i))) (A1 i) (A2 i) (A3 i) T (hSG12 i)
    (fun c hc v => ?_)).1 k hk1 hk2 q L Q hQ
  · rw [← hTr, hP]
  · have he : (LinearEquiv.smulOfNeZero Ω Ω (u τ i)⁻¹ (inv_ne_zero (hu τ i))) v = (u τ i)⁻¹ * v := rfl
    rw [he]
    constructor
    · rw [hA3 i c hc, hA1 i c hc]
      simp only [zpow_neg_one, neg_smul, one_smul, inv_line (hu τ i)]
    · rw [hT c hc, hA2 i c hc]
      simp only [inv_line' (hu τ i)]

end GlobalTheory.CompanionTheory.Ar.Num.RelH
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeCharacterStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_over_mod_p_lattice_character : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Xb : Sg → Fin n → ChartBundle O (mseg x) 1 Ω) (T : ChartBundle O (mseg x) 1 Ω), (∀ τ i c, mseg x c ≠ 0 → (Xb τ i).lat c = (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → IsLine O x 1 0 T.lat → ∀ τ (H Tn : ChartBundle O (mseg x) n (Fin n → Ω)), (∀ c, mseg x c ≠ 0 → H.lat c = (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) ∧ Tn.lat c = stdLat (chartRing O (mseg x) c) (Fin n)) → SameGeneric O x H Tn ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d n H Tn k L Q = (-1) ^ k * ∑ i, ck O x d 1 (Xb τ i) T k L Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RelH.relH_main | exact GlobalTheory.CompanionTheory.Ar.Num.RelH.relH_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RelH.relH_main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InjectiveModPLatticeCharacterBound
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InjectiveModPLatticeCharacterBound
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.RelSeq

section Lattices

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat (R : Subalgebra o Ω) {κ : Type} (v : κ → Ω) :
    v ∈ stdLat R κ ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (v : Fin m → Ω) :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

theorem af_le_std (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (hB : D.Base R p w)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : D.af R p χ ≤ stdLat R (Fin n) := by
  have hl1 : D.l1 R p ≤ stdLat R _ := by
    refine sup_le hB.M_le ?_
    rintro _ ⟨f, hf, rfl⟩
    refine (mem_stdLat R _).2 fun i => ?_
    have := (mem_stdLat R f).1 hf i
    simpa using R.mul_mem (natCast_mem R p) this
  intro l hl
  refine (mem_stdLat R l).2 fun i => ?_
  have h := (mem_stdLat R _).1 (hl1 hl) (Pi.single i 1)
  have e : (linMap n χ) l (Pi.single i 1) = l i := by
    simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [h1]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, h0]
    · simp
  have e' : (linMap n χ).toAddMonoidHom l (Pi.single i 1) = l i := e
  rwa [e'] at h

theorem std_le_hh (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (hB : D.Base R p w)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : stdLat R (Fin n) ≤ D.hh R p χ := by
  intro v hv
  refine (mem_dotDual R _ v).2 fun l hl => ?_
  have hl' := (mem_stdLat R l).1 (af_le_std D R p w hB χ h0 h1 hl)
  have hv' := (mem_stdLat R v).1 hv
  exact sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std_of_mem_hh (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω)
    (χ : F → Ω) (h : mulLat w (stdLat R _) ≤ D.af R p χ) {b : Fin n → Ω} (hb : b ∈ D.hh R p χ) :
    w • b ∈ stdLat R (Fin n) := by
  refine (mem_stdLat R _).2 fun i => ?_
  have hi : (Pi.single i 1 : Fin n → Ω) ∈ stdLat R (Fin n) := by
    refine (mem_stdLat R _).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp [one_mem]
    · simp [Pi.single_eq_of_ne hj, zero_mem]
  have hm : w • (Pi.single i 1 : Fin n → Ω) ∈ D.af R p χ := h ⟨_, hi, rfl⟩
  have := (mem_dotDual R _ b).1 hb _ hm
  simpa [smul_dotProduct, single_one_dotProduct] using this

theorem mem_kerH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (v : Fin (r τ) → Ω) :
    v ∈ D.kerH R p τ χ ↔ ∃ b, (v, b) ∈ D.Gam τ ∧ b ∈ D.hh R p χ := by
  simp [LieLatticeData.kerH, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

theorem mem_imH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (c : Fin (s τ) → Ω) :
    c ∈ D.imH R p τ χ ↔ ∃ b, (b, c) ∈ D.Del τ ∧ b ∈ D.hh R p χ := by
  simp [LieLatticeData.imH, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

def gamH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω) :
    AddSubgroup ((Fin (r τ) → Ω) × (Fin n → Ω)) :=
  D.Gam τ ⊓ (⊤ : AddSubgroup (Fin (r τ) → Ω)).prod (D.hh R p χ)

def delH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω) :
    AddSubgroup ((Fin n → Ω) × (Fin (s τ) → Ω)) :=
  D.Del τ ⊓ (D.hh R p χ).prod (⊤ : AddSubgroup (Fin (s τ) → Ω))

theorem mem_gamH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (a : Fin (r τ) → Ω) (b : Fin n → Ω) :
    (a, b) ∈ gamH D R p τ χ ↔ (a, b) ∈ D.Gam τ ∧ b ∈ D.hh R p χ := by
  simp [gamH, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

theorem mem_delH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (b : Fin n → Ω) (c : Fin (s τ) → Ω) :
    (b, c) ∈ delH D R p τ χ ↔ (b, c) ∈ D.Del τ ∧ b ∈ D.hh R p χ := by
  simp [delH, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

end Lattices

section Families

variable (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem isLatFamily_inf_prod_right (x : (Σ k, ι k) → Ω) {G : (∀ k, ι k) → AddSubgroup (V × V₁)}
    {H : (∀ k, ι k) → AddSubgroup V₁} (hG : IsLatFamily o x G) (hH : IsLatFamily o x H) :
    IsLatFamily o x fun c => G c ⊓ (⊤ : AddSubgroup V).prod (H c) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).2
    exact ⟨hG.1 c hc a ha v hv.1, AddSubgroup.mem_prod.2 ⟨trivial, hH.1 c hc a ha _ h2⟩⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).2
    obtain ⟨m₁, h₁⟩ := hG.2 c t hc ht v hv.1
    obtain ⟨m₂, h₂⟩ := hH.2 c t hc ht _ h2
    have hq := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c
    refine ⟨m₂ + m₁, ?_, AddSubgroup.mem_prod.2 ⟨trivial, ?_⟩⟩
    · have := hG.1 t ht _ (pow_mem hq m₂) _ h₁
      rwa [smul_smul, ← pow_add] at this
    · have := hH.1 t ht _ (pow_mem hq m₁) _ h₂
      rw [smul_smul, ← pow_add, add_comm] at this
      simpa using this

theorem isLatFamily_inf_prod_left (x : (Σ k, ι k) → Ω) {G : (∀ k, ι k) → AddSubgroup (V × V₁)}
    {H : (∀ k, ι k) → AddSubgroup V} (hG : IsLatFamily o x G) (hH : IsLatFamily o x H) :
    IsLatFamily o x fun c => G c ⊓ (H c).prod (⊤ : AddSubgroup V₁) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).1
    exact ⟨hG.1 c hc a ha v hv.1, AddSubgroup.mem_prod.2 ⟨hH.1 c hc a ha _ h2, trivial⟩⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).1
    obtain ⟨m₁, h₁⟩ := hG.2 c t hc ht v hv.1
    obtain ⟨m₂, h₂⟩ := hH.2 c t hc ht _ h2
    have hq := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c
    refine ⟨m₂ + m₁, ?_, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩
    · have := hG.1 t ht _ (pow_mem hq m₂) _ h₁
      rwa [smul_smul, ← pow_add] at this
    · have := hH.1 t ht _ (pow_mem hq m₁) _ h₂
      rw [smul_smul, ← pow_add, add_comm] at this
      simpa using this

end Families

theorem relSeq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → ∀ τ, QuotExact O x (fun c => divLat (algebraMap O Ω w) ((D c).lie τ)) (fun c => (D c).W τ) (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) (fun c => stdLat (chartRing O (mseg x) c) (Fin n)) (fun c => (D c).om τ) (fun c => (D c).omHT τ) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x hinj F _ _ _ n Sg _ r s p hp w χ φ D hD hG hF τ
  have hhfam := (((GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x hinj p hp w χ φ D hD).2 τ).2.2.2.2 hG).1
  obtain ⟨-, -, -, -, hGam, hDel, -⟩ := hD.fam τ
  have h0 : χ τ 0 = 0 := (hD.char.2.2.2.2 τ).1
  have h1 : χ τ 1 = 1 := (hD.char.2.2.2.2 τ).2
  have h0' : algebraMap O Ω (χ τ 0) = 0 := by rw [h0, map_zero]
  have h1' : algebraMap O Ω (χ τ 1) = 1 := by rw [h1, map_one]
  have hstd : ∀ c, mseg x c ≠ 0 → stdLat (chartRing O (mseg x) c) (Fin n) ≤
      (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) :=
    fun c hc => std_le_hh (D c) _ p _ (hD.base c hc) _ h0' h1'
  refine ⟨fun c => gamH (D c) (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)),
    fun c => delH (D c) (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)),
    ⟨isLatFamily_inf_prod_right O x hGam hhfam, fun c hc => ?_⟩,
    ⟨isLatFamily_inf_prod_left O x hDel hhfam, fun c hc => ?_⟩, fun c hc => ?_⟩
  · have hB := hD.base c hc
    have hk := (hF c hc).ker τ
    refine ⟨fun v b hvb => ?_, fun v hv => ?_, fun b => ?_, fun v hv => ?_⟩
    · have h := (mem_gamH _ _ _ _ _ _ _).1 hvb
      refine ⟨?_, h.2⟩
      beta_reduce
      rw [← hk]
      exact (mem_kerH _ _ _ _ _ _).2 ⟨b, h⟩
    · beta_reduce at hv
      rw [← hk] at hv
      obtain ⟨b, h⟩ := (mem_kerH _ _ _ _ _ _).1 hv
      exact ⟨b, (mem_gamH _ _ _ _ _ _ _).2 h⟩
    · rw [mem_gamH]
      exact ⟨fun h => ((hB.gam τ).2.1 b).1 h.1, fun h => ⟨((hB.gam τ).2.1 b).2 h, hstd c hc h⟩⟩
    · exact (mem_gamH _ _ _ _ _ _ _).2 ⟨((hB.gam τ).2.2 v).2 hv, zero_mem _⟩
  · have hB := hD.base c hc
    have hi := (hF c hc).im τ
    refine ⟨fun b e hbe => ?_, fun b hb => ?_, fun e => ?_, fun b hb => ?_⟩
    · have h := (mem_delH _ _ _ _ _ _ _).1 hbe
      refine ⟨h.2, ?_⟩
      beta_reduce
      rw [← hi]
      exact (mem_imH _ _ _ _ _ _).2 ⟨b, h⟩
    · obtain ⟨e, he⟩ := ((hB.del τ).1 b).2
        (smul_mem_std_of_mem_hh (D c) _ p _ _ ((hF c hc).le_af τ) hb)
      exact ⟨e, (mem_delH _ _ _ _ _ _ _).2 ⟨he, hb⟩⟩
    · rw [mem_delH]
      exact ⟨fun h => ((hB.del τ).2.2.1 e).1 h.1, fun h => ⟨((hB.del τ).2.2.1 e).2 h, zero_mem _⟩⟩
    · refine (mem_delH _ _ _ _ _ _ _).2 ⟨((hB.del τ).2.2.2 b).2 ⟨0, ((hB.gam τ).2.1 b).2 hb⟩, hstd c hc hb⟩
  · have hB := hD.base c hc
    have hi := (hF c hc).im τ
    refine ⟨fun v hv => ?_, fun e he => ?_, fun b => ?_⟩
    · exact ((hB.gam τ).2.2 v).1 ((mem_gamH _ _ _ _ _ _ _).1 hv).1
    · beta_reduce at he
      rw [← hi] at he
      obtain ⟨b, h⟩ := (mem_imH _ _ _ _ _ _).1 he
      exact ⟨b, (mem_delH _ _ _ _ _ _ _).2 h⟩
    · rw [mem_delH]
      constructor
      · rintro ⟨h, hb⟩
        obtain ⟨a, ha⟩ := ((hB.del τ).2.2.2 b).1 h
        exact ⟨a, (mem_gamH _ _ _ _ _ _ _).2 ⟨ha, hb⟩⟩
      · rintro ⟨a, ha⟩
        have h := (mem_gamH _ _ _ _ _ _ _).1 ha
        exact ⟨((hB.del τ).2.2.2 b).2 ⟨a, h.1⟩, h.2⟩

end GlobalTheory.CompanionTheory.Ar.Num.RelSeq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InjectiveModPLatticeCharacterBoundStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_mod_p_lattice_character_bound : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → ∀ τ, QuotExact O x (fun c => divLat (algebraMap O Ω w) ((D c).lie τ)) (fun c => (D c).W τ) (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) (fun c => stdLat (chartRing O (mseg x) c) (Fin n)) (fun c => (D c).om τ) (fun c => (D c).omHT τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RelSeq.relSeq | exact GlobalTheory.CompanionTheory.Ar.Num.RelSeq.relSeq | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RelSeq.relSeq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeEigenSplit
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.GoodModel

theorem algebraMap_injective_of_model {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have h3 := h.2.2.1
  have hmem : a ∈ (mcIdeal O x).comap (C : O →+* _) := by
    rw [Ideal.mem_comap]
    simp only [mcIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap]
    erw [MvPolynomial.aeval_C]
    rw [MvPolynomial.algebraMap_apply, ha, map_zero]
  rw [h3] at hmem
  simpa using hmem

theorem quotExact_congr {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {V V₁ V₂ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
    [AddCommGroup V₂] [Module Ω V₂]
    {A A' A₂ A₂' : (∀ k, ι k) → AddSubgroup V} {B B' B₂ B₂' : (∀ k, ι k) → AddSubgroup V₁}
    {C C' C₂ C₂' : (∀ k, ι k) → AddSubgroup V₂}
    (hA : ∀ s, mseg x s ≠ 0 → A s = A₂ s) (hA' : ∀ s, mseg x s ≠ 0 → A' s = A₂' s)
    (hB : ∀ s, mseg x s ≠ 0 → B s = B₂ s) (hB' : ∀ s, mseg x s ≠ 0 → B' s = B₂' s)
    (hC : ∀ s, mseg x s ≠ 0 → C s = C₂ s) (hC' : ∀ s, mseg x s ≠ 0 → C' s = C₂' s)
    (h : QuotExact O x A A' B B' C C') : QuotExact O x A₂ A₂' B₂ B₂' C₂ C₂' := by
  obtain ⟨Γ, Δ, ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
  refine ⟨Γ, Δ, ⟨h1, fun s hs => ?_⟩, ⟨h3, fun s hs => ?_⟩, fun s hs => ?_⟩
  · have := h2 s hs
    rw [hA s hs, hA' s hs, hB s hs, hB' s hs] at this
    exact this
  · have := h4 s hs
    rw [hB s hs, hB' s hs, hC s hs, hC' s hs] at this
    exact this
  · have := h5 s hs
    rw [hA' s hs, hC s hs] at this
    exact this

theorem arith_first (a b c rw rp : ℤ) (P k : ℕ) (hP : 2 ≤ P) (e : a + b = c - (k : ℤ) * rw)
    (bd : ((P - 1 : ℕ) : ℤ) * rw = ((1 : ℕ) : ℤ) * rp) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) - (k : ℝ) * (rp : ℝ) / ((P : ℝ) - 1) := by
  have hP1 : (P : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    intro h0
    linarith
  have bdR : ((P : ℝ) - 1) * (rw : ℝ) = (rp : ℝ) := by
    have h1 := congrArg (Int.cast : ℤ → ℝ) bd
    have h2 : (((P - 1 : ℕ) : ℤ) : ℝ) = (P : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega), Nat.cast_one]
    rw [Int.cast_mul, h2, Int.cast_mul] at h1
    simpa using h1
  have eR : (a : ℝ) + (b : ℝ) = (c : ℝ) - (k : ℝ) * (rw : ℝ) := by exact_mod_cast e
  rw [eR, ← bdR]
  field_simp

theorem arith_second {m : ℕ} (A B : Fin m → ℤ) (Λ : ℤ) (P k : ℕ) (hk : 1 ≤ k)
    (e : (k : ℤ) * Λ = (-1) ^ (k - 1) * ∑ i, (A i - (P : ℤ) ^ k * B i)) :
    (P : ℝ) ^ k * ((((-1) ^ k * ∑ i, B i : ℤ)) : ℝ) =
      ((((-1) ^ k * ∑ i, A i : ℤ)) : ℝ) + (k : ℝ) * (Λ : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hz : (P : ℤ) ^ (j + 1) * ((-1) ^ (j + 1) * ∑ i, B i) =
      (-1) ^ (j + 1) * ∑ i, A i + ((j + 1 : ℕ) : ℤ) * Λ := by
    rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.add_sub_cancel]
    ring
  exact_mod_cast hz

theorem relations : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM F _ _ _ n Sg _ r s p hp w χ φ D hD hG1 hG2 hF hX Lie W Om OmHT hB
  have inj : Function.Injective (algebraMap O Ω) := algebraMap_injective_of_model hM
  obtain ⟨hp0, ⟨u, hu, hwu⟩, -, h01, hχ⟩ := hD.char
  have hp2 : 2 ≤ p := hp.two_le
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hwu
    exact hp0 (by simpa [hu.ne_zero] using hwu.symm)
  have hwΩ : algebraMap O Ω w ≠ 0 := (map_ne_zero_iff _ inj).2 hw0
  have hCD : ∀ c, CharData (chartRing O (mseg x) c) p (algebraMap O Ω w)
      (fun τ a => algebraMap O Ω (χ τ a)) := by
    intro c
    refine ⟨?_, Subalgebra.algebraMap_mem _ _, ?_, h01, fun τ => ⟨?_, ?_, fun a => Subalgebra.algebraMap_mem _ _⟩⟩
    · rw [← map_natCast (algebraMap O Ω)]
      exact (map_ne_zero_iff _ inj).2 hp0
    · obtain ⟨v, hv⟩ := hu.exists_left_inv
      refine ⟨algebraMap O Ω (v * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
      rw [← map_natCast (algebraMap O Ω), ← map_mul]
      congr 1
      have : w ^ (p - 1) = w ^ (p - 2) * w := by
        rw [← pow_succ]; congr 1; omega
      calc (p : O) = v * (u * p) := by rw [← mul_assoc, hv, one_mul]
        _ = v * w ^ (p - 1) := by rw [hwu]
        _ = v * w ^ (p - 2) * w := by rw [this, mul_assoc]
    · simp [(hχ τ).1]
    · simp [(hχ τ).2]
  have hfc := GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x inj p hp w χ φ D hD
  have hgb := fun c (hc : mseg x c ≠ 0) =>
    GlobalTheory.T.lattice_good_base_change (D c) (chartRing O (mseg x) c) p _ _ (hCD c) (hD.base c hc) (hG1 c hc)
  have hbf := GlobalTheory.T.lattice_families_glue_to_bundle O Ω K ι x
  have hbo := GlobalTheory.T.chart_bundle_product O Ω K ι x
  have hXb : ∀ τ i, ∃ E : ChartBundle O (mseg x) 1 Ω, ∀ c, mseg x c ≠ 0 →
      E.lat c = (D c).xId (fun a => algebraMap O Ω (χ τ a)) i := fun τ i =>
    (hbf 1 Ω).1 _ ((hfc.2 τ).2.1 i).1 (fun c hc => ((hgb c hc).1 τ).2.2.2 i)
  choose Xb hXb using hXb
  obtain ⟨T, hT⟩ := hbo.2.2.1 1 0 one_ne_zero
  obtain ⟨Tn, hTn⟩ := hbo.2.2.2.1 n (Fin n → Ω) (Pi.basisFun Ω (Fin n))
  have hTn' : ∀ c, mseg x c ≠ 0 → Tn.lat c = stdLat (chartRing O (mseg x) c) (Fin n) := by
    intro c hc
    ext v
    rw [hTn c hc v]
    simp [stdLat, AddSubgroup.mem_pi]
  have hH : ∀ τ, ∃ E : ChartBundle O (mseg x) n (Fin n → Ω), ∀ c, mseg x c ≠ 0 →
      E.lat c = (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) := fun τ =>
    (hbf n _).1 _ ((hfc.2 τ).2.2.2.2 hG1).1 (fun c hc => ((hgb c hc).1 τ).2.1)
  choose H hH using hH
  have hLa : ∀ τ, ∃ E : ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω),
      IsScaled x (algebraMap O Ω w)⁻¹ (Lie τ).lat E.lat := fun τ =>
    hbo.2.1 _ _ (Lie τ) _ (inv_ne_zero hwΩ)
  choose La hLa using hLa
  have hdiv : ∀ {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (v : Fin m → Ω),
      v ∈ divLat (algebraMap O Ω w) L ↔ algebraMap O Ω w • v ∈ L := fun _ _ => Iff.rfl
  have hLa' : ∀ τ c, mseg x c ≠ 0 →
      (La τ).lat c = divLat (algebraMap O Ω w) ((Lie τ).lat c) := by
    intro τ c hc
    ext v
    rw [hLa τ c hc v]
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [hdiv, smul_inv_smul₀ hwΩ]
      exact he
    · intro hv
      exact ⟨algebraMap O Ω w • v, (hdiv _ _).1 hv, (inv_smul_smul₀ hwΩ v).symm⟩
  have hSc : ∀ τ, IsScaled x (algebraMap O Ω w) (La τ).lat (Lie τ).lat := by
    intro τ c hc v
    rw [hLa' τ c hc]
    constructor
    · intro hv
      refine ⟨(algebraMap O Ω w)⁻¹ • v, ?_, (smul_inv_smul₀ hwΩ v).symm⟩
      rw [hdiv, smul_inv_smul₀ hwΩ]
      exact hv
    · rintro ⟨e, he, rfl⟩
      exact (hdiv _ _).1 he
  have hLW : ∀ τ, LatLE O x (Lie τ) (W τ) := by
    intro τ c hc
    rw [(hB τ c hc).1, (hB τ c hc).2.1]
    exact ((hD.base c hc).incl τ).1
  have hWLa : ∀ τ, LatLE O x (W τ) (La τ) := by
    intro τ c hc
    rw [hLa' τ c hc, (hB τ c hc).1, (hB τ c hc).2.1]
    exact ((hD.base c hc).incl τ).2.1
  have hOm : ∀ τ, SameGeneric O x (Om τ) (OmHT τ) := by
    intro τ c hc
    rw [(hB τ c hc).2.2.1, (hB τ c hc).2.2.2]
    have hi := (hD.base c hc).incl τ
    refine ⟨fun v hv => ⟨w, hw0, hi.2.2.2 hv⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
    rw [map_one, one_smul]
    exact hi.2.2.1 hv
  have hRH := fun τ => GlobalTheory.T.model_over_mod_p_lattice_character O Ω K ι x d hM p hp w χ φ D hD hG1 hG2 hF hX Xb T
    (fun τ i c hc => hXb τ i c hc) hT τ (H τ) Tn (fun c hc => ⟨hH τ c hc, hTn' c hc⟩)
  have hSeq : ∀ τ, QuotExact O x (La τ).lat (W τ).lat (H τ).lat Tn.lat (Om τ).lat (OmHT τ).lat := by
    intro τ
    refine quotExact_congr ?_ ?_ ?_ ?_ ?_ ?_ (GlobalTheory.T.injective_mod_p_lattice_character_bound O Ω K ι x inj p hp w χ φ D hD hG1 hF τ)
    · intro c hc; rw [hLa' τ c hc, (hB τ c hc).1]
    · intro c hc; rw [(hB τ c hc).2.1]
    · intro c hc; rw [hH τ c hc]
    · intro c hc; rw [hTn' c hc]
    · intro c hc; rw [(hB τ c hc).2.2.1]
    · intro c hc; rw [(hB τ c hc).2.2.2]
  intro k hk1 hk2 q L Q hQ
  refine ⟨fun τ => (((-1) ^ k * ∑ i, ck O x d 1 (Xb τ i) T k L Q : ℤ) : ℝ), fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨Ew, hEw⟩ := hbo.2.1 _ _ (Lie τ) _ hwΩ
    have bd := ((GlobalTheory.T.dvr_bundle_statement_d O Ω K ι) x d (r τ) _ (Lie τ) Ew w hw0 hM hEw k hk1 hk2 q L Q hQ).2
      (p - 1) 1 (p : O) u hu (by omega) (by rw [pow_one]; exact hwu)
    have l61 := GlobalTheory.T.hodge_lie_bundle_intersection O Ω K ι x d (r τ) (s τ) n _ _ _ (Lie τ) (W τ) (La τ) (Om τ) (OmHT τ) Tn (H τ)
      w hw0 hM (hLW τ) (hWLa τ) (hSc τ) (hOm τ) (hRH τ).1 (hSeq τ) k hk1 hk2 q L Q hQ
    rw [(hRH τ).2 k hk1 hk2 q L Q hQ] at l61
    exact arith_first _ _ _ _ _ p k hp2 l61 bd
  · exact arith_second _ _ _ p k hk1
      (GlobalTheory.T.model_over_mod_p_lattice_permuted O Ω K ι x d hM p hp w χ φ D hD hG1 hG2 hF hX Xb T
        (fun τ i c hc => hXb τ i c hc) hT Lie W Om OmHT hB τ k hk1 hk2 q L Q hQ)

end GlobalTheory.CompanionTheory.Ar.Num.GoodModel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeEigenSplitStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_over_mod_p_lattice_eigen_split : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.GoodModel.relations | exact GlobalTheory.CompanionTheory.Ar.Num.GoodModel.relations | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.GoodModel.relations <;> assumption)
end

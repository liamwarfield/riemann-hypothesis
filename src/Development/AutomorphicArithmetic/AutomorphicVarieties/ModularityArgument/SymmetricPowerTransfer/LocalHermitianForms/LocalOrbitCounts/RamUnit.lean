module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LeftMulMatrixEmbeddingDetEqNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.IntDown

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RamUnit
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.ramUnit : UpperTheory.V.Z.Sym.Loc.RamUnit := by
  intro O K _ _ _ _ _ Δ L D h0 hD
  obtain ⟨ε, hε⟩ := L.exists_nonsq
  refine ⟨ε, if_neg fun h => ?_⟩
  obtain ⟨a, b, e⟩ := nm_symm h0 L.two_ne h (ε.isUnit.map _).ne_zero
  exact hD (e ▸ L.even_of_norm ε hε (e ▸ h0))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormOneIsCoboundaryUnramifiedQuadratic
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.h90L : UpperTheory.V.Z.Sym.Loc.NormOneIsCoboundaryUnramifiedQuadratic := by
  intro O K _ _ _ _ _ Δ L β hβ
  haveI := L.frac
  have h2 := L.two_ne
  have h0 : Δ ≠ 0 := by
    obtain ⟨u, s, hs, e⟩ := L.even
    rw [e]
    exact mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)
  rw [QuadraticAlgebra.norm_def] at hβ
  by_cases h : 1 + β.re = 0
  · have h1 : β.re = -1 := by linear_combination h
    have h3 : β.im = 0 := by
      have : Δ * β.im ^ 2 = 0 := by rw [h1] at hβ; linear_combination -hβ
      simpa [h0] using this
    have hu : IsUnit (ω : Lsq K Δ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by simp [QuadraticAlgebra.norm_def, h0])
    exact ⟨hu.unit, by ext <;> simp [h1, h3]⟩
  · have hu : IsUnit (⟨1 + β.re, -β.im⟩ : Lsq K Δ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by
      have : QuadraticAlgebra.norm (⟨1 + β.re, -β.im⟩ : Lsq K Δ) = 2 * (1 + β.re) := by
        rw [QuadraticAlgebra.norm_def]; simp only; linear_combination hβ
      rw [this]; exact (mul_ne_zero h2 h).isUnit)
    refine ⟨hu.unit, ?_⟩
    ext
    · simp; linear_combination -hβ
    · simp; ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVals
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Vcount
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.vMax : UpperTheory.V.Z.Sym.Loc.VMax := by
  intro O K _ _ _ _ _ Δ τ hl hτ x htr hnm hdisc
  have hg : PK.Gen1 O x := ⟨htr, hnm, hdisc⟩
  letI := mulAct τ
  have hsm : ∀ (t : (Etau K τ)ˣ) (S : Set (Etau K τ)), t • cls τ S = cls τ (PS.ml t S) := by
    intro t S
    exact PS.cls_ml t S
  have hone : ∀ S : Set (Etau K τ), PS.ml 1 S = S := by
    intro S
    ext w
    simp [PS.mem_ml]
  let P : Set (Set (Set (Etau K τ))) :=
    {X | ∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S}
  have hv : vcount O τ x = wcount (Cint O τ) (P.indicator fun _ => (1 : ℂ)) := by
    unfold vcount
    rfl
  have h1 : ∀ (t : (Etau K τ)ˣ), ∀ X ∈ P, t • X ∈ P := by
    rintro t _ ⟨S, hS, hx, rfl⟩
    refine ⟨PS.ml t S, PS.lat_ml hS t, ?_, hsm t S⟩
    intro y hy
    rw [PS.mem_ml] at hy ⊢
    rw [mul_left_comm]
    exact hx _ hy
  have h2 : ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))) ⊆ P := by
    intro X hX
    rw [Set.mem_singleton_iff] at hX
    subst hX
    exact ⟨PK.Mx O τ, PK.Gen1.lat hl hg, fun y hy => (PK.Gen1.int hg).mul hy, rfl⟩
  have h4 : ∀ c ∈ Cint O τ, ∀ X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))),
      c • X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))) := by
    intro c hc X hX
    rw [Set.mem_singleton_iff] at hX ⊢
    subst hX
    obtain ⟨s, u, hu1, hu2, rfl⟩ := PK.Gen1.cint hl hg hc
    rw [hsm, PS.ml_mul, PK.ml_Mx hu1 hu2, PS.cls_sc]
  have h5 : ∀ X ∈ P, ∃ t : (Etau K τ)ˣ, t • X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))) := by
    rintro _ ⟨S, hS, hx, rfl⟩
    obtain ⟨u, hu⟩ := PK.Gen1.princ hl hτ hg hS hx
    have hSu : S = PS.ml u (PK.Mx O τ) := by
      ext w
      rw [PS.mem_ml, hu]
      rfl
    refine ⟨u⁻¹, ?_⟩
    rw [Set.mem_singleton_iff, hsm, hSu, ← PS.ml_mul, inv_mul_cancel, hone]
  have h6 : ∀ (t : (Etau K τ)ˣ), ∀ X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))),
      t • X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))) → ∃ c ∈ Cint O τ, c • X = t • X := by
    intro t X hX htX
    refine ⟨1, (Cint O τ).one_mem, ?_⟩
    rw [Set.mem_singleton_iff] at hX htX
    rw [one_smul, htX, hX]
  rw [hv, wCard _ _ (Cint O τ) P _ h1 h2 (Set.finite_singleton _) h4 h5 h6, Set.ncard_singleton, Nat.cast_one]
end

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem vcount_one_add {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (x : Etau K τ) :
    vcount O τ (1 + x) = vcount O τ x := by
  have key : ∀ X, (∃ S, IsLat O τ S ∧ (∀ y ∈ S, (1 + x) * y ∈ S) ∧ X = cls τ S) ↔
      (∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S) := by
    intro X
    apply exists_congr
    intro S
    constructor
    · rintro ⟨hL, hst, hX⟩
      refine ⟨hL, ?_, hX⟩
      obtain ⟨s, rfl⟩ := hL.fg
      intro y hy
      have h1 := hst y hy
      rw [SetLike.mem_coe] at h1 hy ⊢
      have h2 := (Submodule.span O (s : Set (Etau K τ))).sub_mem h1 hy
      simpa [add_mul] using h2
    · rintro ⟨hL, hst, hX⟩
      refine ⟨hL, ?_, hX⟩
      obtain ⟨s, rfl⟩ := hL.fg
      intro y hy
      have h1 := hst y hy
      rw [SetLike.mem_coe] at h1 hy ⊢
      rw [add_mul, one_mul]
      exact (Submodule.span O (s : Set (Etau K τ))).add_mem hy h1
  unfold vcount
  congr 1
  funext X
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((key X).1 h1) h2
  · exact absurd ((key X).2 h2) h1
  · rfl

theorem UpperTheory.V.Z.Sym.Loc.gVals : UpperTheory.V.Z.Sym.Loc.GVals := by
  intro O K _ _ _ _ _ Δ τ L hτ hτO j χ hj hχ a ha z hz
  obtain ⟨o, ho⟩ := hτO
  have hna : QuadraticAlgebra.norm (a : Etau K τ) = 1 := by
    rw [ha]
    simp [QuadraticAlgebra.norm]
  have hnz : QuadraticAlgebra.norm (z : Etau K τ) = 2 + τ := by
    rw [hz]
    simp [QuadraticAlgebra.norm]
    ring
  have gA : gOrb O j χ a = vcount O τ a := by
    have h1 := gLat O K Δ τ L hτ j χ hj hχ a 1 1 (by rw [hna]; simp)
    simpa using h1
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    have gZ := gLat O K Δ τ L hτ j χ hj hχ z 1 u (by rw [hnz, hu]; simp)
    simp only [map_one, Units.val_one, inv_one, one_mul, one_smul] at gZ
    rw [gA, gZ, hz, ← ha, vcount_one_add]
  · rintro ⟨u, hu⟩
    rw [gA, ha]
    apply vMax O K Δ τ L hτ
    · exact ⟨o, by rw [ho]; simp [trace]⟩
    · exact ⟨1, by simp [QuadraticAlgebra.norm]⟩
    · exact ⟨u, by rw [hu]; simp⟩
  · rintro ⟨u, hu⟩ s ε hs
    have gZ := gLat O K Δ τ L hτ j χ hj hχ z s ε (by rw [hnz, hs])
    haveI := L.frac
    have hsO : ∃ c : O, algebraMap O K c = (s : K) := by
      have hint : IsIntegral O ((s : K) ^ 2) := by
        have : (s : K) ^ 2 = algebraMap O K (((ε⁻¹ : Oˣ) : O) * (2 + o)) := by
          have hinv : algebraMap O K ((ε⁻¹ : Oˣ) : O) * algebraMap O K (ε : O) = 1 := by
            rw [← map_mul, Units.inv_mul, map_one]
          rw [map_mul, map_add (f := _), map_ofNat, ho]
          linear_combination (-(algebraMap O K ((ε⁻¹ : Oˣ) : O))) * hs - (s : K) ^ 2 * hinv
        rw [this]
        exact isIntegral_algebraMap
      exact IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_pow two_pos hint)
    obtain ⟨c, hc⟩ := hsO
    have hs0 := s.ne_zero
    have hv : vcount O τ (((s⁻¹ : Kˣ) : K) • (z : Etau K τ)) = 1 := by
      apply vMax O K Δ τ L hτ
      · refine ⟨ε * c, ?_⟩
        rw [hz]
        simp [trace]
        rw [hc]
        field_simp
        linear_combination -hs
      · refine ⟨ε, ?_⟩
        rw [hz]
        simp [QuadraticAlgebra.norm]
        field_simp
        linear_combination -hs
      · refine ⟨-(ε * u), ?_⟩
        rw [hz]
        simp
        rw [hu]
        field_simp
        linear_combination (2 - τ) * hs
    rw [gZ, hv, mul_one]
end

module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SubstitutionOfVariables
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FormValuationGeNegDegree

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DworkExponentialRestrictions
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser')

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

abbrev wK (p : ℕ) [Fact p.Prime] (c : WW p) : K0 p := algebraMap (WW p) (K0 p) c

def RestBeta (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
    ∃ c : WW p, (sigW p)^[2] c = c ∧ E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))

def RestGc (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → ∀ c : WW p, (sigW p)^[2] c = c → ∀ (n' r0 r1 : ℕ), 2 ≤ n' → Even n' → ∀ (B : OmBasis p n')
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
    ∃ u : Fin n' → K', (∀ s, u s ∈ Rp p K' vp) ∧ ∃ V : MvPowerSeries (Zidx n' r0 r1) K', IntR (Rp p K' vp) V ∧
      MvPowerSeries.subst (tOf vp μ (coordZ B K' 1)) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
          (Gt p (Eidx n' r0 r1) (wK p c) (wK p (sigW p c)))))) =
        expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u)) * V

def RestGcA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ c : WW p, (sigW p)^[2] c = c → ∀ (j : ℕ)
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
    ∃ u : ∀ v : X.Pl, Fin (X.G.P.n' v) → K', (∀ v s, u v s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        MvPowerSeries.subst (tOf vp μ (X.coordZA K' j)) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
            (Gt p (X.EA j) (wK p c) (wK p (sigW p c)))))) =
          (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v (u v)))) * V

section

variable {p : ℕ} [hp : Fact p.Prime]

theorem th_Gser_const (c c' : K0 p) : MvPowerSeries.constantCoeff (Gser p c c') = 0 := by
  have hA : MvPowerSeries.constantCoeff (Aser (K0 p) p) = 0 := by
    show Aser (K0 p) p 0 = 0
    simp [Aser]
  have hA' : MvPowerSeries.constantCoeff (Aser' (K0 p) p) = 0 := by
    show Aser' (K0 p) p 0 = 0
    simp [Aser']
  simp [Gser, hA, hA']

theorem th_be_const {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeProp p be) :
    MvPowerSeries.constantCoeff be = 0 := by
  by_contra hne
  have hh := (h.ab 0 hne).1
  simp at hh

theorem th_coordZ_eq {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') :
    coordZ (r0 := r0) (r1 := r1) B K' vp = fun x => MvPowerSeries.C vp * coordZ B K' 1 x := by
  funext x
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
    simp only [coordZ, Finset.mul_sum, one_mul, map_mul, mul_assoc]

theorem th_coordZ_int {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : IntR (Rp p K' vp) (coordZ B K' 1 x) := by
  intro n
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩
  all_goals
    simp only [coordZ, map_sum, one_mul]
    refine Subring.sum_mem _ fun s _ => ?_
    rw [MvPowerSeries.coeff_C_mul]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨_, rfl⟩)) ?_
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

theorem th_coordZA_int (X : Sys p) (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (j : ℕ)
    (x : X.EA j ⊕ X.EA j) : IntR (Rp p K' vp) (X.coordZA K' j x) := by
  intro n
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩
  all_goals
    simp only [Sys.coordZA, map_sum]
    refine Subring.sum_mem _ fun s _ => ?_
    rw [MvPowerSeries.coeff_C_mul]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨_, rfl⟩)) ?_
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

private theorem constantCoeff_coordZ_eq_zero {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K']
    (vp : K') (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : MvPowerSeries.constantCoeff (coordZ B K' vp x) = 0 := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;> simp [coordZ]

theorem restSExp_of (hB : RestBeta p) (hG : RestGc p) : RestSExp p := by
  intro h5 hD be hbe n' r0 r1 h2 hev B Ph hPh K' _ _ vp hvp
  obtain ⟨c, hc, hE⟩ := hB h5 hD be hbe
  obtain ⟨μ, hμ0, hμR, hμ1⟩ := exists_mu (p := p) K' vp hvp
  obtain ⟨u, hu, V, hV, hGeq⟩ := hG h5 c hc n' r0 r1 h2 hev B K' vp hvp μ hμ0 hμ1
  obtain ⟨V', hV', hred⟩ := th_reduce (p := p) be (th_be_const hbe) (wK p c) (wK p (sigW p c))
    (th_Gser_const _ _) (fun _ => hE) Ph hPh K' vp μ hμ0 hμR hμ1 (coordZ B K' 1)
    (fun i => constantCoeff_coordZ_eq_zero B K' 1 i) (fun i => th_coordZ_int B K' vp i)
  refine ⟨u, hu, V * V', IntR_mul hV hV', ?_⟩
  unfold ThZ
  rw [th_coordZ_eq B K' vp, hred, hGeq, mul_assoc]

private theorem constantCoeff_coordZA_eq_zero (X : Sys p) (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ)
    (x : X.EA j ⊕ X.EA j) : MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA]

private theorem mvPowerSeries_map_algebraMap_map_algebraMap (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K']
    [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] {σ : Type} (F : MvPowerSeries σ (K0 p)) :
    MvPowerSeries.map (algebraMap K1 K') (MvPowerSeries.map (algebraMap (K0 p) K1) F) =
      MvPowerSeries.map (algebraMap (K0 p) K') F := by
  ext n
  simp [MvPowerSeries.coeff_map, IsScalarTower.algebraMap_apply (K0 p) K1 K']

theorem restSExpA_of (X : Sys p) (hB : RestBeta p) (hG : RestGcA X) : RestSExpA X := by
  intro hD be hbe j Ph hPh K1 _ _ K' _ _ _ _ vp hvp
  obtain ⟨c, hc, hE⟩ : ∃ c : WW p, (sigW p)^[2] c = c ∧
      (X.EA j → E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))) := by
    by_cases h5 : 5 ≤ p
    · obtain ⟨c, hc, hE⟩ := hB h5 hD be hbe
      exact ⟨c, hc, fun _ => hE⟩
    · refine ⟨0, ?_, fun e => absurd (X.std e.1).five_le h5⟩
      first
        | exact Function.iterate_fixed (map_zero (sigW p)) 2
        | simp
  obtain ⟨μ, hμ0, hμR, hμ1⟩ := exists_mu (p := p) K' vp hvp
  obtain ⟨u, hu, V, hV, hGeq⟩ := hG c hc j K' vp hvp μ hμ0 hμ1
  obtain ⟨V', hV', hred⟩ := th_reduce (p := p) be (th_be_const hbe) (wK p c) (wK p (sigW p c))
    (th_Gser_const _ _) hE Ph hPh K' vp μ hμ0 hμR hμ1 (X.coordZA K' j)
    (fun i => constantCoeff_coordZA_eq_zero X K' j i) (fun i => th_coordZA_int X K' vp j i)
  refine ⟨u, hu, V * V', IntR_mul hV hV', ?_⟩
  rw [atPi_map_ThZA (X := X), mvPowerSeries_map_algebraMap_map_algebraMap, hred, hGeq, mul_assoc]

theorem baseChange_preserves_unitary_of (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hB : RestBeta p) (hG : RestGc p) :
    Conclusion1 D X Y :=
  kernel_expansion_of_restrictions D X Y hA (restSExp_of hB hG) (restSInt p)

theorem expansion_all_places_of_computation (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hB : RestBeta p) (hG : RestGcA X) :
    ExpansionsMultiply D X Y :=
  all_places_of_restrictions (hA := hA) (hE := restSExpA_of X hB hG) (hI := restSIntA (X := X))

end

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HkLatTupUpdate
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

section Loc

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem between_fin (p k : ℕ) (hfin : Finite (W ⧸ Ideal.span {(p : W)})) (L : Submodule W (Fin k → Qq))
    (hL : IsLattice W L) :
    {A : Submodule W (Fin k → Qq) | A ≤ L ∧ ∀ x ∈ L, (p : W) • x ∈ A}.Finite := by
  classical
  obtain ⟨g, -, hg⟩ := hL
  have hfg : L.FG := by
    rw [hg]; exact Submodule.fg_span (Set.finite_range _)
  have : Module.Finite W L := Module.Finite.iff_fg.mpr hfg
  set I : Ideal W := Ideal.span {(p : W)} with hI
  have : Module.Finite (W ⧸ I) (↥L ⧸ I • (⊤ : Submodule W L)) :=
    Module.Finite.of_restrictScalars_finite W _ _
  have : Finite (↥L ⧸ I • (⊤ : Submodule W L)) := Module.finite_of_finite (W ⧸ I)
  let f : Submodule W (Fin k → Qq) → Set (↥L ⧸ I • (⊤ : Submodule W L)) :=
    fun A => ((A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ : Set _)
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  have key : ∀ A : Submodule W (Fin k → Qq), (∀ x ∈ L, (p : W) • x ∈ A) →
      I • (⊤ : Submodule W L) ≤ A.comap L.subtype := by
    intro A hA
    rw [Submodule.smul_le]
    intro a ha x _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [mul_smul]
    apply Submodule.smul_mem
    show (p : W) • (x : Fin k → Qq) ∈ A
    exact hA x x.2
  intro A hA B hB hAB
  have h1 : (A.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ =
      (B.comap L.subtype).map (I • (⊤ : Submodule W L)).mkQ := SetLike.coe_injective hAB
  have h2 := congrArg (Submodule.comap (I • (⊤ : Submodule W L)).mkQ) h1
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.mpr (key A hA.2),
    sup_eq_right.mpr (key B hB.2)] at h2
  have h3 := congrArg (Submodule.map L.subtype) h2
  rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hA.1,
    inf_eq_right.mpr hB.1] at h3
  exact h3

theorem up_fin_gen (p n' r k : ℕ) (hfin : Finite (W ⧸ Ideal.span {(p : W)})) (hp : algebraMap W Qq (p : W) ≠ 0)
    (A : Submodule W (Fin k → Qq)) :
    {A1 : Submodule W (Fin k → Qq) | IsEdge p n' r ⟨A, A1⟩}.Finite := by
  by_cases hA : IsLattice W A
  · let φ : (Fin k → Qq) →ₗ[W] (Fin k → Qq) := (p : W) • LinearMap.id
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : (p : W) • x = (p : W) • y := hxy
      rw [← algebraMap_smul Qq (p : W) x, ← algebraMap_smul Qq (p : W) y] at h1
      exact smul_right_injective _ hp h1
    refine Set.Finite.of_finite_image (f := fun A1 => A1.map φ) ((between_fin p k hfin A hA).subset ?_)
      (fun a _ b _ h => Submodule.map_injective_of_injective hφ h)
    rintro _ ⟨A1, hA1, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hA1.2.2.2.1 x hx
    · intro x hx
      exact ⟨x, hA1.2.2.1 hx, rfl⟩
  · apply Set.Finite.subset Set.finite_empty
    intro A1 h
    exact (hA h.1).elim

theorem count_fun (hC : CountLoc) (p n' : ℕ) [IsDomain W] [IsDiscreteValuationRing W] (h1 : IsFractionRing W Qq)
    (h2 : Irreducible (p : W)) (h3 : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (N N' g i : ℕ) (hN : N' = N + g)
    (A : Submodule W (Fin N → Qq)) (B : Submodule W (Fin N' → Qq)) (hA : IsLattice W A) (hB : IsLattice W B)
    (SB : Finset (Submodule W (Fin N' → Qq))) (hSB : ∀ B1, B1 ∈ SB ↔ IsEdge p n' i ⟨B1, B⟩)
    (SA : ℕ → Finset (Submodule W (Fin N → Qq))) (hSA : ∀ k A1, A1 ∈ SA k ↔ IsEdge p n' k ⟨A, A1⟩)
    (x : Matrix (Fin N') (Fin N) Qq) :
    (∑ B1 ∈ SB, (by classical exact if ∀ y ∈ A, x.mulVec y ∈ B1 then (1 : ℚ) else 0)) =
      ∑ l ∈ range (i + 1), (((p ^ n') ^ ((i - l) * (g - l)) * Formalism.G0.gaussBinom (p ^ n') g l : ℕ) : ℚ) *
        ∑ A1 ∈ SA (i - l), (by classical exact if ∀ y ∈ A1, x.mulVec y ∈ B then (1 : ℚ) else 0) := by
  classical
  have e1 : ∀ (M : ℕ) (S : Finset (Submodule W (Fin M → Qq))) (E Pp : Submodule W (Fin M → Qq) → Prop)
      (_ : ∀ Z, Z ∈ S ↔ E Z), (∑ Z ∈ S, if Pp Z then (1 : ℚ) else 0) =
        (Nat.card {Z : Submodule W (Fin M → Qq) // E Z ∧ Pp Z} : ℚ) := by
    intro M S E Pp hS
    rw [Finset.sum_boole]
    congr 1
    rw [← Nat.card_eq_fintype_card.trans (Fintype.card_coe (S.filter Pp))]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun Z => by rw [Finset.mem_filter, hS]
  have := hC p n' W Qq h1 h2 h3 N N' g i hN A B hA hB x
  convert congrArg (fun n : ℕ => (n : ℚ)) this using 1
  · exact e1 N' SB _ _ hSB
  · push_cast
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    exact e1 N (SA (i - l)) _ _ (hSA (i - l))

end Loc

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem hk_pQ_ne (v : Fin P.nV) : algebraMap (P.W v) (P.Qq v) (p : P.W v) ≠ 0 := by
  have := (P.setting v).frac_alt
  exact (map_ne_zero_iff _ (IsFractionRing.injective (P.W v) (P.Qq v))).2 (P.setting v).p_unif.ne_zero

theorem up_fin (v : Fin P.nV) (i : ℕ) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {A1 : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨A, A1⟩}.Finite := by
  apply up_fin_gen
  · apply Nat.finite_of_card_ne_zero
    rw [(P.setting v).res_card]
    exact pow_ne_zero _ (P.setting v).prime.ne_zero
  · exact hk_pQ_ne P v

def UP (v : Fin P.nV) (i : ℕ) (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (up_fin P v i A).toFinset

theorem mem_UP {v : Fin P.nV} {i : ℕ} {A A1 : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    A1 ∈ UP P v i A ↔ IsEdge p (P.n' v) i ⟨A, A1⟩ := by
  simp [UP]

theorem hk_latTup_update {L : P.Tup} (hL : P.IsLatTup L) (v : Fin P.nV)
    (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (hA : IsLattice (P.W v) A) :
    P.IsLatTup (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A) := by
  unfold Places.IsLatTup at *
  intro w
  by_cases h : w = v
  · subst h
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L w A w = A := by
      first
        | exact Function.update_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A L
        | exact Function.update_same (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A L
    exact (congrArg (fun Z => IsLattice (P.W w) Z) e).mpr hA
  · have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A w = L w := Function.update_of_ne (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) h A L
    exact (congrArg (fun Z => IsLattice (P.W w) Z) e).mpr (hL w)

theorem latTup_smul (C : Level P) (γ : C.Γ) (L : P.Tup) : P.IsLatTup (C.smul γ L) ↔ P.IsLatTup L := by
  constructor
  · intro h u
    have h1 : IsLattice (P.W u) ((L u).map (nt_phi (P.W u) (C.act u γ))) := h u
    have h2 := nt_lat_map (C.act u γ)⁻¹ _ h1
    rw [nt_map_inv] at h2
    exact h2
  · intro h u
    exact nt_lat_map (C.act u γ) (L u) (h u)

end PlacesLevel

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

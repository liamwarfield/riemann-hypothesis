module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BalancedNonnegFormInPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPsdFormsCoverContactSet
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFiniteBelowModTwo
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_finite_below_mod_two {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] {m : ℕ}
    (f : X → Fin m → ℕ) :
    ∃ G : Set X, G.Finite ∧ ∀ y, ∃ y' ∈ G, (∃ x : X, y' = y + (x + x)) ∧ f y' ≤ f y := by
  classical
  have hmin : ∀ (V : Set (Fin m → ℕ)) (a : Fin m → ℕ), a ∈ V → ∃ v, Minimal (· ∈ V) v ∧ v ≤ a := by
    intro V a ha
    obtain ⟨v, ⟨hvV, hva⟩, hvmin⟩ := wellFounded_lt.has_min {w | w ∈ V ∧ w ≤ a} ⟨a, ha, le_rfl⟩
    refine ⟨v, ⟨hvV, fun w hwV hwv => ?_⟩, hva⟩
    by_contra hne
    exact hvmin w ⟨hwV, hwv.trans hva⟩ (lt_of_le_of_ne hwv fun h => hne (le_of_eq h.symm))
  set e := (Module.finBasis ℤ X).equivFun with he
  have key : ∀ y : X, ∃ x : X,
      e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y + (x + x) := by
    intro y
    refine ⟨e.symm (fun i => -(e y i / 2)), ?_⟩
    apply e.injective
    rw [map_add (f := _), map_add (f := _), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    funext i
    simp only [ZMod.val_intCast, Pi.add_apply, Nat.cast_ofNat]
    rw [Int.emod_def]
    ring
  let red : X → (Fin (Module.finrank ℤ X) → ZMod 2) := fun y i => ((e y i : ℤ) : ZMod 2)
  have hred : ∀ y y' : X, red y' = red y → ∃ x : X, y' = y + (x + x) := by
    intro y y' h
    obtain ⟨x1, h1⟩ := key y
    obtain ⟨x2, h2⟩ := key y'
    refine ⟨x1 - x2, ?_⟩
    have hh : (fun i => ((e y' i : ℤ) : ZMod 2)) = (fun i => ((e y i : ℤ) : ZMod 2)) := h
    have h2' : e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y' + (x2 + x2) := by
      rw [← h2]
      congr 1
      funext i
      rw [congrFun hh i]
    have h3 : y' + (x2 + x2) = y + (x1 + x1) := h2'.symm.trans h1
    rw [eq_sub_of_add_eq h3]
    abel
  let V : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ) := fun ε => f '' {y | red y = ε}
  let M : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ) := fun ε => {v | Minimal (· ∈ V ε) v}
  have hMfin : ∀ ε, (M ε).Finite := fun ε =>
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain fun x => x ∈ V ε)
  let pick : (Fin (Module.finrank ℤ X) → ZMod 2) → (Fin m → ℕ) → X := fun ε v =>
    if h : ∃ y, red y = ε ∧ f y = v then h.choose else 0
  refine ⟨⋃ ε, pick ε '' M ε, Set.finite_iUnion fun ε => (hMfin ε).image _, fun y => ?_⟩
  obtain ⟨v, hvM, hvle⟩ := hmin (V (red y)) (f y) ⟨y, rfl, rfl⟩
  have hex : ∃ w, red w = red y ∧ f w = v := by
    obtain ⟨w, hw, hwv⟩ := hvM.1
    exact ⟨w, hw, hwv⟩
  have hpick : red (pick (red y) v) = red y ∧ f (pick (red y) v) = v := by
    dsimp only [pick]
    rw [dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨pick (red y) v, Set.mem_iUnion.mpr ⟨red y, v, hvM, rfl⟩, hred y _ hpick.1, ?_⟩
  rw [hpick.2]
  exact hvle

theorem finite_isMin2 : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (m : ℕ)
    (P : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) →
    ∃ F : Set X, F.Finite ∧ ∀ B ∈ rcone P, IsPosDef B → ∀ y, IsMin2 B y → y ∈ F := by
  intro X _ _ _ m P hsym hnn
  classical
  obtain ⟨G, hG, hGy⟩ := exists_finite_below_mod_two (fun y i => (P i y y).toNat)
  set C : ℤ := ∑ g ∈ hG.toFinset, ∑ i, P i g g with hC
  let Q : Finset (Fin m) → LinearMap.BilinForm ℤ X := fun S => ∑ i ∈ S, P i
  have hQ : ∀ S z w, Q S z w = ∑ i ∈ S, P i z w := by
    intro S z w
    simp [Q, LinearMap.sum_apply]
  refine ⟨⋃ S : Finset (Fin m), if (∀ y : X, y ≠ 0 → 0 < Q S y y) then {y | Q S y y ≤ S.card * C} else ∅,
    ?_, ?_⟩
  · refine Set.finite_iUnion fun S => ?_
    split_ifs with hpos
    · exact GlobalTheory.T.finite_pos_def_form_sublevel X (Q S) (fun y z => by
        rw [hQ, hQ]
        exact Finset.sum_congr rfl fun i _ => hsym i y z) hpos _
    · exact Set.finite_empty
  · rintro B ⟨t, ht0, rfl⟩ hB y hy
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin m), S = Finset.univ.filter (fun i => 0 < t i) := ⟨_, rfl⟩
    have hBapp : ∀ z w : X, (∑ i, t i • GlobalTheory.PolFan.toReal (P i)) z w = ∑ i, t i * ((P i z w : ℤ) : ℝ) := by
      intro z w
      simp [GlobalTheory.PolFan.toReal, LinearMap.sum_apply]
    have hBpos : ∀ z : X, z ≠ 0 → 0 < ∑ i, t i * ((P i z z : ℤ) : ℝ) := by
      intro z hz
      have h1 := hB 1 ![z] (linearIndependent_unique_iff.mpr (by simpa using hz)) ![1] (by simp)
      simpa [hBapp] using h1
    have hterm : ∀ z : X, ∑ i, t i * ((P i z z : ℤ) : ℝ) = ∑ i ∈ S, t i * ((P i z z : ℤ) : ℝ) := by
      intro z
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · have h0 : t i = 0 := le_antisymm (not_lt.mp h) (ht0 i)
        simp [h0]
    have hpos : ∀ z : X, z ≠ 0 → 0 < Q S z z := by
      intro z hz
      rw [hQ]
      by_contra hle
      have h0 : ∑ i ∈ S, P i z z = 0 := le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun i _ => hnn i z)
      have hzero : ∀ i ∈ S, P i z z = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i z).mp h0
      have h1 := hBpos z hz
      rw [hterm, Finset.sum_eq_zero fun i hi => by rw [hzero i hi]; simp] at h1
      exact lt_irrefl _ h1
    obtain ⟨y', hy'G, ⟨x, hx⟩, hle⟩ := hGy y
    have hle' : ∀ i, P i y' y' ≤ P i y y := fun i => by
      have h1 : (P i y' y').toNat ≤ (P i y y).toNat := hle i
      have h2 := hnn i y
      have h3 := hnn i y'
      omega
    have hmin : ∑ i, t i * ((P i y y : ℤ) : ℝ) ≤ ∑ i, t i * ((P i y' y' : ℤ) : ℝ) := by
      have h1 := hy x
      rw [← hx, hBapp, hBapp] at h1
      exact h1
    have hd : ∀ i ∈ Finset.univ, 0 ≤ t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ)) := fun i _ =>
      mul_nonneg (ht0 i) (sub_nonneg.mpr (by exact_mod_cast hle' i))
    have hsum : ∑ i, t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ)) = 0 := by
      apply le_antisymm
      · simp only [mul_sub, Finset.sum_sub_distrib]
        linarith
      · exact Finset.sum_nonneg hd
    have heq : ∀ i ∈ S, P i y y ≤ P i y' y' := by
      intro i hi
      have hi0 := (Finset.sum_eq_zero_iff_of_nonneg hd).mp hsum i (Finset.mem_univ i)
      rw [hS, Finset.mem_filter] at hi
      have h4 : ((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp hi0 with h | h
        · exact absurd h hi.2.ne'
        · exact h
      have h5 : ((P i y y : ℤ) : ℝ) ≤ ((P i y' y' : ℤ) : ℝ) := by linarith
      exact_mod_cast h5
    have hbound : ∀ i, P i y' y' ≤ C := by
      intro i
      rw [hC]
      calc P i y' y' ≤ ∑ j, P j y' y' := Finset.single_le_sum (fun j _ => hnn j y') (Finset.mem_univ i)
        _ ≤ ∑ g ∈ hG.toFinset, ∑ j, P j g g :=
          Finset.single_le_sum (f := fun g => ∑ j, P j g g)
            (fun g _ => Finset.sum_nonneg fun j _ => hnn j g) (hG.mem_toFinset.mpr hy'G)
    refine Set.mem_iUnion.mpr ⟨S, ?_⟩
    rw [if_pos hpos]
    show Q S y y ≤ S.card * C
    rw [hQ]
    calc ∑ i ∈ S, P i y y ≤ ∑ i ∈ S, C := Finset.sum_le_sum fun i hi => (heq i hi).trans (hbound i)
      _ = S.card * C := by rw [Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntEqZeroOfForallTwoPowDvd
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem int_eq_zero_of_forall_two_pow_dvd (n : ℤ) (h : ∀ k : ℕ, (2 : ℤ) ^ k ∣ n) : n = 0 := by
  refine Int.eq_zero_of_abs_lt_dvd (h n.natAbs) ?_
  have h1 : n.natAbs < 2 ^ n.natAbs := Nat.lt_two_pow_self
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1

theorem exists_two_pow_smul_of_covers2 {X : Type} [AddCommGroup X] {ι : Type} {a : ι → X}
    (ha : Covers2 a) (d : X →+ X) (hd : ∀ i, d (a i) = 0) (k : ℕ) :
    ∀ y : X, ∃ z : X, d y = ((2 : ℤ) ^ k) • z := by
  induction k with
  | zero => exact fun y => ⟨d y, by simp⟩
  | succ k ih =>
    intro y
    obtain ⟨i, x, rfl⟩ := ha y
    obtain ⟨z, hz⟩ := ih x
    refine ⟨z, ?_⟩
    rw [map_add (f := _), map_add (f := _), hd, hz, zero_add, pow_succ, mul_smul, two_smul]
    simp only [two_smul, smul_add]

theorem addHom_eq_zero_of_covers2 {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {ι : Type} {a : ι → X} (ha : Covers2 a) (d : X →+ X) (hd : ∀ i, d (a i) = 0) : d = 0 := by
  ext y
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective (Finsupp.ext fun j => ?_)
  have : b.repr (d y) j = 0 := by
    refine int_eq_zero_of_forall_two_pow_dvd _ fun k => ?_
    obtain ⟨z, hz⟩ := exists_two_pow_smul_of_covers2 ha d hd k y
    exact ⟨b.repr z j, by rw [hz]; simp⟩
  simpa using this

theorem addHom_ext_of_covers2 {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {ι : Type} {a : ι → X} (ha : Covers2 a) {f g : X →+ X} (h : ∀ i, f (a i) = g (a i)) : f = g := by
  have := addHom_eq_zero_of_covers2 ha (f - g) (fun i => by simp [h i])
  exact sub_eq_zero.mp this

theorem finite_addHom_of_covers2 : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (ι : Type)
    [Finite ι] (a : ι → X), Covers2 a → ∀ F : Set X, F.Finite → {f : X →+ X | ∀ i, f (a i) ∈ F}.Finite := by
  intro X _ _ _ ι _ a ha F hF
  have hT : (Set.pi Set.univ fun _ : ι => F).Finite := Set.Finite.pi fun _ => hF
  refine Set.Finite.of_injOn (f := fun (f : X →+ X) (i : ι) => f (a i)) ?_ ?_ hT
  · exact fun f hf i _ => hf i
  · exact fun f _ g _ h => addHom_ext_of_covers2 ha fun i => congrFun h i

end GlobalTheory.CompanionTheory.Ar.Fan
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPsdFormsCoverContactSet
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem finite_free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    Module.Finite ℤ X ∧ Module.Free ℤ X := by
  have hfin : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O X)
  have hinj : Function.Injective s := fun x y h => by
    have := congrArg (Finsupp.linearCombination O id) h
    simpa using (LinearMap.congr_fun hs x).symm.trans (this.trans (LinearMap.congr_fun hs y))
  have htf : Module.IsTorsionFree ℤ X := Module.IsTorsionFree.of_smul_eq_zero fun r x hx => by
    by_cases hr : r = 0
    · exact Or.inl hr
    refine Or.inr (hinj ?_)
    rw [map_zero]
    ext c
    have h1 : r • s x = 0 := by
      rw [← map_zsmul s r x, hx, map_zero]
    have h2 : r • (s x c) = 0 := by simpa using DFunLike.congr_fun h1 c
    rw [zsmul_eq_mul] at h2
    have h3 : (r : O) ≠ 0 := by exact_mod_cast hr
    simpa using (mul_eq_zero.1 h2).resolve_left h3
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

theorem exists_fin_reindex {T : Type} [Finite T] {X : Type} [AddCommGroup X] (m' : T → ℕ)
    (u' : ∀ t, Fin (m' t) → LinearMap.BilinForm ℤ X) (hsym : ∀ t i y z, u' t i y z = u' t i z y)
    (hnn : ∀ t i y, 0 ≤ u' t i y y) :
    ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X),
      (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧
      ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∃ t, B ∈ rcone (u' t)) → ∃ j, B ∈ rcone (u j) := by
  obtain ⟨k, ⟨eq⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨k, fun j => m' (eq.symm j), fun j => u' (eq.symm j), fun j => hsym _, fun j => hnn _, ?_⟩
  rintro B ⟨t, ht⟩
  refine ⟨eq t, ?_⟩
  have key : ∀ t', t' = t → B ∈ rcone (u' t') := by
    rintro _ rfl
    exact ht
  exact key _ (eq.symm_apply_apply t)

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem isPosDef_pullR (e : X ≃ₗ[O] X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : IsPosDef B) :
    IsPosDef (pullR e.toLinearMap B) := by
  intro n x hx c hc
  let eZ : X ≃ₗ[ℤ] X := e.toAddEquiv.toIntLinearEquiv
  have h1 : LinearIndependent ℤ (fun i => e (x i)) := hx.map' eZ.toLinearMap eZ.ker
  simpa using hB n _ h1 c hc

theorem isMin2_pullR (e : X ≃ₗ[O] X) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (hy : IsMin2 B y) :
    IsMin2 (pullR e.toLinearMap B) (e.symm y) := by
  intro x
  have := hy (e x)
  simpa [pullR_apply, map_add (f := _)] using this

theorem exists_rcone_cover_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X),
    HasRedCover bar X → Covers2 a → ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X),
      (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧
      ∀ B ∈ contact bar a, IsPosDef B → ∃ j, B ∈ rcone (u j) := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a hR ha
  obtain ⟨hfin, hfree⟩ := finite_free_int_of_projective O X
  obtain ⟨k, n, P, hsym, hnn, hcov⟩ := hR
  choose F hF hmin using fun j => finite_isMin2 X (n j) (P j) (hsym j) (hnn j)
  have hU : (⋃ j, F j).Finite := Set.finite_iUnion hF
  have hS := finite_addHom_of_covers2 X ι a ha _ hU
  let S : Set (X →+ X) := {f : X →+ X | ∀ i, f (a i) ∈ ⋃ j, F j}
  have hSf : Finite S := hS
  let form : ∀ (t : (Fin k) × S), Fin (n t.1) → LinearMap.BilinForm ℤ X := fun t i =>
    (P t.1 i).compl₁₂ t.2.1.toIntLinearMap t.2.1.toIntLinearMap
  obtain ⟨K, m, u, h1, h2, h3⟩ := exists_fin_reindex (T := Fin k × S) (fun t => n t.1) form
    (fun t i y z => hsym _ _ _ _) (fun t i y => hnn _ _ _)
  refine ⟨K, m, u, h1, h2, fun B hB hpos => h3 B ?_⟩
  obtain ⟨e, j, c, hc, hE⟩ := hcov B hB.1
  let f : X →+ X := e.symm.toLinearMap.toAddMonoidHom
  have hf : f ∈ S := fun i => Set.mem_iUnion.2 ⟨j, hmin j _ ⟨c, hc, hE⟩ (isPosDef_pullR e hpos) _ (isMin2_pullR e (hB.2 i))⟩
  refine ⟨(j, ⟨f, hf⟩), c, hc, LinearMap.ext₂ fun y z => ?_⟩
  have h4 := LinearMap.congr_fun₂ hE (f y) (f z)
  simpa [f, form, LinearMap.sum_apply] using h4

end GlobalTheory.CompanionTheory.Ar.Fan
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPsdFormsCoverContactSetStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psd_forms_cover_contact_set : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X), (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧ ∀ B ∈ contact bar a, IsPosDef B → ∃ j, B ∈ rcone (u j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_rcone_cover_contact | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_rcone_cover_contact | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_rcone_cover_contact <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsBalancedFormsDominating
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsMin2IffFinite
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem isMin2_iff_finite : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (y : X),
    (∀ i x, 0 ≤ u i x x) → ∃ F : Finset X, ∀ B ∈ rcone u,
      (IsMin2 B y ↔ ∀ x ∈ F, B y y ≤ B (y + (x + x)) (y + (x + x))) := by
  intro X _ m u y hu
  obtain ⟨F, hF⟩ := GlobalTheory.dickson_finite_below_every (ι := X) m fun x i => (u i (y + (x + x)) (y + (x + x))).toNat
  refine ⟨F, ?_⟩
  rintro B ⟨t, ht, rfl⟩
  refine ⟨fun h x _ => h x, fun h x => ?_⟩
  obtain ⟨x', hx', hle⟩ := hF x
  refine (h x' hx').trans ?_
  have hval : ∀ a : X, (∑ i, t i • toReal (u i)) a a = ∑ i, t i * (u i a a : ℝ) := fun a => by
    simp [LinearMap.sum_apply]
  simp only [hval]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
  have h1 := hle i
  have h2 := hu i (y + (x' + x'))
  have h3 := hu i (y + (x + x))
  simp only at h1
  exact_mod_cast (by omega : u i (y + (x' + x')) (y + (x' + x')) ≤ u i (y + (x + x)) (y + (x + x)))

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsBalancedFormsDominating
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem contact_inter_rcone_spanned : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι]
    (a : ι → X) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) →
    ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧
      (∀ i, toReal (γ i) ∈ contact bar a) ∧ ∀ B ∈ contact bar a, B ∈ rcone u → B ∈ rcone γ := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a m u hsym hpsd
  classical
  choose F hF using fun i => isMin2_iff_finite X m u (a i) hpsd
  let A : Set (Fin m → ℤ) := ⋃ i, (fun (x : X) (k : Fin m) =>
    u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) '' (F i : Set X)
  let V : Set (Fin m → ℤ) := Set.range fun (p : O × X × X) (k : Fin m) =>
    u k (p.1 • p.2.1) p.2.2 - u k p.2.1 (bar p.1 • p.2.2)
  have hA : A.Finite := Set.finite_iUnion fun i => (F i).finite_toSet.image _
  obtain ⟨r, v, hv, -⟩ := GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints m A V hA
  have hval : ∀ (t : Fin m → ℝ) (y z : X), (∑ k, t k • toReal (u k)) y z = ∑ k, t k * (u k y z : ℝ) :=
    fun t y z => by simp [LinearMap.sum_apply]
  have hdiff : ∀ (t : Fin m → ℝ) (p p' q q' : X), ∑ k, (((u k p p' - u k q q' : ℤ)) : ℝ) * t k =
      (∑ k, t k • toReal (u k)) p p' - (∑ k, t k • toReal (u k)) q q' := fun t p p' q q' => by
    rw [hval, hval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  have hAiff : ∀ t : Fin m → ℝ, (∀ k, 0 ≤ t k) → ((∀ i, IsMin2 (∑ k, t k • toReal (u k)) (a i)) ↔
      ∀ b ∈ A, ∑ k, (b k : ℝ) * t k ≤ 0) := fun t ht => by
    constructor
    · intro h b hb
      obtain ⟨i, x, -, rfl⟩ : ∃ i, ∃ x ∈ (F i : Set X), (fun k : Fin m =>
          u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) = b := by
        simpa [A] using hb
      rw [hdiff]
      linarith [h i x]
    · intro h i
      refine (hF i _ ⟨t, ht, rfl⟩).2 fun x hx => ?_
      have := h _ (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)
      rw [hdiff] at this
      linarith
  have hViff : ∀ t : Fin m → ℝ, (∀ (c : O) (y z : X), (∑ k, t k • toReal (u k)) (c • y) z =
      (∑ k, t k • toReal (u k)) y (bar c • z)) ↔ ∀ b ∈ V, ∑ k, (b k : ℝ) * t k = 0 := fun t => by
    constructor
    · rintro h _ ⟨⟨c, y, z⟩, rfl⟩
      simp only []
      rw [hdiff, h, sub_self]
    · intro h c y z
      have := h _ ⟨(c, y, z), rfl⟩
      simp only [] at this
      rw [hdiff] at this
      linarith
  let γ : Fin r → LinearMap.BilinForm ℤ X := fun s => ∑ k, v s k • u k
  have hγ : ∀ s y z, γ s y z = ∑ k, (v s k : ℤ) * u k y z := fun s y z => by
    simp [γ, LinearMap.sum_apply]
  have hγr : ∀ s, toReal (γ s) = ∑ k, (v s k : ℝ) • toReal (u k) := fun s => LinearMap.ext₂ fun y z => by
    rw [hval, toReal_apply, hγ]
    push_cast
    rfl
  have hvs : ∀ s, (∀ k, (0 : ℝ) ≤ v s k) ∧ (∀ b ∈ A, ∑ k, (b k : ℝ) * (v s k : ℝ) ≤ 0) ∧
      (∀ b ∈ V, ∑ k, (b k : ℝ) * (v s k : ℝ) = 0) := fun s => by
    refine (hv fun k => (v s k : ℝ)).2 ⟨Pi.single s 1, fun j => ?_, ?_⟩
    · by_cases h : j = s
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · rw [Finset.sum_eq_single s (fun j _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
      simp
  have hbal : ∀ s, γ s ∈ balForms bar X := fun s => by
    refine mem_balForms.2 ⟨fun y z => ?_, fun c y z => ?_⟩
    · simp only [hγ, hsym _ y z]
    · have := (hViff _).2 (hvs s).2.2 c y z
      rw [← hγr] at this
      simpa using this
  have hnn : ∀ s y, 0 ≤ γ s y y := fun s y => by
    rw [hγ]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Int.natCast_nonneg _) (hpsd k y)
  refine ⟨r, γ, hbal, hnn, fun s => ⟨?_, fun i => ?_⟩, ?_⟩
  · simpa using GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![γ s] ![1] (by simpa using hbal s) (by simpa using hnn s) (by simp)
  · rw [hγr]
    exact (hAiff _ (hvs s).1).2 (hvs s).2.1 i
  · rintro _ hB ⟨t, ht, rfl⟩
    have hre := mem_realForms_of_mem_psdCone hB.1
    obtain ⟨c, hc, rfl⟩ := (hv t).1 ⟨ht, (hAiff t ht).1 hB.2, (hViff t).1 hre.2⟩
    refine ⟨c, hc, LinearMap.ext₂ fun y z => ?_⟩
    rw [hval]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hγ, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsBalancedFormsDominatingStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_balanced_forms_dominating : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) → ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧ (∀ i, toReal (γ i) ∈ contact bar a) ∧ ∀ B ∈ contact bar a, B ∈ rcone u → B ∈ rcone γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.contact_inter_rcone_spanned | exact GlobalTheory.CompanionTheory.Ar.Fan.contact_inter_rcone_spanned | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.contact_inter_rcone_spanned <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemRationalConeOfPerturbation
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemRationalConeOfPerturbation
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section SegCone

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]

theorem exists_indep_rep (v : ι → V) (n : ℕ) : ∀ (t : ι → ℝ), (∀ i, 0 ≤ t i) →
    (by classical exact (Finset.univ.filter (fun i => t i ≠ 0)).card) = n →
    ∃ (S : Finset ι) (s : ι → ℝ), LinearIndepOn ℝ v (S : Set ι) ∧ (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧
      ∑ i, s i • v i = ∑ i, t i • v i := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t ht hn
  set S := Finset.univ.filter (fun i => t i ≠ 0) with hS
  have hSt : ∀ i, i ∉ S → t i = 0 := fun i hi => by simpa [hS] using hi
  by_cases hli : LinearIndepOn ℝ v (S : Set ι)
  · exact ⟨S, t, hli, ht, hSt, rfl⟩
  rw [linearIndepOn_finset_iff] at hli
  push_neg at hli
  obtain ⟨f, hf0, i₀, hi₀, hfi₀⟩ := hli
  obtain ⟨g, hg0, hgS, hgpos⟩ : ∃ g : ι → ℝ, (∑ i, g i • v i = 0) ∧ (∀ i, i ∉ S → g i = 0) ∧ 0 < g i₀ := by
    refine ⟨fun i => if i ∈ S then f i * f i₀ else 0, ?_, fun i hi => by simp [hi], ?_⟩
    · have : ∑ i, (if i ∈ S then f i * f i₀ else 0) • v i = ∑ i ∈ S, (f i * f i₀) • v i := by
        rw [← Finset.sum_subset (Finset.subset_univ S)
          (fun i _ hi => by simp [hi])]
        exact Finset.sum_congr rfl fun i hi => by simp [hi]
      rw [this]
      have h2 : ∑ i ∈ S, (f i * f i₀) • v i = f i₀ • ∑ i ∈ S, f i • v i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
      rw [h2, hf0, smul_zero]
    · simp only [hi₀, if_true]
      exact mul_self_pos.mpr hfi₀
  have hP : (S.filter (fun i => 0 < g i)).Nonempty := ⟨i₀, by simp [hi₀, hgpos]⟩
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image _ (fun i => t i / g i) hP
  have hjS : j ∈ S := (Finset.mem_filter.mp hjP).1
  have hgj : 0 < g j := (Finset.mem_filter.mp hjP).2
  set l := t j / g j with hl
  have hl0 : 0 ≤ l := div_nonneg (ht j) hgj.le
  have ht' : ∀ i, 0 ≤ t i - l * g i := fun i => by
    by_cases hgi : 0 < g i
    · have hiS : i ∈ S := by
        by_contra hi
        rw [hgS i hi] at hgi
        exact lt_irrefl _ hgi
      have := hjmin i (Finset.mem_filter.mpr ⟨hiS, hgi⟩)
      have h3 : l * g i ≤ t i := (le_div_iff₀ hgi).mp this
      linarith
    · have : l * g i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl0 (not_lt.mp hgi)
      linarith [ht i]
  have hlt : (Finset.univ.filter (fun i => t i - l * g i ≠ 0)).card < n := by
    rw [← hn]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, hjS, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [hl, div_mul_cancel₀ _ hgj.ne', sub_self]
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hiS
      apply hi
      rw [hSt i hiS, hgS i hiS]
      simp
  obtain ⟨S', s, h1, h2, h3, h4⟩ := ih _ hlt (fun i => t i - l * g i) ht' (by congr)
  refine ⟨S', s, h1, h2, h3, h4.trans ?_⟩
  have : ∑ i, (t i - l * g i) • v i = ∑ i, t i • v i - l • ∑ i, g i • v i := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [sub_smul, mul_smul]
  rw [this, hg0, smul_zero, sub_zero]

theorem seg_mem_cone (v : ι → V) (B B₀ : V)
    (h : ∀ ε : ℝ, 0 < ε → ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ B + ε • B₀ = ∑ i, t i • v i) :
    ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ B = ∑ i, t i • v i := by
  classical
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have h' : ∀ k : ℕ, ∃ (S : Finset ι) (s : ι → ℝ), LinearIndepOn ℝ v (S : Set ι) ∧ (∀ i, 0 ≤ s i) ∧
      (∀ i, i ∉ S → s i = 0) ∧ B + (1 / ((k : ℝ) + 1)) • B₀ = ∑ i, s i • v i := fun k => by
    obtain ⟨t, ht, hx⟩ := h _ (hpos k)
    obtain ⟨S, s, h1, h2, h3, h4⟩ := exists_indep_rep v _ t ht rfl
    exact ⟨S, s, h1, h2, h3, hx.trans h4.symm⟩
  choose S s hli hs hS hx using h'
  obtain ⟨S₀, hinf⟩ := Finite.exists_infinite_fiber S
  have hI : (S ⁻¹' {S₀}).Infinite := Set.infinite_coe_iff.mp hinf
  obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := hI.nontrivial
  have hk₁' : S k₁ = S₀ := hk₁
  have hk₂' : S k₂ = S₀ := hk₂
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hε
  have hd : ε k₁ - ε k₂ ≠ 0 := by
    intro h0
    apply hne
    have h1 : ε k₁ = ε k₂ := sub_eq_zero.mp h0
    simp only [hε] at h1
    have h2 : (k₁ : ℝ) + 1 ≠ 0 := by positivity
    have h3 : (k₂ : ℝ) + 1 ≠ 0 := by positivity
    field_simp at h1
    have : (k₂ : ℝ) = k₁ := by linarith
    exact_mod_cast this.symm
  set b : ι → ℝ := fun i => (s k₁ i - s k₂ i) / (ε k₁ - ε k₂) with hb
  set a : ι → ℝ := fun i => s k₁ i - ε k₁ * b i with ha
  have hB₀ : B₀ = ∑ i, b i • v i := by
    have h1 : (ε k₁ - ε k₂) • B₀ = ∑ i, (s k₁ i - s k₂ i) • v i := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hx k₁, ← hx k₂]
      simp only [hε]
      abel
    have h2 : B₀ = (ε k₁ - ε k₂)⁻¹ • ∑ i, (s k₁ i - s k₂ i) • v i := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hb]
    congr 1
    simp only
    rw [div_eq_mul_inv, mul_comm]
  have hB : B = ∑ i, a i • v i := by
    have h1 : ∑ i, a i • v i = ∑ i, s k₁ i • v i - ε k₁ • ∑ i, b i • v i := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [ha]; simp only; rw [sub_smul, mul_smul]
    rw [h1, ← hB₀, ← hx k₁]
    simp only [hε]
    abel
  have hb0 : ∀ i, i ∉ S₀ → b i = 0 := fun i hi => by
    simp only [hb]
    rw [hS k₁ i (hk₁' ▸ hi), hS k₂ i (hk₂' ▸ hi)]
    simp
  have ha0 : ∀ i, i ∉ S₀ → a i = 0 := fun i hi => by
    simp only [ha]
    rw [hb0 i hi, hS k₁ i (hk₁' ▸ hi)]
    simp
  have hcoord : ∀ k, S k = S₀ → ∀ i ∈ S₀, 0 ≤ a i + ε k * b i := fun k hk i hi => by
    have hz : ∑ j ∈ S₀, (a j + ε k * b j - s k j) • v j = 0 := by
      rw [Finset.sum_subset (Finset.subset_univ S₀) (fun j _ hj => by
        rw [ha0 j hj, hb0 j hj, hS k j (hk ▸ hj)]; simp)]
      have h1 : ∑ j, (a j + ε k * b j - s k j) • v j =
          ∑ j, a j • v j + ε k • ∑ j, b j • v j - ∑ j, s k j • v j := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [sub_smul, add_smul, mul_smul]
      rw [h1, ← hB, ← hB₀, ← hx k]
      simp only [hε]
      abel
    have hl := hli k
    rw [hk, linearIndepOn_finset_iff] at hl
    have := hl _ hz i hi
    have h0 := hs k i
    linarith
  refine ⟨a, fun i => ?_, hB⟩
  by_cases hi : i ∈ S₀
  · by_contra hneg
    have hai : a i < 0 := not_le.mp hneg
    obtain ⟨N, hN⟩ := exists_nat_gt (|b i| / (-a i))
    obtain ⟨k, hk, hNk⟩ := hI.exists_gt N
    have hc := hcoord k hk i hi
    have hna : 0 < -a i := by linarith
    have h1 : |b i| < N * (-a i) := (div_lt_iff₀ hna).mp hN
    have h2 : (N : ℝ) < (k : ℝ) + 1 := by
      have : (N : ℝ) < k := by exact_mod_cast hNk
      linarith
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h3 : |b i| < ((k : ℝ) + 1) * (-a i) := lt_trans h1 (mul_lt_mul_of_pos_right h2 hna)
    have h4 : ε k * b i < -a i := by
      simp only [hε]
      rw [one_div, inv_mul_lt_iff₀ hk1]
      exact lt_of_le_of_lt (le_abs_self _) h3
    linarith
  · rw [ha0 i hi]

end SegCone

theorem rcone_closed_seg (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (h : ∀ ε : ℝ, 0 < ε → B + ε • B₀ ∈ rcone γ) : B ∈ rcone γ :=
  seg_mem_cone (fun i => toReal (γ i)) B B₀ h

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemRationalConeOfPerturbationStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rational_cone_of_perturbation : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ ε : ℝ, 0 < ε → B + ε • B₀ ∈ rcone γ) → B ∈ rcone γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg | exact GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsPosDefAddAndMemPsdCone
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y] :
    Module.Finite ℤ Y ∧ Module.Free ℤ Y := by
  have hfin : Module.Finite ℤ Y := Module.Finite.trans O Y
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O Y)
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := Finsupp.linearCombination O id) (fun y => by
    simpa using LinearMap.congr_fun hs y)
  have htf : Module.IsTorsionFree ℤ Y := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n y h
    by_contra hc
    push_neg at hc
    have h1 : ((n : O)) • y = 0 := by rw [Int.cast_smul_eq_zsmul]; exact h
    have h2 : (n : O) • s y = 0 := by rw [← map_smul, h1, map_zero]
    have hy : s y ≠ 0 := fun h0 => hc.2 (hinj (by rw [h0, map_zero]))
    obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hy
    have h3 := DFunLike.congr_fun h2 a
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h3 ha
    exact (mul_ne_zero (Int.cast_ne_zero.2 hc.1) ha) h3
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

theorem sum_nonneg_of_isPosDef {Y ι : Type} [AddCommGroup Y] [Fintype ι] (b : Module.Basis ι ℤ Y)
    {B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ} (h : IsPosDef B) {n : ℕ} (y : Fin n → Y) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * B (y i) (y j) := by
  have hy : ∀ i j, B (y i) (y j) = ∑ k, ∑ l, (b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l) := fun i j => by
    conv_lhs => rw [← b.sum_repr (y i), ← b.sum_repr (y j)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have key : ∑ i, ∑ j, c i * c j * B (y i) (y j) = ∑ k, ∑ l, (∑ i, c i * (b.repr (y i) k : ℝ)) *
      (∑ i, c i * (b.repr (y i) l : ℝ)) * B (b k) (b l) := by
    symm
    simp only [hy, Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ k, ∑ l, ∑ i, ∑ j, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, ∑ i, ∑ j, ∑ l, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [key]
  by_cases hd : (fun k => ∑ i, c i * (b.repr (y i) k : ℝ)) = 0
  · have hd' : ∀ k, ∑ i, c i * (b.repr (y i) k : ℝ) = 0 := fun k => congrFun hd k
    simp [hd']
  · exact ((isPosDef_iff_basis b B).1 h _ hd).le

theorem sum_nonneg_of_mem_psdCone (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X))
    {n : ℕ} (x : Fin n → X) (c : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, c i * c j * B (x i) (x j) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, -, h1, h2⟩ := hB
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  obtain ⟨_, _⟩ := free_int_of_projective O X₁
  simp only [h2]
  exact sum_nonneg_of_isPosDef (Module.Free.chooseBasis ℤ X₁) h1 (fun i => r (x i)) c

theorem isPosDef_add_and_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hB : B ∈ psdCone (bar := bar) (X := X)) (hB₀ : B₀ ∈ realForms bar X) (h₀ : IsPosDef B₀) :
    IsPosDef (B + B₀) ∧ B + B₀ ∈ psdCone (bar := bar) (X := X) := by
  have hpos : IsPosDef (B + B₀) := fun n x hx c hc => by
    have h1 := sum_nonneg_of_mem_psdCone O hB x c
    have h2 := h₀ n x hx c hc
    have h3 : ∑ i, ∑ j, c i * c j * (B + B₀) (x i) (x j) =
        ∑ i, ∑ j, c i * c j * B (x i) (x j) + ∑ i, ∑ j, c i * c j * B₀ (x i) (x j) := by
      simp only [LinearMap.add_apply, mul_add, Finset.sum_add_distrib]
    rw [h3]
    exact add_pos_of_nonneg_of_pos h1 h2
  exact ⟨hpos, hpos.mem_psdCone (add_mem (mem_realForms_of_mem_psdCone hB) hB₀)⟩

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpansOfPosDef
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section SlopeTestRemainingChoices

variable {X : Type} [AddCommGroup X]

theorem IsMin2.add {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (h : IsMin2 B y) (h' : IsMin2 B' y) : IsMin2 (B + B') y :=
  fun x => by
    simpa only [LinearMap.add_apply] using add_le_add (h x) (h' x)

theorem IsMin2.smul {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (h : IsMin2 B y) {t : ℝ} (ht : 0 ≤ t) : IsMin2 (t • B) y :=
  fun x => by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left (h x) ht

theorem isPosDef_smul_of_pos {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : IsPosDef B) {t : ℝ} (ht : 0 < t) : IsPosDef (t • B) :=
  fun n x hx c hc => by
    have key : ∑ i, ∑ j, c i * c j * (t • B) (x i) (x j) = t * ∑ i, ∑ j, c i * c j * B (x i) (x j) := by
      simp only [LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [key]
    exact mul_pos ht (h n x hx c hc)

theorem rcone_subset_sigma {k : ℕ} {s : Fin k → ℕ} (γ : ∀ j, Fin (s j) → LinearMap.BilinForm ℤ X) {N : ℕ}
    (e : (Σ j, Fin (s j)) ≃ Fin N) (j : Fin k) :
    rcone (γ j) ⊆ rcone (fun i => γ (e.symm i).1 (e.symm i).2) := by
  rintro B ⟨t, ht, rfl⟩
  have hinj : Function.Injective (fun b : Fin (s j) => (⟨j, b⟩ : Σ j, Fin (s j))) := fun b c h => by simpa using h
  let T : (Σ j, Fin (s j)) → ℝ := Function.extend (fun b : Fin (s j) => (⟨j, b⟩ : Σ j, Fin (s j))) t 0
  have hT : ∀ b, T ⟨j, b⟩ = t b := fun b => hinj.extend_apply t 0 b
  have hT0 : ∀ a, a ≠ j → ∀ b, T ⟨a, b⟩ = 0 := fun a ha b => by
    refine (Function.extend_apply' _ _ _ ?_).trans rfl
    rintro ⟨c, hc⟩
    exact ha (congrArg Sigma.fst hc).symm
  have hTn : ∀ p, 0 ≤ T p := fun ⟨a, b⟩ => by
    by_cases ha : a = j
    · subst ha
      rw [hT]
      exact ht b
    · rw [hT0 a ha]
  refine ⟨fun i => T (e.symm i), fun i => hTn _, ?_⟩
  rw [e.symm.sum_comp (fun p => T p • toReal (γ p.1 p.2)), Fintype.sum_sigma,
    Finset.sum_eq_single j (fun a _ ha => Finset.sum_eq_zero fun b _ => by rw [hT0 a ha, zero_smul])
      (fun h => (h (Finset.mem_univ j)).elim)]
  exact Finset.sum_congr rfl fun b _ => by rw [hT]

end SlopeTestRemainingChoices

theorem isSpanned_contact_of_posDef : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → (∃ B₀ ∈ contact bar a, IsPosDef B₀) → IsSpanned bar (contact bar a) := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a hR hC ⟨B₀, hB₀, hd⟩
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨k, m, u, hsym, hnn, hcov⟩ := GlobalTheory.T.exists_psd_forms_cover_contact_set O bar X ι a hR hC
  choose s γ hbal hγnn hγK hsub using fun j => GlobalTheory.T.exists_balanced_forms_dominating O bar X ι a (m j) (u j) (hsym j) (hnn j)
  let e := Fintype.equivFin (Σ j, Fin (s j))
  refine ⟨_, fun i => γ (e.symm i).1 (e.symm i).2, fun i => hbal _ _, fun i y => hγnn _ _ _, fun i => hγK _ _,
    fun B hB => ?_⟩
  refine GlobalTheory.T.mem_rational_cone_of_perturbation X _ _ B B₀ fun ε hε => ?_
  have hεd : IsPosDef (ε • B₀) := isPosDef_smul_of_pos hd hε
  have hεr : ε • B₀ ∈ realForms bar X := (realForms bar X).smul_mem ε (mem_realForms_of_mem_psdCone hB₀.1)
  obtain ⟨hpd, hps⟩ := isPosDef_add_and_mem_psdCone O bar X B (ε • B₀) hB.1 hεr hεd
  have hmem : B + ε • B₀ ∈ contact bar a := ⟨hps, fun i => (hB.2 i).add ((hB₀.2 i).smul hε.le)⟩
  obtain ⟨j, hj⟩ := hcov _ hmem hpd
  exact rcone_subset_sigma γ e j (hsub j _ hmem hj)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpansOfPosDefStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.contact_set_spans_of_pos_def : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → (∃ B₀ ∈ contact bar a, IsPosDef B₀) → IsSpanned bar (contact bar a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef | exact GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef <;> assumption)
end

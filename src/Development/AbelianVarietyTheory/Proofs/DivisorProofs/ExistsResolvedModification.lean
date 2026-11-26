module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedSmoothProjModificationOffO
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedSmoothProjModificationOffO
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS

set_option autoImplicit false

namespace GlobalTheory.ModifGeomConn

theorem geometricallyConnected_of_geometricallyIrreducible {X Y : Scheme.{0}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  infer_instance

theorem geometricallyConnected_modif : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  intro F _ X _ sX n _ U M _ _ hU
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have : GeometricallyIntegral sX := GlobalTheory.geometricallyIntegral_of_smooth sX
  obtain ⟨x, hx⟩ := hU
  have : Surjective (U.ι ≫ sX) := ⟨fun s => ⟨⟨x, hx⟩, Subsingleton.elim _ _⟩⟩
  have h2 : GeometricallyConnected (U.ι ≫ sX) := geometricallyConnected_of_geometricallyIrreducible _
  have := M.iso
  have h3 : GeometricallyConnected (M.opn.ι ≫ M.str) := by
    have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ sX) := by
      rw [Modif.str, ← Category.assoc, ← Category.assoc, morphismRestrict_ι]
    rw [e]
    rw [GeometricallyConnected.eq_geometrically] at h2 ⊢
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 h2
  exact GlobalTheory.CompactVar.geometricallyConnected_of_denseRange M.opn.ι M.str
    (by rw [Scheme.Opens.range_ι]; exact M.dense)

end GlobalTheory.ModifGeomConn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedSmoothProjModificationOffOStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  first | exact @GlobalTheory.ModifGeomConn.geometricallyConnected_modif | exact GlobalTheory.ModifGeomConn.geometricallyConnected_modif | (intros; apply GlobalTheory.ModifGeomConn.geometricallyConnected_modif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationExtendingMapFromOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorIdealSheafPrincipalisingFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorIdealSheafPrincipalisingFamily
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier

namespace GlobalTheory.DenomIdeal

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (w : ι → X.functionField)

def IsDen (V : X.Opens) (a : Γ(X, V)) : Prop :=
  ∀ h : genericPoint X ∈ V, ∀ j, ∀ y ∈ V, RegAt y (fnOf V h a * w j)

def gens (V : X.Opens) : Set Γ(X, V) :=
  {b | ∃ a, IsDen w V a ∧ ∃ j, ∀ h : genericPoint X ∈ V, fnOf V h b = fnOf V h a * w j}

def idealOn (V : X.Opens) : Ideal Γ(X, V) := Ideal.span (gens w V)

variable {w}

theorem IsDen.res {U V : X.Opens} (e : V ≤ U) {a : Γ(X, U)} (ha : IsDen w U a) :
    IsDen w V (resG X e a) := by
  intro h j y hy
  rw [fnOf_resG]
  exact ha (e h) j y (e hy)

theorem res_mem_gens {U V : X.Opens} (e : V ≤ U) {b : Γ(X, U)} (hb : b ∈ gens w U) :
    resG X e b ∈ gens w V := by
  obtain ⟨a, ha, j, hj⟩ := hb
  exact ⟨resG X e a, ha.res e, j, fun h => by rw [fnOf_resG, fnOf_resG, hj]⟩

theorem mem_map_of_mem_gens_basicOpen [Fintype ι] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    {b : Γ(X, X.basicOpen f)} (hb : b ∈ gens w (X.basicOpen f)) :
    b ∈ (idealOn w U).map (resG X (X.basicOpen_le f)) := by
  by_cases hg : genericPoint X ∈ X.basicOpen f
  swap
  · have : b = 0 := Cartier.fn_ext fun h => (hg h).elim
    rw [this]; exact zero_mem _
  have hU' : genericPoint X ∈ U := X.basicOpen_le f hg
  have := hU.isLocalization_basicOpen f
  obtain ⟨a', ha', j, hj⟩ := hb
  obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) a'
  have e' : fnOf _ hg a' * fnOf U hU' f ^ n = fnOf U hU' a := by
    have := congrArg (fnOf _ hg) e
    simp only [map_mul, map_pow] at this
    change fnOf _ hg a' * fnOf _ hg (resG X (X.basicOpen_le f) f) ^ n =
      fnOf _ hg (resG X (X.basicOpen_le f) a) at this
    rwa [fnOf_resG, fnOf_resG] at this
  have hreg : ∀ i, ∀ x ∈ X.basicOpen f, RegAt x (fnOf U hU' a * w i) := fun i x hx => by
    rw [← e', mul_right_comm]
    exact (ha' hg i x hx).mul (GlobalTheory.TrueGeo.SmallSec.regAt_pow (regAt_fnOf (X.basicOpen_le f hx) hU' f) n)
  have := fun i => GlobalTheory.InvertIdeal.exists_mul_pow hU hU' f hg (hreg i)
  choose m γ hγ using this
  set M := ∑ i, m i
  have hm : ∀ i, m i ≤ M := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have key : ∀ i, fnOf U hU' (γ i * f ^ (M - m i)) = fnOf U hU' (a * f ^ M) * w i := fun i => by
    rw [map_mul, map_mul, hγ, map_pow, map_pow, ← Nat.add_sub_cancel' (hm i), pow_add]
    simp only [Nat.add_sub_cancel_left]
    ring
  have hden : IsDen w U (a * f ^ M) := fun h i y hy => by
    rw [← key i]; exact regAt_fnOf hy _ _
  have hgen : γ j * f ^ (M - m j) ∈ gens w U := ⟨_, hden, j, fun h => key j⟩
  have hu : IsUnit (resG X (X.basicOpen_le f) f) := IsLocalization.Away.algebraMap_isUnit f
  have hb0 : resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) = b * resG X (X.basicOpen_le f) f ^ (n + M) :=
    Cartier.fn_ext fun h => by
      rw [fnOf_resG, key, map_mul (fnOf _ h), map_pow, fnOf_resG, hj, map_mul, map_pow, ← e']
      ring
  have hb : b = resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) * ((hu.unit⁻¹ : _) : Γ(X, X.basicOpen f)) ^ (n + M) := by
    rw [hb0, mul_assoc, ← mul_pow, hu.mul_val_inv, one_pow, mul_one]
  rw [hb]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hgen))


variable (w) in
def idealSheaf [Fintype ι] : X.IdealSheafData where
  ideal U := idealOn w U.1
  map_ideal_basicOpen U f := by
    show Ideal.map (resG X (X.basicOpen_le f)) (idealOn w U.1) = idealOn w (X.basicOpen f)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 fun b hb => ?_
      exact Ideal.subset_span (res_mem_gens (X.basicOpen_le f) hb)
    · exact Ideal.span_le.2 fun b hb => mem_map_of_mem_gens_basicOpen U.2 f hb

theorem idealSheaf_ne_bot [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) : idealSheaf w ≠ ⊥ := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hηW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hW' : IsAffineOpen W := hW
  choose β γ hβ hγ using fun j => GlobalTheory.InvertIdeal.exists_denom hW' hηW hηW (regAt_genericPoint (w j))
  have hβ0 : ∀ j, fnOf W hηW (β j) ≠ 0 := fun j => ((unitAt_fnOf_iff hηW hηW (β j)).2 (hβ j)).ne_zero
  set d := ∏ j, β j
  have hd : ∀ j, fnOf W hηW d * w j = fnOf W hηW (γ j) * fnOf W hηW (∏ i ∈ Finset.univ.erase j, β i) := fun j => by
    rw [hγ, show d = β j * ∏ i ∈ Finset.univ.erase j, β i from (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm,
      map_mul]
    ring
  have hden : IsDen w W d := fun h j y hy => by
    rw [hd j]; exact (regAt_fnOf hy _ _).mul (regAt_fnOf hy _ _)
  have hgen : d ∈ gens w W := ⟨d, hden, i₀, fun h => by rw [h1, mul_one]⟩
  have hd0 : fnOf W hηW d ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => hβ0 j
  intro hbot
  have hmem : d ∈ (idealSheaf w).ideal ⟨W, hW⟩ := Ideal.subset_span hgen
  rw [hbot] at hmem
  exact hd0 (by rw [(Ideal.mem_bot).1 hmem, map_zero])

theorem notMem_support [Finite ι] [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) {y : X} {k : ι} (hk : w k ≠ 0)
    (hy : ∀ j, RegAt y (w j / w k)) : y ∉ (idealSheaf w).support := by
  obtain ⟨V, hyV, ha⟩ := GlobalTheory.InvertIdeal.exists_common_open hy
  choose a ha using ha
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
  have e : W ≤ V := hWV
  have hηW : genericPoint X ∈ W := gen_mem hyW
  have hfa : ∀ j, fnOf W hηW (resG X e (a j)) = w j / w k := fun j => by rw [fnOf_resG, ha]
  have hden : IsDen w W (resG X e (a i₀)) := fun h j x hx => by
    rw [hfa, h1, one_div, inv_mul_eq_div, ← hfa j]; exact regAt_fnOf hx _ _
  have hgen : (1 : Γ(X, W)) ∈ gens w W :=
    ⟨_, hden, k, fun h => by rw [map_one, hfa, h1, one_div, inv_mul_cancel₀ hk]⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hyW, Scheme.mem_zeroLocus_iff]
  intro H
  exact H 1 (Ideal.subset_span hgen) (by rw [Scheme.basicOpen_one]; exact hyW)

theorem fnOf_appLE {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X) {W : X.Opens} {A : Y'.Opens} (hA : A ≤ s ⁻¹ᵁ W)
    (hA' : genericPoint Y' ∈ A) (hW : genericPoint X ∈ W) (c : Γ(X, W)) :
    fnOf A hA' ((s.appLE W A hA).hom c) = GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hW c) := by
  rw [GlobalTheory.TrueGeo.SmallSec.fnMap_fnOf s hη hW (hA hA'), ← fnOf_resG hA hA']
  rfl

theorem exists_dvd_of_effCartier [Fintype ι] {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X)
    (hE : ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier ((idealSheaf w).comap s)) (y' : Y') :
    ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k) ≠ 0 ∧ ∀ j,
      RegAt y' (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k)) := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (s y')) isOpen_univ
  obtain ⟨U0, f0, sectionFrameQuotient, hf0, hI0⟩ := hE y'
  obtain ⟨t, htle, hyt⟩ := U0.2.exists_basicOpen_le (V := U0.1 ⊓ s ⁻¹ᵁ W) ⟨y', sectionFrameQuotient, hyW⟩ sectionFrameQuotient
  have hAW : Y'.basicOpen t ≤ s ⁻¹ᵁ W := fun x hx => (htle hx).2
  have hA' : genericPoint Y' ∈ Y'.basicOpen t := gen_mem hyt
  have hηW : genericPoint X ∈ W := gen_mem hyW
  set F := resG Y' (Y'.basicOpen_le t) f0 with hFdef
  have hIA : ((idealSheaf w).comap s).ideal (Y'.affineBasicOpen t) = Ideal.span {F} := by
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, hI0, Ideal.map_span, Set.image_singleton]
  have hmap : Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W) = Ideal.span {F} := by
    rw [← hIA, GlobalTheory.Principalise.comapIdealAffine _ s ⟨W, hW⟩ (Y'.affineBasicOpen t) hAW]
    rfl
  set φ := fnOf (Y'.basicOpen t) hA'
  set w' := fun j => GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) with hw'
  have hφ : ∀ c : Γ(X, W), φ ((s.appLE W (Y'.basicOpen t) hAW).hom c) =
      GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW c) := fun c => fnOf_appLE s hη hAW hA' hηW c
  have hF0 : φ F ≠ 0 := by
    have hU0 : genericPoint Y' ∈ U0.1 := Y'.basicOpen_le t hA'
    have : Nontrivial Γ(Y', U0.1) := (fnOf U0.1 hU0).domain_nontrivial
    rw [hFdef, fnOf_resG]
    intro h
    exact nonZeroDivisors.ne_zero hf0 (fnOf_injective _ hU0 (h.trans (map_zero _).symm))
  have key : ∀ x ∈ Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W),
      ∃ C : ι → Y'.functionField, φ x = ∑ j, w' j * C j ∧ ∀ i j, ∃ r : Γ(Y', Y'.basicOpen t),
        w' i * C j = φ F * φ r := by
    intro x hx
    rw [idealOn, Ideal.map_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, ⟨a, ha, j₀, hb⟩, rfl⟩ := hx
      refine ⟨Pi.single j₀ (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW a)), ?_, fun i j => ?_⟩
      · rw [hφ, hb hηW, map_mul, Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
          (by simp), Pi.single_eq_same, mul_comm]
      · by_cases hj : j = j₀
        · subst hj
          rw [Pi.single_eq_same]
          obtain ⟨bi, hbi⟩ := exists_fnOf_eq hηW fun y hy => ha hηW i y hy
          have hmem : (s.appLE W (Y'.basicOpen t) hAW).hom bi ∈ Ideal.span {F} :=
            hmap ▸ Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, ha, i, fun _ => hbi⟩)
          obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
          refine ⟨r, ?_⟩
          rw [hw', ← map_mul, mul_comm (w i), ← hbi, ← hφ, ← hr, map_mul, mul_comm]
        · rw [Pi.single_eq_of_ne hj, mul_zero]
          exact ⟨0, by rw [map_zero, mul_zero]⟩
    | zero => exact ⟨0, by simp, fun i j => ⟨0, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨C, hC, hC'⟩ := hx
      obtain ⟨D, hD, hD'⟩ := hy
      refine ⟨C + D, by rw [map_add (f := _), hC, hD, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, mul_add],
        fun i j => ?_⟩
      obtain ⟨r, hr⟩ := hC' i j
      obtain ⟨r', hr'⟩ := hD' i j
      exact ⟨r + r', by simp only [Pi.add_apply, mul_add, hr, hr', map_add (f := _)]⟩
    | smul c x _ hx =>
      obtain ⟨C, hC, hC'⟩ := hx
      refine ⟨fun j => φ c * C j, ?_, fun i j => ?_⟩
      · rw [smul_eq_mul, map_mul, hC, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · obtain ⟨r, hr⟩ := hC' i j
        refine ⟨c * r, ?_⟩
        rw [map_mul, mul_left_comm, hr]
        ring
  obtain ⟨C, hC, hC'⟩ := key F (hmap ▸ Ideal.mem_span_singleton_self F)
  choose r hr using hC'
  have hreg : ∀ i j, RegAt y' (w' i * (C j / φ F)) := fun i j => by
    rw [mul_div_assoc', hr, mul_div_cancel_left₀ _ hF0]
    exact regAt_fnOf hyt _ _
  have he1 : ∑ j, (fun _ => (1 : Y'.functionField)) j * (w' j * (C j / φ F)) = 1 := by
    simp only [one_mul, mul_div_assoc']
    rw [← Finset.sum_div, ← hC, div_self hF0]
  obtain ⟨k, hk⟩ := GlobalTheory.InvertIdeal.exists_unitAt (x := y') (c := fun _ => 1)
    (g := fun j => w' j * (C j / φ F)) (fun _ => ⟨1, map_one _⟩) (fun j => hreg j j) he1
  have hk0 : w' k * (C k / φ F) ≠ 0 := hk.ne_zero
  refine ⟨k, left_ne_zero_of_mul hk0, fun j => ?_⟩
  have e : w' j / w' k = (w' j * (C k / φ F)) * (w' k * (C k / φ F))⁻¹ := by
    have h2 : C k / φ F ≠ 0 := right_ne_zero_of_mul hk0
    rw [← div_eq_mul_inv, mul_div_mul_right _ _ h2]
  change RegAt y' (w' j / w' k)
  rw [e]
  exact (hreg j k).mul hk.inv.regAt

theorem exists_idealSheaf : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  intro Y _ N w i₀ U h1 hU
  refine ⟨idealSheaf w, idealSheaf_ne_bot i₀ h1, fun y hy => ?_, fun Y' _ s hη hE y' =>
    exists_dvd_of_effCartier s (specializes_of_eq hη) hE y'⟩
  obtain ⟨k, hk, hreg⟩ := hU y hy
  exact notMem_support i₀ h1 hk hreg

end GlobalTheory.DenomIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorIdealSheafPrincipalisingFamilyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  first | exact @GlobalTheory.DenomIdeal.exists_idealSheaf | exact GlobalTheory.DenomIdeal.exists_idealSheaf | (intros; apply GlobalTheory.DenomIdeal.exists_idealSheaf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationExtendingMapFromOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section

theorem GlobalTheory.CompHS.exists_modif_map_of_open : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (Y T : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) (t : T ⟶ Sp F) (U : Y.Opens) (r₀ : U.toScheme ⟶ T), SmoothOfRelativeDimension d p → IsProjOver p → IsProjOver t → (U : Set Y).Nonempty → r₀ ≫ t = U.ι ≫ p → ∃ (M : Modif p U d) (r : M.X ⟶ T), IsIntegral M.X ∧ r ≫ t = M.str ∧ M.opn.ι ≫ r = (M.σ ∣_ U) ≫ r₀ := by
  intro hPr F _ _ Y T _ p d t U r₀ hs hpY hpT hU hr
  obtain ⟨N, i, hi, hit⟩ := hpT
  have hφ : (r₀ ≫ i) ≫ PSpace.str F N = U.ι ≫ p := by rw [Category.assoc, hit, hr]
  obtain ⟨w, i₀, hw₀, hwU, hext⟩ := GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace F Y p N U (r₀ ≫ i) hφ hU
  obtain ⟨I, hI0, hIU, hC⟩ := GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family Y N w i₀ U hw₀ hwU
  obtain ⟨Y', s, hY', hs', hp', -, hiso, hEC, -⟩ := hPr F d Y p inferInstance hs hpY I hI0
  have hUle : U ≤ I.support.compl := fun y hy => hIU y hy
  have hisoU : IsIso (s ∣_ U) := ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le s hUle
  have : Nonempty U := hU.to_subtype
  let c : U.toScheme ⟶ Y' := inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι
  have hc : c ≫ s = U.ι := by simp [c, morphismRestrict_ι]
  have hcη : c (genericPoint U) = genericPoint Y' := genericPoint_eq_of_isOpenImmersion c
  have hη : s (genericPoint Y') = genericPoint Y := by
    rw [← hcη, ← Scheme.Hom.comp_apply, hc]
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have hne : ((s ⁻¹ᵁ U : Y'.Opens) : Set Y').Nonempty :=
    ⟨genericPoint Y', show s (genericPoint Y') ∈ U from hη ▸ GlobalTheory.Cartier.gen_mem hU.some_mem⟩
  have hdense : Dense ((s ⁻¹ᵁ U : Y'.Opens) : Set Y') := (s ⁻¹ᵁ U).isOpen.dense hne
  let M : Modif p U d := ⟨Y', s, hs', hp', hisoU, hdense⟩
  obtain ⟨g, hg1, hg2⟩ := hext Y' s hη (hC Y' s hη hEC)
  obtain ⟨r, hr'⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i g _ hdense fun x hx => by
    refine ⟨(s ∣_ U ≫ r₀) ⟨x, hx⟩, ?_⟩
    have e := congrArg (fun f : (s ⁻¹ᵁ U).toScheme ⟶ PSpace F N => f ⟨x, hx⟩) hg2
    exact e.symm
  refine ⟨M, r, hY', ?_, ?_⟩
  · show r ≫ t = s ≫ p
    rw [← hit, ← Category.assoc, hr', hg1]
  · show (s ⁻¹ᵁ U).ι ≫ r = (s ∣_ U) ≫ r₀
    rw [← cancel_mono i, Category.assoc, hr', hg2, Category.assoc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationExtendingMapFromOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modification_extending_map_from_open : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (Y T : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) (t : T ⟶ Sp F) (U : Y.Opens) (r₀ : U.toScheme ⟶ T), SmoothOfRelativeDimension d p → IsProjOver p → IsProjOver t → (U : Set Y).Nonempty → r₀ ≫ t = U.ι ≫ p → ∃ (M : Modif p U d) (r : M.X ⟶ T), IsIntegral M.X ∧ r ≫ t = M.str ∧ M.opn.ι ≫ r = (M.σ ∣_ U) ≫ r₀ := by
  first | exact @GlobalTheory.CompHS.exists_modif_map_of_open | exact GlobalTheory.CompHS.exists_modif_map_of_open | (intros; apply GlobalTheory.CompHS.exists_modif_map_of_open <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QuotSetup

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem surjective_of_isProjOver {F : Type} [Field F] {Y Z : Scheme.{0}} [IsIntegral Z] (p : Y ⟶ Sp F)
    (pZ : Z ⟶ Sp F) (f : Y ⟶ Z) (hf : f ≫ pZ = p) (hp : IsProjOver p) (hZ : IsProjOver pZ) (y : Y)
    (hy : f y = genericPoint Z) : Surjective f := by
  have h₁ : IsProper (f ≫ pZ) := hf ▸ ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have : IsProper pZ := ((isProjOver_iff_isProper_and_exists_isAmpleLB pZ).1 hZ).1
  have : IsProper f := IsProper.of_comp f pZ
  have hc : closure {genericPoint Z} ⊆ Set.range f :=
    f.isClosedMap.isClosed_range.closure_subset_iff.2 (by rintro _ rfl; exact ⟨y, hy⟩)
  exact ⟨fun z => hc (by rw [(genericPoint_spec Z).def]; trivial)⟩

end GlobalTheory.QuotSetup

namespace GlobalTheory.QuotSetup

theorem exists_resolved_modification : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → ∀ (δ : LB X) (hδ : δ.IsLB) (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → ∀ (J : Type) (v : J → (Sp ℂ ⟶ V)), (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (pW : W' ⟶ Sp F) (U : X.Opens) (M : Modif sX U n) (f : M.X ⟶ W') (NW : LB W') (hNW : NW.IsLB), IsIntegral M.X ∧ SmoothOfRelativeDimension n pW ∧ IsProjOver pW ∧ GeometricallyConnected pW ∧ f ≫ pW = M.str ∧ Surjective f ∧ (U : Set X).Nonempty ∧ CechPic.pull f (cls NW hNW) = CechPic.pull M.σ (cls δ hδ) ∧ ∃ z : J → (Sp ℂ ⟶ M.X), (∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn) ∧ (∀ j, z j ≫ M.σ = v j ≫ i) ∧ (∀ j j', z j ≫ f = z j' ≫ f) ∧ (∀ j s, (z j ≫ f) s = genericPoint W') := by
  intro hP F _ _ X X' W V _ _ _ sX n _ φ q sW i ℓ hsX hgc hφ hsW hqf hqs hw hi hℓ hℓi δ hδ N hN hNδ J v hv hgen
  obtain ⟨j₀, hj₀⟩ := hgen
  obtain ⟨o₀⟩ : Nonempty (Sp ℂ) := inferInstance
  haveI : Nonempty V := ⟨v j₀ o₀⟩
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion i
  haveI : Nonempty X := ⟨i (v j₀ o₀)⟩
  have hpX : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hsX).1
  have hpX' : IsProper (φ ≫ sX) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hφ).1
  have hpW : IsProper sW := ((isProjOver_iff_isProper_and_exists_isAmpleLB sW).1 hsW).1

  have hWgen : ∀ j o, (v j ≫ ℓ ≫ q) o = genericPoint W := fun j o => by
    rw [hv j j₀]
    have h₁ : v j₀ o = genericPoint V :=
      i.isOpenEmbedding.injective ((hj₀ o).trans (genericPoint_eq_of_isOpenImmersion i).symm)
    simp only [Scheme.Hom.comp_apply]
    rw [h₁, genericPoint_eq_of_isOpenImmersion ℓ, map_genericPoint q]

  have hdW : topologicalKrullDim W = n := by
    have hdX : topologicalKrullDim X = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance
    have hdV := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X V sX i
    have hdV' := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X' V (φ ≫ sX) ℓ
    have h₁ := PosBaseChange.dim_le_of_isClosedMap q.isClosedMap q.surjective
    have h₂ := PosBaseChange.dim_le_of_isDiscrete q.continuous q.isDiscrete_preimage_singleton
    rw [← hdX, ← hdV, hdV']
    exact le_antisymm h₁ h₂

  obtain ⟨W', s, UW, hW', hsm, hpj, hUW, hiso⟩ := GlobalTheory.T.weak_resolution_of_principalisation hP F W sW n hsW hdW
  haveI := hW'
  haveI := hiso
  have hηUW : genericPoint W ∈ UW := genericPoint_mem UW hUW

  let O : V.Opens := (ℓ ≫ q) ⁻¹ᵁ UW
  have hvO : ∀ j o, v j o ∈ O := fun j o => by
    show (ℓ ≫ q) (v j o) ∈ UW
    rw [← Scheme.Hom.comp_apply, hWgen j o]
    exact hηUW
  let U : X.Opens := i ''ᵁ O
  have hUi : Set.range U.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  let e : U.toScheme ⟶ V := IsOpenImmersion.lift i U.ι hUi
  have he : e ≫ i = U.ι := IsOpenImmersion.lift_fac _ _ _
  have hc : Set.range (e ≫ ℓ ≫ q) ⊆ Set.range UW.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : i (e x) ∈ U := by rw [← Scheme.Hom.comp_apply, he]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rw [i.isOpenEmbedding.injective hyx] at hy
    exact hy
  let c : U.toScheme ⟶ UW.toScheme := IsOpenImmersion.lift UW.ι (e ≫ ℓ ≫ q) hc
  have hcf : c ≫ UW.ι = e ≫ ℓ ≫ q := IsOpenImmersion.lift_fac _ _ _
  let b : UW.toScheme ⟶ W' := inv (s ∣_ UW) ≫ (s ⁻¹ᵁ UW).ι
  have hb : b ≫ s = UW.ι := by simp [b, ← morphismRestrict_ι]
  let r₀ : U.toScheme ⟶ pullback q s :=
    pullback.lift (e ≫ ℓ) (c ≫ b) (by rw [Category.assoc, Category.assoc, hb, hcf])
  have hUne : (U : Set X).Nonempty := ⟨i (v j₀ o₀), v j₀ o₀, hvO j₀ o₀, rfl⟩
  have ht : IsProjOver (pullback.snd q s ≫ s ≫ sW) := isProjOver_comp_of_isFinite _ hpj
  have hr₀ : r₀ ≫ pullback.snd q s ≫ s ≫ sW = U.ι ≫ sX := by
    simp only [r₀, pullback.lift_snd_assoc, Category.assoc]
    rw [reassoc_of% hb, reassoc_of% hcf, hw, reassoc_of% hℓi, reassoc_of% he]
  obtain ⟨M, r, hMi, hrt, hrM⟩ :=
    GlobalTheory.T.exists_modification_extending_map_from_open hP F X (pullback q s) sX n (pullback.snd q s ≫ s ≫ sW) U r₀ inferInstance hsX ht hUne hr₀
  haveI := hMi
  have hsep : IsSeparated sX := inferInstance
  haveI : IsDominant M.opn.ι := ⟨show Dense (Set.range M.opn.ι) by rw [Scheme.Opens.range_ι]; exact M.dense⟩
  have hσ : r ≫ pullback.fst q s ≫ φ = M.σ := by
    refine ext_of_isDominant_of_isSeparated sX ?_ M.opn.ι ?_
    · simp only [Category.assoc]
      rw [← hw, pullback.condition_assoc]
      exact hrt
    · rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_fst_assoc, Category.assoc]
      rw [hℓi, he, morphismRestrict_ι]
  let f : M.X ⟶ W' := r ≫ pullback.snd q s
  have hfs : f ≫ s = (r ≫ pullback.fst q s) ≫ q := by
    simp only [f, Category.assoc, pullback.condition]
  have hfp : f ≫ s ≫ sW = M.str := by
    simp only [f, Category.assoc]; exact hrt

  have hvU : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ U := fun j o _ => by
    show (v j ≫ i) o ∈ U
    rw [Scheme.Hom.comp_apply]
    exact ⟨v j o, hvO j o, rfl⟩
  choose z hz using fun j => (M.existsUnique_lift (v j ≫ i) (hvU j)).exists
  have hzU : ∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn := fun j => by
    show ⊤ ≤ z j ⁻¹ᵁ (M.σ ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, hz j]
    exact hvU j
  have key : ∀ j, ∃ d : Sp ℂ ⟶ UW.toScheme, d ≫ UW.ι = v j ≫ ℓ ≫ q ∧ z j ≫ f = d ≫ b := fun j => by
    have hr : Set.range (z j) ⊆ Set.range M.opn.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨o, rfl⟩
      exact hzU j (Set.mem_univ o)
    let w := IsOpenImmersion.lift M.opn.ι (z j) hr
    have hw' : w ≫ M.opn.ι = z j := IsOpenImmersion.lift_fac _ _ _
    have hwe : w ≫ (M.σ ∣_ U) ≫ e = v j := by
      rw [← cancel_mono i, Category.assoc, Category.assoc, he, morphismRestrict_ι, reassoc_of% hw', hz j]
    refine ⟨w ≫ (M.σ ∣_ U) ≫ c, ?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hcf, ← reassoc_of% hwe]
    · simp only [f, ← hw', Category.assoc]
      rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_snd, Category.assoc]
  choose d hd hzd using key
  haveI : Nonempty UW.toScheme := ⟨⟨_, hηUW⟩⟩
  haveI : IsIntegral UW.toScheme := isIntegral_of_isOpenImmersion UW.ι
  have hgen' : ∀ j o, (z j ≫ f) o = genericPoint W' := fun j o => by
    have h₁ : d j o = genericPoint UW.toScheme := by
      apply UW.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hd j, hWgen j o, genericPoint_eq_of_isOpenImmersion UW.ι]
    rw [hzd j, Scheme.Hom.comp_apply, h₁]
    exact genericPoint_eq_of_isOpenImmersion b
  have hfsurj : Surjective f :=
    surjective_of_isProjOver M.str (s ≫ sW) f hfp M.proj hpj (z j₀ o₀) (by rw [← Scheme.Hom.comp_apply]; exact hgen' j₀ o₀)
  have hgcM : GeometricallyConnected M.str := GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen F X sX n U M hUne
  have hgcW : GeometricallyConnected (s ≫ sW) := by
    rw [← hfp] at hgcM
    exact geometricallyConnected_of_surjective f (s ≫ sW)
  refine ⟨W', hW', s ≫ sW, U, M, f, N.pull s, LB.isLB_pull hN s, hMi, hsm, hpj, hgcW, hfp, hfsurj, hUne, ?_,
    z, hzU, hz, fun j j' => ?_, hgen'⟩
  · rw [cls_pull hN s, ← pull_comp, hfs, pull_comp, hNδ, ← pull_comp, Category.assoc, hσ]
  · rw [hzd j, hzd j']
    congr 1
    rw [← cancel_mono UW.ι, hd j, hd j', hv j j']

end GlobalTheory.QuotSetup

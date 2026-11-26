module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyMovingPartsChainBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalModelRegularUnitValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalModelRegularUnitValues
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem model_regAt_unitAt_values : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → (∀ (y : Y) (f : X.functionField), RegAt (π y) f → RegAt y (φ f)) ∧ (∀ (y : Y) (f : X.functionField), UnitAt (π y) f → UnitAt y (φ f)) ∧ (∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)), φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a)) ∧ ∀ (σ : k →+* ℂ) (z : CxPts q σ) (f : X.functionField), RegAt (π (under z)) f → ratVal (φ f) z = ratVal f (GlobalTheory.Points.PtsOver.map π hπ _ z) := by
  intro k _ X Y _ _ p q π hπ φ hM
  have h3 : ∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)),
      φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a) := by
    intro U h h' a
    have e1 := algebraMap_germ (X := X) (show π (genericPoint Y) ∈ U from h') a
    have e2 := algebraMap_germ (X := Y) h' (π.app U a)
    rw [← e1, hM.compat, ← e2]
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply π U (genericPoint Y) h' a
  refine ⟨?_, ?_, h3, ?_⟩
  · rintro y f ⟨a, rfl⟩
    exact ⟨π.stalkMap y a, (hM.compat y a).symm⟩
  · rintro y f ⟨a, ha, rfl⟩
    exact ⟨π.stalkMap y a, ha.map _, (hM.compat y a).symm⟩
  · intro σ z f hf
    obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
    have hz : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := mem_ptsIn.2 hU
    have hz' : GlobalTheory.Points.PtsOver.map π hπ _ z ∈ ptsIn p σ U := mem_ptsIn.2 (by first | exact hU | simpa [Function.comp_apply] using hU)
    rw [h3 U _ (gen_mem (show under z ∈ π ⁻¹ᵁ U from hU)) a, ratVal_fnOf hz, ratVal_fnOf hz',
      ev_app π hπ]

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalModelRegularUnitValuesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birationalModel_regular_unit_values : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → (∀ (y : Y) (f : X.functionField), RegAt (π y) f → RegAt y (φ f)) ∧ (∀ (y : Y) (f : X.functionField), UnitAt (π y) f → UnitAt y (φ f)) ∧ (∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)), φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a)) ∧ ∀ (σ : k →+* ℂ) (z : CxPts q σ) (f : X.functionField), RegAt (π (under z)) f → ratVal (φ f) z = ratVal f (GlobalTheory.Points.PtsOver.map π hπ _ z) := by
  first | exact @GlobalTheory.HSNef.model_regAt_unitAt_values | exact GlobalTheory.HSNef.model_regAt_unitAt_values | (intros; apply GlobalTheory.HSNef.model_regAt_unitAt_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirationalModelTotallyOrderedFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupModelRegularFunctionOrInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelOfIsIsoOverNonemptyOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelOfIsIsoOverNonemptyOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens),
    (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  intro X Y _ _ π U hU hiso
  obtain ⟨h₁, h₂⟩ := GlobalTheory.Published.generic_of_isIso_restrict π U hU
  have e : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  have hd : IsDominant π := ⟨dense_iff_closure_eq.mpr
    (Set.eq_univ_of_univ_subset (e ▸ closure_mono (Set.singleton_subset_iff.mpr ⟨_, h₁⟩)))⟩
  exact ⟨functionFieldMap π, h₁, h₂, fun y a => functionFieldMap_algebraMap π y a⟩

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelOfIsIsoOverNonemptyOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBirationalModel_of_isIso_over_nonempty_open : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens), (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  first | exact @GlobalTheory.HSNef.isModel_of_isIso_restrict | exact GlobalTheory.HSNef.isModel_of_isIso_restrict | (intros; apply GlobalTheory.HSNef.isModel_of_isIso_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupModelRegularFunctionOrInverse
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.RegOrInvModel

theorem exists_idealSheaf_principalises_of_ne_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)), (∀ j, IsAffineOpen (U j)) → (∀ j, ∃ k, A j k ≠ 0) → ∃ J : X.IdealSheafData, genericPoint X ∉ J.support ∧ ∀ (W : Scheme.{0}) (b : W ⟶ X), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) → ∀ (w : W) (j : Fin n), b w ∈ U j → ∃ (V : W.Opens) (hV : V ≤ b ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', (b.appLE (U j) V hV).hom (A j k) ∣ (b.appLE (U j) V hV).hom (A j k') := by
  intro X _ _ n U m A hU hA
  choose J hJU hJp using fun j => GlobalTheory.Principalise.kerIdealAffine X (U j) (hU j) (Ideal.span (Set.range (A j)))
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hηV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hsupp : ∀ I : X.IdealSheafData, genericPoint X ∉ I.support ↔
      ∃ f ∈ I.ideal ⟨V₀, hV₀⟩, genericPoint X ∈ X.basicOpen f := by
    intro I
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V₀, hV₀⟩) hηV₀, Scheme.mem_zeroLocus_iff]
    push_neg
    rfl
  have hmul : ∀ I I' : X.IdealSheafData, genericPoint X ∉ I.support → genericPoint X ∉ I'.support →
      genericPoint X ∉ (I * I').support := by
    intro I I' h h'
    obtain ⟨f, hf, hηf⟩ := (hsupp I).1 h
    obtain ⟨f', hf', hηf'⟩ := (hsupp I').1 h'
    refine (hsupp _).2 ⟨f * f', ?_, ?_⟩
    · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
      exact Ideal.mul_mem_mul hf hf'
    · rw [Scheme.basicOpen_mul]
      exact ⟨hηf, hηf'⟩
  have hone : genericPoint X ∉ (1 : X.IdealSheafData).support := by
    refine (hsupp _).2 ⟨1, ?_, ?_⟩
    · show (1 : Γ(X, V₀)) ∈ (⊤ : X.IdealSheafData).ideal ⟨V₀, hV₀⟩
      rw [Scheme.IdealSheafData.ideal_top]
      exact Submodule.mem_top
    · rw [Scheme.basicOpen_one]
      exact hηV₀
  have hJj : ∀ j, genericPoint X ∉ (J j).support := by
    intro j
    obtain ⟨k, hk⟩ := hA j
    have hb : X.basicOpen (A j k) ≠ ⊥ := fun h0 => hk ((basicOpen_eq_bot_iff _).1 h0)
    obtain ⟨x, hx⟩ : ∃ x, x ∈ X.basicOpen (A j k) := by
      by_contra hc
      push_neg at hc
      exact hb (eq_bot_iff.2 fun x hx => (hc x hx).elim)
    have hηb : genericPoint X ∈ X.basicOpen (A j k) := gen_mem hx
    have hηU : genericPoint X ∈ U j := X.basicOpen_le _ hηb
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U j, hU j⟩) hηU, Scheme.mem_zeroLocus_iff, hJU j]
    exact fun h => h _ (Ideal.subset_span ⟨k, rfl⟩) hηb
  refine ⟨∏ j, J j, ?_, ?_⟩
  · exact Finset.prod_induction J (fun I => genericPoint X ∉ I.support) hmul hone fun j _ => hJj j
  · intro W b hE w j hw
    obtain ⟨V₁, f, hw₁, hf, hV₁⟩ := hE w
    obtain ⟨g, hgle, hwg⟩ := V₁.2.exists_basicOpen_le (V := V₁.1 ⊓ b ⁻¹ᵁ U j) ⟨w, hw₁, hw⟩ hw₁
    have hDU : (W.affineBasicOpen g).1 ≤ b ⁻¹ᵁ U j := hgle.trans inf_le_right
    have hDV : (W.affineBasicOpen g).1 ≤ V₁.1 := W.basicOpen_le g
    have hfD : (W.presheaf.map (homOfLE hDV).op).hom f ∈ nonZeroDivisors Γ(W, (W.affineBasicOpen g).1) :=
      (GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen (W.affineBasicOpen g).2).1
        (((GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen V₁.2).2 hf).resG hDV)
    have hI1 := ((∏ i, J i).comap b).map_ideal_basicOpen V₁ g
    rw [hV₁, Ideal.map_span, Set.image_singleton] at hI1
    have hI2 := GlobalTheory.Principalise.comapIdealAffine (∏ i, J i) b ⟨U j, hU j⟩ (W.affineBasicOpen g) hDU
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j), Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, Ideal.map_mul, hJU, Ideal.map_span, ← Set.range_comp] at hI2
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j)] at hI1
    have hwD : w ∈ (W.affineBasicOpen g).1 := hwg
    obtain ⟨k, s, hsP, hdiv⟩ := GlobalTheory.Principalise.exists_dvd_of_span_mul_eq
      (Ideal.comap (W.presheaf.germ (W.affineBasicOpen g).1 w hwD).hom (IsLocalRing.maximalIdeal _)) _ _
      (hI2.symm.trans hI1.symm) hfD
    have hsu : w ∈ W.basicOpen s := by
      rw [Scheme.mem_basicOpen _ _ _ hwD]
      by_contra hc
      exact hsP ((IsLocalRing.mem_maximalIdeal _).2 hc)
    have hED : W.basicOpen s ≤ (W.affineBasicOpen g).1 := W.basicOpen_le s
    have hV : W.basicOpen s ≤ b ⁻¹ᵁ U j := fun x hx => hDU (hED hx)
    refine ⟨W.basicOpen s, hV, hsu, (W.affineBasicOpen g).2.basicOpen s, k, fun k' => ?_⟩
    have key : b.appLE (U j) _ hDU ≫ W.presheaf.map (homOfLE hED).op = b.appLE (U j) (W.basicOpen s) hV :=
      Scheme.Hom.appLE_map _ _ _
    have hu := W.toRingedSpace.isUnit_res_basicOpen s
    have h1 := map_dvd (W.presheaf.map (homOfLE hED).op).hom (hdiv k')
    rw [map_mul] at h1
    have h2 := hu.dvd_mul_left.1 h1
    rw [← key]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact h2

theorem exists_model_regAt_or_regAt_inv : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ g : X.functionField, g ≠ 0 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ y : Y, RegAt y (φ g) ∨ RegAt y (φ g)⁻¹ := by
  intro k _ X _ p D hX g hg
  have := hX.isLocallyNoetherian
  have := hX.isNoetherian
  choose V hVa hxV using fun x : X => (by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hx⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let e := t.equivFin
  let U : Fin t.card → X.Opens := fun j => V (e.symm j).1
  have hU : ∀ j, IsAffineOpen (U j) := fun j => hVa _
  have hη : ∀ j, genericPoint X ∈ U j := fun j => gen_mem (hxV (e.symm j).1)
  have hfr : ∀ j, ∃ a b : Γ(X, U j), b ≠ 0 ∧ fnOf (U j) (hη j) a / fnOf (U j) (hη j) b = g := by
    intro j
    have : Nonempty (U j) := ⟨⟨_, hη j⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X (U j) (hU j)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U j)) g
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, hab⟩
  choose a b hb hab using hfr
  let A : ∀ j, Fin 2 → Γ(X, U j) := fun j => ![a j, b j]
  obtain ⟨J, hJη, hJdiv⟩ := exists_idealSheaf_principalises_of_ne_zero X t.card U (fun _ => 2) A hU fun j => ⟨1, hb j⟩
  obtain ⟨Y, ρ, hY, hE, hiso⟩ := GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso k X p D hX J hJη
  have : IsIntegral Y := hY.isIntegral
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isBirationalModel_of_isIso_over_nonempty_open X Y ρ J.support.compl ⟨genericPoint X, hJη⟩ (hiso _ fun _ hx => hx)
  obtain ⟨-, -, hfn, -⟩ := GlobalTheory.T.birationalModel_regular_unit_values k X Y p (ρ ≫ p) ρ rfl φ hφ
  refine ⟨Y, inferInstance, ρ, φ, hY, hφ, fun y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, ρ y ∈ V x := by
    simpa using ht (Set.mem_univ (ρ y))
  set j := e ⟨x, hxt⟩ with hj
  have hyj : ρ y ∈ U j := by simpa [U, j] using hyx
  obtain ⟨W, hW, hyW, -, kk, hdiv⟩ := hJdiv Y ρ hE y j hyj
  have hWη : genericPoint Y ∈ W := gen_mem hyW
  have key : ∀ c : Γ(X, U j), fnOf W hWη ((ρ.appLE (U j) W hW).hom c) = φ (fnOf (U j) (hη j) c) := by
    intro c
    rw [hfn (U j) (hη j) (hW hWη) c]
    exact fnOf_resG hW hWη ((ρ.app (U j)).hom c)
  have hbne : φ (fnOf (U j) (hη j) (b j)) ≠ 0 := by
    rw [map_ne_zero]
    exact fun h0 => hb j (fnOf_injective _ _ (h0.trans (map_zero _).symm))
  have hane : φ (fnOf (U j) (hη j) (a j)) ≠ 0 := by
    rw [map_ne_zero]
    intro h0
    apply hg
    rw [← hab j, h0, zero_div]
  have hφg : φ g = φ (fnOf (U j) (hη j) (a j)) / φ (fnOf (U j) (hη j) (b j)) := by
    rw [← hab j, map_div₀]
  fin_cases kk
  · right
    obtain ⟨c, hc⟩ := hdiv 1
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : (φ g)⁻¹ = fnOf W hWη c := by
      rw [hφg, inv_div, div_eq_iff hane]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c
  · left
    obtain ⟨c, hc⟩ := hdiv 0
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : φ g = fnOf W hWη c := by
      rw [hφg, div_eq_iff hbne]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c

end GlobalTheory.RegOrInvModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupModelRegularFunctionOrInverseStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blowup_model_regular_function_or_inverse : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ g : X.functionField, g ≠ 0 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ y : Y, RegAt y (φ g) ∨ RegAt y (φ g)⁻¹ := by
  first | exact @GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv | exact GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv | (intros; apply GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelIdAndComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelIdAndComp
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_id (X : Scheme.{0}) [IsIntegral X] : IsModel (𝟙 X) (RingHom.id X.functionField) := by
  refine { gen := rfl, deg := Scheme.Hom.residueDegree_id _, compat := ?_ }
  intro y a
  simp only [RingHom.id_apply, Scheme.Hom.stalkMap_id]
  rfl

theorem IsModel.comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] {π : Y ⟶ X} {π' : Z ⟶ Y}
    {φ : X.functionField →+* Y.functionField} {φ' : Y.functionField →+* Z.functionField}
    (h : IsModel π φ) (h' : IsModel π' φ') : IsModel (π' ≫ π) (φ'.comp φ) := by
  refine { gen := ?_, deg := ?_, compat := ?_ }
  · show π (π' (genericPoint Z)) = genericPoint X
    rw [h'.gen, h.gen]
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp π' π (genericPoint Z), h'.deg]
    rw [h'.gen, h.deg]
  · intro z a
    refine (congrArg φ' (h.compat (π' z) a)).trans ((h'.compat z _).trans ?_)
    rw [Scheme.Hom.stalkMap_comp]
    rfl

theorem isModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y)
    (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField),
    IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) :=
  fun X _ _ _ _ _ _ _ _ _ => ⟨isModel_id X, fun h h' => h.comp h'⟩

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelIdAndCompStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBirationalModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y) (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField), IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) := by
  first | exact @GlobalTheory.HSNef.isModel_id_and_comp | exact GlobalTheory.HSNef.isModel_id_and_comp | (intros; apply GlobalTheory.HSNef.isModel_id_and_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirationalModelTotallyOrderedFamily
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_model_list (k : Type) [CommRing k] (D : ℕ) (L : ℕ) :
    ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsArithVar p D →
    ∀ (g : List X.functionField), g.length = L → (∀ h ∈ g, h ≠ 0) →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField),
      IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ h ∈ g, ∀ y : Y, RegAt y (φ h) ∨ RegAt y (φ h)⁻¹ := by
  induction L with
  | zero =>
    intro X _ p hp g hg _
    obtain rfl := List.length_eq_zero_iff.1 hg
    refine ⟨X, inferInstance, 𝟙 X, RingHom.id _, by simpa using hp, (GlobalTheory.T.isBirationalModel_id_and_comp X X X (𝟙 X) (𝟙 X)
      (RingHom.id _) (RingHom.id _)).1, by simp⟩
  | succ n ih =>
    intro X _ p hp g hg hne
    obtain ⟨a, g', rfl⟩ : ∃ a g', g = a :: g' := by
      cases g with
      | nil => simp at hg
      | cons a g' => exact ⟨a, g', rfl⟩
    obtain ⟨Y₁, hY₁, π₁, φ₁, hA₁, hM₁, hR₁⟩ :=
      ih X p hp g' (by simpa using hg) (fun h hh => hne h (List.mem_cons_of_mem _ hh))
    have ha : φ₁ a ≠ 0 := (map_ne_zero φ₁).2 (hne a List.mem_cons_self)
    obtain ⟨Y₂, hY₂, π₂, φ₂, hA₂, hM₂, hR₂⟩ := GlobalTheory.T.exists_blowup_model_regular_function_or_inverse k Y₁ (π₁ ≫ p) D hA₁ (φ₁ a) ha
    refine ⟨Y₂, hY₂, π₂ ≫ π₁, φ₂.comp φ₁, by simpa [Category.assoc] using hA₂,
      (GlobalTheory.T.isBirationalModel_id_and_comp X Y₁ Y₂ π₁ π₂ φ₁ φ₂).2 hM₁ hM₂, ?_⟩
    have hreg := (GlobalTheory.T.birationalModel_regular_unit_values k Y₁ Y₂ (π₁ ≫ p) (π₂ ≫ π₁ ≫ p) π₂ rfl φ₂ hM₂).1
    intro h hh y
    rcases List.mem_cons.1 hh with rfl | hh
    · simpa using hR₂ y
    · rcases hR₁ h hh (π₂ y) with h1 | h1
      · exact Or.inl (by simpa using hreg y _ h1)
      · exact Or.inr (by simpa [map_inv₀] using hreg y _ h1)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_model_total : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (J : Type) [Finite J] (f : J → X.functionField), (∀ j, f j ≠ 0) → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ Total (fun j => φ (f j)) := by
  intro k _ X _ p D hp J _ f hf
  have := Fintype.ofFinite J
  let g : List X.functionField := (Finset.univ : Finset (J × J)).toList.map (fun q => f q.1 / f q.2)
  have hg : ∀ j l, f j / f l ∈ g := fun j l => by
    simp only [g, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨(j, l), rfl⟩
  obtain ⟨Y, hY, π, φ, hA, hM, hR⟩ := exists_model_list k D g.length X p hp g rfl (by
    intro h hh
    simp only [g, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hh
    obtain ⟨q, rfl⟩ := hh
    exact div_ne_zero (hf q.1) (hf q.2))
  refine ⟨Y, hY, π, φ, hA, hM, fun j => (map_ne_zero φ).2 (hf j), fun y j l => ?_⟩
  rcases hR _ (hg j l) y with h | h
  · exact Or.inl (by simpa [map_div₀] using h)
  · exact Or.inr (by simpa [map_div₀, inv_div] using h)

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirationalModelTotallyOrderedFamilyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birationalModel_totallyOrdered_family : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (J : Type) [Finite J] (f : J → X.functionField), (∀ j, f j ≠ 0) → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ Total (fun j => φ (f j)) := by
  first | exact @GlobalTheory.HSNef.exists_model_total | exact GlobalTheory.HSNef.exists_model_total | (intros; apply GlobalTheory.HSNef.exists_model_total <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLeShiftOfSmallSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLeShiftOfSmallSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.FsTop

variable {X : Scheme.{0}} [IsIntegral X]

theorem regAt_mul' {x : X} {a b : X.functionField} (ha : RegAt x a) (hb : RegAt x b) : RegAt x (a * b) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  exact ⟨u * v, map_mul _ u v⟩

theorem regAt_inv_of_unitAt {x : X} {a : X.functionField} (ha : UnitAt x a) : RegAt x a⁻¹ := by
  obtain ⟨u, hu, rfl⟩ := ha
  refine ⟨(hu.unit⁻¹ : (X.presheaf.stalk x)ˣ), ?_⟩
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← map_mul]
  simp

end GlobalTheory.HSNef.FsTop


open GlobalTheory.HSNef.FsTop in
theorem GlobalTheory.HSNef.le_shift_of_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M B : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → SmallFam B f w → Le M (B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl) := by
  intro k _ X _ p M B J _ f w hM hB
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨β, hβ, hbreg, hbnorm⟩ := hB
  have key : ∀ (x : X) (c : B.B.ι) (d : M.B.ι), x ∈ B.B.U c → x ∈ M.B.U d →
      RegAt x ((β c : X.functionField) / (ρ d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨l, hl⟩ := (hreg x d hd).2
    have hfl : f l ≠ 0 := fun h => hl.ne_zero (by rw [h, zero_mul])
    have e : (β c : X.functionField) / (ρ d) = (f l * β c) * (f l * ρ d)⁻¹ := by
      field_simp
    rw [e]
    exact regAt_mul' (hbreg x c hc l) (regAt_inv_of_unitAt hl)
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p _ M).2 ⟨β, ρ, hβ, hρ, fun x i j hi hj => key x i j hi hj, ?_⟩
  intro σ y i j hi hj
  have hxi : under y ∈ B.B.U i := mem_ptsIn.1 hi
  have hxj : under y ∈ M.B.U j := mem_ptsIn.1 hj
  have hq := key _ i j hxi hxj
  obtain ⟨l₀, hl₀⟩ := (hreg _ j hxj).2
  set q : X.functionField := (β i : X.functionField) / (ρ j : X.functionField) with hqdef
  have hval : ∀ l, ratVal (f l * (β i : X.functionField)) y = ratVal q y * ratVal (f l * (ρ j : X.functionField)) y := by
    intro l
    have e : f l * (β i : X.functionField) = q * (f l * (ρ j : X.functionField)) := by
      rw [hqdef]; field_simp
    rw [e, ratVal_mul hq ((hreg _ j hxj).1 l)]
  have hφj : (M.φ σ).φ j y = Real.log (∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) :=
    hφ σ y j hj
  have hφi : ((B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl).φ σ).φ i y =
      (B.φ σ).φ i y + 2 * (Real.log (Fintype.card J) / 2) := rfl
  set S := ∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l) with hS
  set φB := (B.φ σ).φ i y
  set Q := ‖ratVal q y‖
  have hn : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨l₀⟩
  have hSpos : 0 < S := by
    have h0 : 0 < ‖ratVal (f l₀ * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l₀) :=
      mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hl₀)) 2) (Real.exp_pos _)
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun l => ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
      (fun l _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Finset.mem_univ l₀))

  have hterm : ∀ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) ≤ Real.exp φB := by
    intro l
    have h1 := hbnorm σ y i hi l
    rw [hval l, norm_mul] at h1
    have h2 : Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖ ≤ Real.exp (-w l) * Real.exp (φB / 2) := by
      have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (φB / 2)).le
      rwa [mul_assoc, ← Real.exp_add, show -φB / 2 + φB / 2 = 0 by ring, Real.exp_zero, mul_one] at this
    have h3 := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h2 2
    have e1 : (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) = Real.exp φB := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; push_cast; ring
    calc Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        = (Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖) ^ 2 * Real.exp (2 * w l) := by ring
      _ ≤ (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp φB := e1
  have hsum : Q ^ 2 * S ≤ Fintype.card J * Real.exp φB := by
    rw [hS, Finset.mul_sum]
    calc ∑ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        ≤ ∑ _l : J, Real.exp φB := Finset.sum_le_sum fun l _ => hterm l
      _ = Fintype.card J * Real.exp φB := by simp
  rw [hφi, hφj]
  have hE : Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) ^ 2 =
      S / (Fintype.card J * Real.exp φB) := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2)
        = Real.log S - (Real.log (Fintype.card J) + φB) by push_cast; ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hSpos, Real.exp_log (by linarith)]
  have hpos : 0 ≤ Q * Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine (pow_le_one_iff_of_nonneg hpos two_ne_zero).1 ?_
  rw [mul_pow, hE, ← mul_div_assoc, div_le_one (by positivity)]
  exact hsum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLeShiftOfSmallSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_le_shift_of_smallSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M B : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → SmallFam B f w → Le M (B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl) := by
  first | exact @GlobalTheory.HSNef.le_shift_of_isFS | exact GlobalTheory.HSNef.le_shift_of_isFS | (intros; apply GlobalTheory.HSNef.le_shift_of_isFS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFnFamilySmallPullbackBirationalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFnFamilySmallPullbackBirationalModel
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem smallFam_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  intro k _ X Y _ _ p q π hπ φ hM B J f w hs
  obtain ⟨β, hβ, hreg, hnorm⟩ := hs
  obtain ⟨hR, -, hF, hV⟩ := GlobalTheory.T.birationalModel_regular_unit_values k X Y p q π hπ φ hM
  refine ⟨fun c => Units.map φ.toMonoidHom (β (c PUnit.unit)), ?_, ?_, ?_⟩
  · intro i j h
    have hi : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (i PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit h.1
    have hj : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (j PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit h.2
    have hX : genericPoint X ∈ B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit) := by
      rw [← hM.gen]; exact ⟨hi, hj⟩
    have eg : ((B.B.pull π).g i j).val = resG Y (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit)))
        (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val) := by
      dsimp only [LB.pull, LB.LinComb]
      simp only [Fintype.prod_unique, zpow_one, LB.val_res, pullU, Units.coe_map]
      rfl
    show φ (β (i PUnit.unit)) = fnOf _ h ((B.B.pull π).g i j).val * φ (β (j PUnit.unit))
    rw [hβ (i PUnit.unit) (j PUnit.unit) hX, map_mul, hF _ hX ⟨hi, hj⟩, eg]
    exact congrArg (· * φ (β (j PUnit.unit))) (fnOf_resG (X := Y) (U := π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) h (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val)).symm
  · intro y c hy j
    show RegAt y (φ (f j) * φ (β (c PUnit.unit)))
    rw [← map_mul]
    exact hR y _ (hreg (π y) (c PUnit.unit) (LB.wchart_le B.B (fun _ : PUnit => π) c PUnit.unit hy) j)
  · intro σ z c hz j
    have hm := mem_of_mem_linComb (m := fun _ => GlobalTheory.Points.PtsOver.map π hπ _ z) (fun _ => rfl) hz
      PUnit.unit
    have hr := hreg (π (under z)) (c PUnit.unit) (mem_ptsIn.1 hm) j
    have e2 : ((B.φ σ).pull π hπ).φ c z = (B.φ σ).φ (c PUnit.unit) (GlobalTheory.Points.PtsOver.map π hπ _ z) :=
      (B.φ σ).pull_φ π hπ c z
    show ‖ratVal (φ (f j) * φ (β (c PUnit.unit))) z‖ * Real.exp (-((B.φ σ).pull π hπ).φ c z / 2) ≤ _
    rw [← map_mul, hV σ z _ hr, e2]
    exact hnorm σ _ (c PUnit.unit) hm j

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFnFamilySmallPullbackBirationalModelStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  first | exact @GlobalTheory.HSNef.smallFam_pull | exact GlobalTheory.HSNef.smallFam_pull | (intros; apply GlobalTheory.HSNef.smallFam_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePullBirationalModel
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem isometric_pull_shiftC {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (L : HermLB p) (t : ℝ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.shift (fun _ => t) fun _ => rfl).pull π hπ).Isometric ((L.pull π hπ).shift (fun _ => t) fun _ => rfl) :=
  HermLB.isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t) π hπ a y).symm

theorem gdeg_pull_model : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q)
    (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧
    ∀ (a t : ℝ), L.IsSelfInter a →
      ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  intro hC k _ X Y _ _ p q D hX hY π hπ φ hM L
  have hdeg : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hM.deg]; exact one_ne_zero
  have hP := ((hC.arProj k X Y p q D hX hY π hπ hM.gen hdeg).1)
  have hP1 : ∀ (M : HermLB p) (a : ℝ), M.IsSelfInter a → (M.pull π hπ).IsSelfInter a := fun M a h => by
    have := hP M a h
    rwa [hM.deg, Nat.cast_one, one_mul] at this
  have hS := hC.arShift
  have hg : gdeg (L.pull π hπ) D = gdeg L D := by
    obtain ⟨h, hh⟩ := ((hC.arExists k X p D hX).1 L)
    have ha : L.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    set a := h (genericPoint X)

    have h1 := hP1 _ _ (hS k X p D hX L a 1 ha)
    have h1' := (isometric_pull_shiftC L 1 π hπ).isSelfInter hY h1
    have h2 := hS k Y q D hY (L.pull π hπ) a 1 (hP1 L a ha)
    have e := HermLB.IsSelfInter.unique hY h1' h2
    have hD : ((D : ℝ) + 1) ≠ 0 := by positivity
    have : ((D : ℝ) + 1) * gdeg L D = ((D : ℝ) + 1) * gdeg (L.pull π hπ) D := by linarith
    exact (mul_left_cancel₀ hD this).symm
  refine ⟨hg, fun a t ha => ?_⟩
  have := hS k Y q D hY (L.pull π hπ) a t (hP1 L a ha)
  rwa [hg] at this

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianSmallSectionsKeyInequality
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNefCore

theorem key_ineq : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  intro hA hAmp hSP k _ X _ p D hX B β hB hβ x Δ hx hΔ J _ _ e n he hsm

  have hne : ∀ c, boxFam e x c ≠ 0 := by
    intro c
    simp only [boxFam]
    refine mul_ne_zero (he.ne_zero c.1) ?_
    exact Finset.prod_ne_zero_iff.2 fun i _ => hx.ne_zero i
  obtain ⟨Y, hY, π, φ, hvarY, hmod, htot⟩ := GlobalTheory.T.exists_birationalModel_totallyOrdered_family k X p D hX (J × Finset (Fin D)) (boxFam e x) hne
  haveI := hY
  set q := π ≫ p with hq
  set f : J × Finset (Fin D) → Y.functionField := fun c => φ (boxFam e x c) with hf
  have hbox : f = boxFam (φ ∘ e) (φ ∘ x) := by
    funext c
    simp [hf, boxFam, map_mul, map_prod]
  have hx' : AlgebraicIndependent ℤ (φ ∘ x) := hx.map' (f := φ.toIntAlgHom) φ.injective
  have he' : LinearIndependent ℤ (φ ∘ e) :=
    he.map' φ.toIntAlgHom.toLinearMap (LinearMap.ker_eq_bot.2 φ.injective)
  set w : J × Finset (Fin D) → ℝ := fun c => n c.1 * Δ with hw
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k Y q (J × Finset (Fin D)) f w htot
  obtain ⟨μ, hμ⟩ : ∃ μ, M.IsSelfInter μ := by
    obtain ⟨Φ, hΦ⟩ := ((hA.arExists k Y q D hvarY).2 PUnit fun _ => M).1
    exact ⟨_, ((hA.arIso k Y q D hvarY).2 PUnit _ Φ hΦ).1 PUnit.unit⟩

  have hN : ∀ j, n j ≤ ∑ i, n i := fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hchain := GlobalTheory.HSNef.chain_moving_parts hA hAmp hSP k Y q D hvarY (φ ∘ x) Δ hx' hΔ (∑ i, n i) J (φ ∘ e) n M μ he' hN
    (hbox ▸ htot) (hbox ▸ hM) hμ

  set s : ℝ := Real.log (Fintype.card (J × Finset (Fin D))) / 2 with hs
  set B' := B.pull π rfl with hB'
  have hsmall : SmallFam B' f w := GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel k X Y p q π rfl φ hmod B _ (boxFam e x) w hsm
  have hle : Le M (B'.shift (fun _ => s) fun _ => rfl) := GlobalTheory.T.fubiniStudy_le_shift_of_smallSections k Y q M B' _ f w hM hsmall
  have hle' := (GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift k Y q (B'.shift (fun _ => s) fun _ => rfl) M M).2.2.2 Δ hle

  have hs0 : 0 ≤ s := by
    rw [hs]
    have : (1 : ℝ) ≤ Fintype.card (J × Finset (Fin D)) := by exact_mod_cast Fintype.card_pos
    have := Real.log_nonneg this
    linarith
  have hMnef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hA k Y q D hvarY M _ f w hM fun c => by
    simp only [hw]; exact mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have hB'nef : B'.IsNef D := GlobalTheory.T.hermitianLineBundle_isNef_pullback hA hSP k X Y p q D D hX hvarY π rfl B hB
  have hA1 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY B' s hs0 hB'nef
  have hA2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY _ Δ hΔ.le hA1
  have hM2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY M Δ hΔ.le hMnef

  obtain ⟨hg, hgs⟩ := GlobalTheory.HSNef.gdeg_pull_model hA k X Y p q D hX hvarY π rfl φ hmod B
  have h1 := hgs β s hβ
  have h2 := hA.arShift k Y q D hvarY _ _ Δ h1
  have h3 := hA.arShift k Y q D hvarY M μ Δ hμ
  have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hA hAmp hSP k Y q D hvarY _ _ _ _ hA2 hM2 hle' h2 h3
  rw [GlobalTheory.CovTest.GeoSwap.gdeg_shift_const, hg] at hmono

  have hcard : s = Real.log (Fintype.card J) / 2 + D * Real.log 2 / 2 := by
    rw [hs, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
    push_cast
    rw [Real.log_mul (by exact_mod_cast Fintype.card_ne_zero) (by positivity), Real.log_pow]
    ring
  rw [hcard] at hmono
  nlinarith [hchain, hmono]

end GlobalTheory.HSNefCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianSmallSectionsKeyInequalityStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_hermitian_small_sections_key_inequality : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  first | exact @GlobalTheory.HSNefCore.key_ineq | exact GlobalTheory.HSNefCore.key_ineq | (intros; apply GlobalTheory.HSNefCore.key_ineq <;> assumption)
end

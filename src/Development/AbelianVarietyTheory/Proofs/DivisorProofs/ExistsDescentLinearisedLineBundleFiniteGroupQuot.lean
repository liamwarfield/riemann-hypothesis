module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantLocalEquationCartierFiniteQuotien
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotient
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

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem functionFieldMap_fnOf (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {x : X}
    (hx : x ∈ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from hx)) s) =
      GlobalTheory.Cartier.fnOf (f ⁻¹ᵁ U) (GlobalTheory.Cartier.gen_mem hx) (f.app U s) := by
  rw [← GlobalTheory.Cartier.algebraMap_germ (show f x ∈ U from hx), functionFieldMap_algebraMap,
    ← GlobalTheory.Cartier.algebraMap_germ hx]
  congr 1
  exact Scheme.Hom.germ_stalkMap_apply f U x hx s

theorem fnOf_appLE (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    {x : X} (hx : x ∈ V) (s : Γ(Y, U)) :
    GlobalTheory.Cartier.fnOf V (GlobalTheory.Cartier.gen_mem hx) (f.appLE U V e s) =
      functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from e hx)) s) := by
  rw [functionFieldMap_fnOf f (e hx)]
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact X.presheaf.germ_res_apply (homOfLE e) _ _ _

end GlobalTheory.FnPull

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {Γ : Type} [Group Γ]

theorem functionFieldMap_act (ρ : Γ →* Aut X) (q : X ⟶ Y) [IsDominant q]
    (hq : ∀ g, (ρ g).asIso.hom ≫ q = q) (hs : Function.Surjective q) (g : Γ) [IsDominant (ρ g).asIso.hom]
    (c : Y.functionField) :
    functionFieldMap (ρ g).asIso.hom (functionFieldMap q c) = functionFieldMap q c := by
  obtain ⟨U₀, hη, s, rfl⟩ := Y.presheaf.exists_germ_eq c
  obtain ⟨x, hx⟩ := hs (genericPoint Y)
  have hx' : x ∈ q ⁻¹ᵁ U₀ := show q x ∈ U₀ from hx ▸ hη
  change functionFieldMap (ρ g).asIso.hom (functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)) =
    functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)
  rw [functionFieldMap_fnOf q hx' s]
  obtain ⟨e, hinv⟩ := isInvariantSection_app ρ q hq U₀ s g
  rw [← fnOf_appLE (ρ g).asIso.hom e hx', hinv]

theorem isInvariantSection_of_fnOf [Finite Γ] {ρ : Γ →* Aut X} {q : X ⟶ Y} [IsDominant q]
    (h : IsAffineQuotient ρ q) {V : Y.Opens} {x : X} (hx : x ∈ q ⁻¹ᵁ V) (c : Γ(X, q ⁻¹ᵁ V))
    (b : Y.functionField) (hc : GlobalTheory.Cartier.fnOf _ (GlobalTheory.Cartier.gen_mem hx) c = functionFieldMap q b) :
    IsInvariantSection ρ _ c := fun g ↦ by
  haveI : IsIso (ρ g).asIso.hom := Iso.isIso_hom _
  refine ⟨h.preimage_le V g, GlobalTheory.Cartier.fnOf_injective _ (GlobalTheory.Cartier.gen_mem hx) ?_⟩
  rw [fnOf_appLE (ρ g).asIso.hom (h.preimage_le V g) hx, hc,
    functionFieldMap_act ρ q h.comp_eq h.surjective.surj g]

end GlobalTheory.FnPull

namespace GlobalTheory.OrbitSep

theorem unitAt_of_forall_unitAt_fibre : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (y : W) (b : W.functionField),
    (∀ x, q x = y → UnitAt x (functionFieldMap q b)) → UnitAt y b := by
  intro X W _ _ Γ _ _ ρ q _ h y b hb
  have hsurj : Function.Surjective q := h.surjective.surj
  haveI := h.isIntegralHom
  let O : Set X := {x | GlobalTheory.Cartier.UnitAt x (functionFieldMap q b)}
  have hOo : IsOpen O := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hx
    exact ⟨U, fun z hz ↦ hU z hz, U.isOpen, hxU⟩
  have hV : IsOpen (q '' Oᶜ)ᶜ := (q.isClosedMap _ hOo.isClosed_compl).isOpen_compl
  let V : W.Opens := ⟨_, hV⟩
  obtain ⟨x₀, hx₀⟩ := hsurj y
  have hyV : y ∈ V := fun ⟨x, hx, e⟩ ↦ hx (hb x e)
  have hx₀V : x₀ ∈ q ⁻¹ᵁ V := show q x₀ ∈ V from hx₀ ▸ hyV
  have hUO : ∀ x ∈ q ⁻¹ᵁ V, GlobalTheory.Cartier.UnitAt x (functionFieldMap q b) := fun x hx ↦ by
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hUO
  have hgen := GlobalTheory.Cartier.gen_mem hx₀V
  have ha1 : GlobalTheory.Cartier.fnOf _ hgen (a : Γ(X, q ⁻¹ᵁ V)) = functionFieldMap q b := ha hgen
  have ha2 : GlobalTheory.Cartier.fnOf _ hgen ((a⁻¹ : Γ(X, q ⁻¹ᵁ V)ˣ) : Γ(X, q ⁻¹ᵁ V)) =
      functionFieldMap q b⁻¹ := by
    rw [map_units_inv, ha1, map_inv₀]
  obtain ⟨t, ht⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b ha1)
  obtain ⟨t', ht'⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b⁻¹ ha2)
  have htt : t * t' = 1 := h.app_injective V (by rw [map_mul, ht, ht', Units.mul_inv, map_one])
  let u : Γ(W, V)ˣ := ⟨t, t', htt, by rw [mul_comm]; exact htt⟩
  have hgenW := GlobalTheory.Cartier.gen_mem hyV
  have hbu : GlobalTheory.Cartier.fnOf V hgenW t = b := (functionFieldMap q).injective (by
    rw [GlobalTheory.FnPull.functionFieldMap_fnOf q hx₀V t, ht, ha1])
  rw [← hbu]
  exact GlobalTheory.Cartier.unitAt_fnOf hyV hgenW u

end GlobalTheory.OrbitSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotientStatement
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
theorem _root_.GlobalTheory.T.rationalFunctionUnitAtPoint_of_fibre_quotient : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (y : W) (b : W.functionField),
    (∀ x, q x = y → UnitAt x (functionFieldMap q b)) → UnitAt y b := by
  first | exact @GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre | exact GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre | (intros; apply GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorGroupQuotientDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorGroupQuotientDescent
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

namespace GlobalTheory.Cartier.Descent

theorem unitAt_functionFieldMap {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W)
    [IsDominant q] (x : X) {f : W.functionField} (h : UnitAt (q x) f) :
    UnitAt x (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap x a, ha.map _, (functionFieldMap_algebraMap q x a).symm⟩

theorem exists_cartierDiv_descent : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    ∃ E : CartierDiv W, ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
  intro X W _ _ Γ _ _ ρ q _ hq D h
  choose b hb using h
  have : IsIntegralHom q := hq.isIntegralHom
  have hcl : IsClosedMap q := q.isClosedMap

  have hloc : ∀ y : W, ∃ U : W.Opens, y ∈ U ∧ ∃ f, ∀ y' ∈ U, germOf y' (b y') = germOf y' f := by
    intro y
    let O : Set X := {x | D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom (b y))}
    have hO : IsOpen O := isOpen_iff_forall_mem_open.2 fun x hx => by
      obtain ⟨U, hU, hU'⟩ := CartierDiv.IsEqn.exists_nhds hx
      exact ⟨U, fun z hz => hU' z hz, U.isOpen, hU⟩
    have hZ : IsClosed (q '' Oᶜ) := hcl _ hO.isClosed_compl
    refine ⟨⟨(q '' Oᶜ)ᶜ, hZ.isOpen_compl⟩, ?_, b y, fun y' hy' => ?_⟩
    · rintro ⟨x, hx, hxy⟩
      exact hx (hb y x hxy)
    · refine (germOf_eq_iff.2 ?_).symm
      refine GlobalTheory.T.rationalFunctionUnitAtPoint_of_fibre_quotient X W Γ ρ q hq y' _ fun x hx => ?_
      have h1 : x ∈ O := by
        by_contra hn
        exact hy' ⟨x, hn, hx⟩
      have h2 := (h1 : D.IsEqn x _).iff_unitAt.1 (hb y' x hx)
      simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using h2
  let E : CartierDiv W := show cartierGroup W from ⟨fun y => germOf y (b y), hloc⟩
  refine ⟨E, fun y b' hE x hx => ?_⟩
  have hu : UnitAt y ((b' : W.functionField) / b y) := germOf_eq_iff.1 hE
  subst hx
  refine (hb (q x) x rfl).iff_unitAt.2 ?_
  have := unitAt_functionFieldMap q x hu
  simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using this

end GlobalTheory.Cartier.Descent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorGroupQuotientDescentStatement
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
theorem _root_.GlobalTheory.T.exists_cartierDivisor_group_quotient_descent : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    ∃ E : CartierDiv W, ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
  first | exact @GlobalTheory.Cartier.Descent.exists_cartierDiv_descent | exact GlobalTheory.Cartier.Descent.exists_cartierDiv_descent | (intros; apply GlobalTheory.Cartier.Descent.exists_cartierDiv_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapEqOfGroupInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapEqOfGroupInvariant
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

namespace GlobalTheory.OrbitSep

theorem functionFieldMap_germToFunctionField {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ X') [IsDominant f] (V : X'.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) [Nonempty U]
    [Nonempty V] (s : Γ(X', V)) :
    functionFieldMap f (X'.germToFunctionField V s) = X.germToFunctionField U (f.appLE V U e s) := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hfx : f (genericPoint X) ∈ V := e hx
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X') hfx, functionFieldMap_algebraMap,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx]
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply f V _ hfx s).trans
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE e) _ hx (f.app V s)).symm

theorem exists_functionFieldMap_eq_of_invariant (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W]
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q]
    (h : IsAffineQuotient ρ q) (u : X.functionFieldˣ) (hu : ∀ γ, fnAct ρ γ u = u) :
    ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  classical
  have := Fintype.ofFinite Γ
  have := h.isAffineHom
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  haveI : Nonempty V := ⟨⟨_, hyV⟩⟩
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := (show IsAffineOpen V from hV).preimage q
  obtain ⟨x, hx⟩ := q.denseRange.exists_mem_open V.isOpen ⟨_, hyV⟩
  haveI : Nonempty (q ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  have hst := h.preimage_le V
  haveI (γ : Γ) : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  let σ : Γ → Γ(X, q ⁻¹ᵁ V) →+* Γ(X, q ⁻¹ᵁ V) := fun γ ↦ ((ρ γ).asIso.hom.appLE _ _ (hst γ)).hom
  have hσ (γ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) :
      functionFieldMap (ρ γ).asIso.hom (algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField s) =
        algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField (σ γ s) :=
    functionFieldMap_germToFunctionField _ _ _ (hst γ) s
  have hσ1 (s : Γ(X, q ⁻¹ᵁ V)) : σ 1 s = s := by
    have e1 : (ρ 1).asIso.hom = 𝟙 X := by rw [map_one]; rfl
    change (ρ 1).asIso.hom.appLE _ _ (hst 1) s = s
    simp only [e1]
    exact congr($(X.presheaf.map_id (Opposite.op (q ⁻¹ᵁ V))) s)
  have hσmul (γ δ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) : σ δ (σ γ s) = σ (γ * δ) s := by
    have e2 : (ρ (γ * δ)).asIso.hom = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom := by rw [map_mul]; rfl
    change (ρ δ).asIso.hom.appLE _ _ (hst δ) ((ρ γ).asIso.hom.appLE _ _ (hst γ) s) =
      (ρ (γ * δ)).asIso.hom.appLE _ _ (hst (γ * δ)) s
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, e2]
  set e := algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField with he_def
  have einj : Function.Injective e := IsFractionRing.injective _ _
  have hfu (δ : Γ) : functionFieldMap (ρ δ).asIso.hom (u : X.functionField) = u :=
    congrArg Units.val (hu δ)
  obtain ⟨a, t, ht, hat⟩ := IsFractionRing.div_surjective (A := Γ(X, q ⁻¹ᵁ V)) (u : X.functionField)
  have ht0 : e t ≠ 0 := by
    rw [Ne, ← map_zero e]
    exact fun h0 ↦ nonZeroDivisors.ne_zero ht (einj h0)
  let N := ∏ γ, σ γ t
  have hN (δ : Γ) : σ δ N = N := by
    simp only [N, map_prod, hσmul]
    exact Fintype.prod_equiv (Equiv.mulRight δ) _ _ (fun _ ↦ rfl)
  have hNe : e N ≠ 0 := by
    simp only [N, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun γ _ ↦ ?_
    rw [← hσ]
    exact (map_ne_zero _).mpr ht0
  let c := a * ∏ γ ∈ Finset.univ.erase 1, σ γ t
  have hc : e c = u * e N := by
    have hsplit : N = t * ∏ γ ∈ Finset.univ.erase 1, σ γ t := by
      simp only [N]
      rw [← Finset.mul_prod_erase Finset.univ (fun γ ↦ σ γ t) (Finset.mem_univ 1), hσ1]
    rw [← he_def] at hat
    rw [hsplit]
    simp only [c, map_mul]
    rw [← hat]
    field_simp
  have hcinv (δ : Γ) : σ δ c = c := by
    apply einj
    rw [← hσ, hc, map_mul, hfu, hσ, hN]
  obtain ⟨bc, hbc⟩ := h.mem_range_app V c fun δ ↦ ⟨hst δ, hcinv δ⟩
  obtain ⟨bN, hbN⟩ := h.mem_range_app V N fun δ ↦ ⟨hst δ, hN δ⟩
  have hq (b : Γ(W, V)) : functionFieldMap q (W.germToFunctionField V b) = e (q.app V b) := by
    rw [Scheme.Hom.app_eq_appLE]
    exact functionFieldMap_germToFunctionField q V (q ⁻¹ᵁ V) le_rfl b
  have hbN0 : W.germToFunctionField V bN ≠ 0 := by
    intro h0
    apply hNe
    rw [← hbN, ← hq, h0, map_zero]
  have hbc0 : W.germToFunctionField V bc ≠ 0 := by
    intro h0
    apply mul_ne_zero u.ne_zero hNe
    rw [← hc, ← hbc, ← hq, h0, map_zero]
  refine ⟨Units.mk0 (W.germToFunctionField V bc / W.germToFunctionField V bN)
    (div_ne_zero hbc0 hbN0), Units.ext ?_⟩
  simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_div₀, hq, hbc, hbN, hc]
  field_simp

end GlobalTheory.OrbitSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapEqOfGroupInvariantStatement
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
theorem _root_.GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ u : X.functionFieldˣ,
    (∀ γ, fnAct ρ γ u = u) → ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  first | exact @GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant | exact GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant | (intros; apply GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentLinearisedLineBundleFiniteGroupQuot
set_option autoImplicit false

noncomputable section

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

namespace GlobalTheory.QuotDescent

private theorem descent_algebraMap_stalkCongr_of_eq {X : Scheme.{0}} [IsIntegral X] {x y : X} (h : x = y)
    (a : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk y) X.functionField ((X.presheaf.stalkCongr (.of_eq h)).hom a) =
      algebraMap (X.presheaf.stalk x) X.functionField a := by
  subst h
  simp

private theorem descent_fromSpecResidueField_comp_eq_of_fixes (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ]
    (ρ : Γ →* Aut X) (γ : Γ) (x : X) (hx : (ρ γ).asIso.hom x = x)
    (h : ∀ u : X.functionFieldˣ, RegAt x u → ZeroAt x ((fnAct ρ γ u : X.functionField) - u)) :
    X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x := by
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  set φ := (ρ γ).asIso.hom with hφ
  have key : (X.residueFieldCongr hx.symm).hom ≫ φ.residueFieldMap x = 𝟙 _ := by
    rw [← cancel_epi (X.residue x), Category.comp_id, X.residue_residueFieldCongr_assoc,
      Scheme.residue_residueFieldMap]
    ext a
    change IsLocalRing.residue _ (φ.stalkMap x ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom a)) =
      IsLocalRing.residue _ a
    set b := (X.presheaf.stalkCongr (.of_eq hx.symm)).hom a with hb
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    by_cases ha : a = 0
    · rw [hb, ha, map_zero, map_zero, sub_zero]
      exact zero_mem _
    · have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
      obtain ⟨c, hc, e⟩ := h (Units.mk0 _ hne) ⟨a, rfl⟩
      have e2 : ((fnAct ρ γ (Units.mk0 _ hne) : X.functionFieldˣ) : X.functionField) =
          GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) := rfl
      have e4 : GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) =
          algebraMap (X.presheaf.stalk x) X.functionField (φ.stalkMap x b) := by
        rw [← descent_algebraMap_stalkCongr_of_eq hx.symm a, ← hb]
        exact GlobalTheory.functionFieldMap_algebraMap φ x b
      rw [e2, Units.val_mk0, e4, ← map_sub] at e
      rwa [← IsFractionRing.injective _ _ e]
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← X.residueFieldCongr_fromSpecResidueField hx.symm, ← Category.assoc, ← Spec.map_comp, key,
    Spec.map_id, Category.id_comp]


theorem functionFieldMap_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    functionFieldMap (a ≫ b) = (functionFieldMap a).comp (functionFieldMap b) := by
  have e : Spec.map (CommRingCat.ofHom (functionFieldMap (a ≫ b))) ≫ genericFieldPoint Z =
      Spec.map (CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b))) ≫
        genericFieldPoint Z := by
    rw [specMap_functionFieldMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      specMap_functionFieldMap, ← Category.assoc, ← Category.assoc, specMap_functionFieldMap]
  haveI : Mono (genericFieldPoint Z) := inferInstanceAs (Mono (Z.fromSpecStalk _))
  have := Spec.map_injective ((cancel_mono _).mp e)
  exact congrArg CommRingCat.Hom.hom this

theorem fnAct_mul : ∀ (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ] (ρ : Γ →* Aut X) (γ δ : Γ)
    (u : X.functionFieldˣ), fnAct ρ (γ * δ) u = fnAct ρ δ (fnAct ρ γ u) := by
  intro X _ Γ _ ρ γ δ u
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  haveI : IsIso (ρ δ).asIso.hom := Iso.isIso_hom (ρ δ).asIso
  haveI : IsIso (ρ (γ * δ)).asIso.hom := Iso.isIso_hom (ρ (γ * δ)).asIso
  have hc : (ρ (γ * δ)).asIso.hom = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom := by
    rw [map_mul, Aut.mul_asIso]; rfl
  apply Units.ext
  change functionFieldMap (ρ (γ * δ)).asIso.hom (u : X.functionField) =
    functionFieldMap (ρ δ).asIso.hom (functionFieldMap (ρ γ).asIso.hom (u : X.functionField))
  have key : ∀ (f : X ⟶ X) (_ : IsDominant f), f = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom →
      functionFieldMap f (u : X.functionField) =
        functionFieldMap (ρ δ).asIso.hom (functionFieldMap (ρ γ).asIso.hom (u : X.functionField)) := by
    rintro f _ rfl
    rw [functionFieldMap_comp]
    rfl
  exact key _ inferInstance hc

theorem descent : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ W) (sW : W ⟶ Sp F) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB), IsProjOver (q ≫ sW) → IsAffineQuotient ρ q → RatLin ρ L hL → ∃ (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = cls L hL := by
  intro F _ _ X W _ q sW Γ _ _ ρ L hL _ hq hR
  obtain ⟨D, c, hcls, hcoc, heq, hin⟩ := hR
  haveI : IsIntegral W := hq.isIntegral
  haveI : Surjective q := hq.surjective
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (toFunctionField (q ≫ sW)).injective
  let σ : Γ → X.functionField →+* X.functionField := fun γ =>
    haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso; functionFieldMap (ρ γ).asIso.hom
  have hσu : ∀ γ (u : X.functionFieldˣ), ((fnAct ρ γ u : X.functionFieldˣ) : X.functionField) = σ γ u :=
    fun _ _ => rfl
  have hσ : ∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a) := by
    intro γ δ a
    by_cases ha : a = 0
    · simp [ha]
    · have := congrArg Units.val (fnAct_mul X Γ ρ γ δ (Units.mk0 a ha))
      rwa [hσu, hσu, hσu] at this
  have hcoc' : ∀ γ δ, (c (γ * δ) : X.functionField) = σ δ (c γ) * c δ := fun γ δ => by
    rw [hcoc, Units.val_mul, hσu]
  have htriv : ∀ γ, (∀ a, σ γ a = a) → c γ = 1 := by
    intro γ hγ
    have hη : (ρ γ).asIso.hom (genericPoint X) = genericPoint X := by
      haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
      have h1 := (genericPoint_spec X).image (ρ γ).asIso.hom.continuous
      have hs : Function.Surjective (ρ γ).asIso.hom.base := (ρ γ).asIso.hom.surjective
      simp only [Set.top_eq_univ, Set.image_univ, hs.range_eq, closure_univ] at h1
      exact h1.eq (genericPoint_spec X)
    have hfix := descent_fromSpecResidueField_comp_eq_of_fixes X Γ ρ γ (genericPoint X) hη (fun u _ => by rw [hσu, hγ, sub_self]; exact zeroAt_zero _)
    have h0 := hin γ _ 1 hfix (D.isEqn_genericPoint 1)
    have h1 : ((fnAct ρ γ 1 * (c γ)⁻¹ * 1⁻¹ : X.functionFieldˣ) : X.functionField) - 1 = 0 := by
      by_contra hne
      exact (zeroAt_iff.1 h0).2 (unitAt_genericPoint hne)
    rw [map_one, one_mul, inv_one, mul_one, sub_eq_zero, ← Units.val_one, Units.val_inj, inv_eq_one] at h1
    exact h1
  obtain ⟨f, hf⟩ := GlobalTheory.T.hilbert90_finite_rightAction_charZero_field _ Γ σ hσ c hcoc' htriv
  have hfu : ∀ γ, fnAct ρ γ f = c γ * f := fun γ => Units.ext (by rw [hσu, Units.val_mul]; exact hf γ)
  set D' := D - CartierDiv.principal f with hD'
  have hD : D' + CartierDiv.principal f = D := sub_add_cancel _ _
  have hinv' : ∀ γ x g, D'.IsEqn ((ρ γ).asIso.hom x) g → D'.IsEqn x (fnAct ρ γ g) := by
    intro γ x g h
    have h1 := heq γ x (g * f) (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f _))
    have h2 := h1.sub (CartierDiv.isEqn_principal f x)
    have e : fnAct ρ γ g = fnAct ρ γ (g * f) * (c γ)⁻¹ / f := by
      rw [map_mul, hfu]; simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h2
  have hin' : ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x → D'.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1) := by
    intro γ x g hx h
    have h1 := hin γ x (g * f) hx (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f x))
    have e : fnAct ρ γ g * g⁻¹ = fnAct ρ γ (g * f) * (c γ)⁻¹ * (g * f)⁻¹ := by
      rw [map_mul, hfu]; simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h1
  have hloc := GlobalTheory.T.exists_invariant_localEquation_cartier_finiteQuotient F X W (q ≫ sW) Γ ρ q hq D' hinv' hin'
  have key : ∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y →
      D'.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
    intro y
    obtain ⟨x, rfl⟩ := q.surjective y
    obtain ⟨g, hg, hgx⟩ := hloc x
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant X W Γ ρ q hq g hg
    refine ⟨b, fun x' hx' => ?_⟩
    obtain ⟨γ, rfl⟩ := (hq.apply_eq_iff x x').1 hx'.symm
    rw [hb]
    have hp : (ρ γ⁻¹).asIso.hom ((ρ γ).asIso.hom x) = x := by
      rw [map_inv]
      exact Scheme.inv_hom_apply _ _
    have := hinv' γ⁻¹ ((ρ γ).asIso.hom x) g (by rw [hp]; exact hgx)
    rwa [hg] at this
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_cartierDivisor_group_quotient_descent X W Γ ρ q hq D' key
  refine ⟨toLB E, isLB_toLB E, ?_⟩
  rw [GlobalTheory.T.cechPicardPullback_cartierDivisorBundle_eq X W q D' E hE]
  calc cls (toLB D') (isLB_toLB D') = toPic D' := (toPic_apply D').symm
    _ = toPic D := by rw [hD', map_sub, toPic_principal, sub_zero]
    _ = cls L hL := hcls

end GlobalTheory.QuotDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentLinearisedLineBundleFiniteGroupQuotStatement
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
theorem _root_.GlobalTheory.T.exists_descent_linearised_lineBundle_finiteGroup_quotient : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ W) (sW : W ⟶ Sp F) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB), IsProjOver (q ≫ sW) → IsAffineQuotient ρ q → RatLin ρ L hL → ∃ (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = cls L hL := by
  first | exact @GlobalTheory.QuotDescent.descent | exact GlobalTheory.QuotDescent.descent | (intros; apply GlobalTheory.QuotDescent.descent <;> assumption)
end

module

public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolution
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsRoundedDownDivisor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntOfIsIntegral
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistAmple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardIdealRegularity
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
noncomputable section

namespace GlobalTheory.PushIdeal

open GlobalTheory.Twist GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

section Rat

variable {Y : Scheme.{0}} [IsIntegral Y] {D : CartierDiv Y}

def genChart (D : CartierDiv Y) : (toLB D).ι := (exists_chart (isLB_toLB D) (genericPoint Y)).choose

theorem genChart_mem (D : CartierDiv Y) : genericPoint Y ∈ (toLB D).U (genChart D) :=
  (exists_chart (isLB_toLB D) (genericPoint Y)).choose_spec

def cd {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) (i : (toLB D).ι) :
    Γ(Y, W ⊓ (toLB D).U i) :=
  structureModuleSectionsEquiv _ (coord σ i)

theorem cd_rel {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) (i j : (toLB D).ι)
    (h : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U j) :
    fnOf _ (memInf h.1.1 h.1.2) (cd σ i) = ((i.1.2 : Y.functionField) / j.1.2) *
      fnOf _ (memInf h.1.1 h.2) (cd σ j) := by
  have e := congrArg (fun m => fnOf _ h (structureModuleSectionsEquiv _ m))
    (coord_rel σ i j (inf_le_left)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  simp only [LinearEquiv.map_smul, smul_eq_mul, map_mul] at e
  change fnOf _ h (resG Y _ (cd σ i)) = fnOf _ h (resG Y _ ((toLB D).g i j).val) *
    fnOf _ h (resG Y _ (cd σ j)) at e
  rw [fnOf_resG, fnOf_resG, fnOf_resG, fnOf_toLB_g] at e
  exact e


open Classical in
def ratOf {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) : Y.functionField :=
  if h : genericPoint Y ∈ W then
    fnOf _ (memInf h (genChart_mem D)) (cd σ (genChart D)) / ((genChart D).1.2 : Y.functionField)
  else 0

theorem ratOf_mul {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W))
    (i : (toLB D).ι) (h : genericPoint Y ∈ W ⊓ (toLB D).U i) :
    ratOf σ * (i.1.2 : Y.functionField) = fnOf _ h (cd σ i) := by
  have hj : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U (genChart D) := ⟨h, genChart_mem D⟩
  have hW : genericPoint Y ∈ W := h.1
  rw [ratOf, dite_eq_left hW, cd_rel σ i (genChart D) hj]
  have := Units.ne_zero (genChart D).1.2
  field_simp

theorem regularAt_ratOf {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W))
    {y : Y} (hy : y ∈ W) : D.RegularAt y (ratOf σ) := by
  obtain ⟨i, hi⟩ := exists_chart (isLB_toLB D) y
  have h : y ∈ W ⊓ (toLB D).U i := ⟨hy, hi⟩
  exact ⟨i.1.2, i.2.2 y hi, by rw [ratOf_mul σ i (gen_mem h)]; exact regAt_fnOf h _ _⟩

theorem sec_ext' {W : Y.Opens} {σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)}
    (h : ∀ i hi, fnOf (W ⊓ (toLB D).U i) hi (cd σ i) = fnOf _ hi (cd τ i)) : σ = τ :=
  sec_ext fun i => (structureModuleSectionsEquiv _).injective (GlobalTheory.Cartier.fn_ext (h i))

theorem ratOf_injective {W : Y.Opens}
    {σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)} (e : ratOf σ = ratOf τ) : σ = τ :=
  sec_ext' fun i h => by rw [← ratOf_mul σ i h, ← ratOf_mul τ i h, e]

theorem ratOf_add {W : Y.Opens} (σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) :
    ratOf (σ + τ) = ratOf σ + ratOf τ := by
  by_cases hW : genericPoint Y ∈ W
  · have h : genericPoint Y ∈ W ⊓ (toLB D).U (genChart D) := ⟨hW, genChart_mem D⟩
    apply mul_right_cancel₀ (Units.ne_zero (genChart D).1.2)
    rw [add_mul, ratOf_mul _ _ h, ratOf_mul _ _ h, ratOf_mul _ _ h, ← map_add (f := _)]
    congr 1
  · simp [ratOf, dif_neg hW]

theorem ratOf_smul {W : Y.Opens} (hW : genericPoint Y ∈ W) (a : Γ(Y, W))
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) :
    ratOf (a • σ) = fnOf W hW a * ratOf σ := by
  have h : genericPoint Y ∈ W ⊓ (toLB D).U (genChart D) := ⟨hW, genChart_mem D⟩
  apply mul_right_cancel₀ (Units.ne_zero (genChart D).1.2)
  rw [mul_assoc, ratOf_mul _ _ h, ratOf_mul _ _ h]
  change fnOf _ h (structureModuleSectionsEquiv _ (resG Y _ a • coord σ (genChart D))) = _
  rw [LinearEquiv.map_smul, smul_eq_mul, map_mul, fnOf_resG]
  rfl

theorem ratOf_res {W W' : Y.Opens} (hle : W' ≤ W) (hW : genericPoint Y ∈ W')
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) :
    ratOf (resM _ hle σ) = ratOf σ := by
  have h : genericPoint Y ∈ W' ⊓ (toLB D).U (genChart D) := ⟨hW, genChart_mem D⟩
  have h' : genericPoint Y ∈ W ⊓ (toLB D).U (genChart D) := ⟨hle hW, genChart_mem D⟩
  apply mul_right_cancel₀ (Units.ne_zero (genChart D).1.2)
  rw [ratOf_mul _ _ h, ratOf_mul _ _ h']
  change fnOf _ h (resG Y _ (cd σ (genChart D))) = _
  rw [fnOf_resG]

theorem exists_ratOf_eq {W : Y.Opens} (hW : genericPoint Y ∈ W) {f : Y.functionField}
    (hf : ∀ y ∈ W, D.RegularAt y f) :
    ∃ σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W), ratOf σ = f := by
  have key (i : (toLB D).ι) : ∃ a : Γ(Y, W ⊓ (toLB D).U i), ∀ hi, fnOf _ hi a = f * i.1.2 := by
    by_cases hi : genericPoint Y ∈ W ⊓ (toLB D).U i
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hi fun x hx =>
        (i.2.2 x hx.2).regularAt_iff.1 (hf x hx.1)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (hi h').elim⟩
  choose a ha using key
  refine ⟨mkSec (F := GlobalTheory.structureModule Y) (L := toLB D)
    (fun i => (structureModuleSectionsEquiv _).symm (a i)) fun i j => ?_, ?_⟩
  · apply (structureModuleSectionsEquiv _).injective
    rw [LinearEquiv.map_smul, smul_eq_mul]
    change resG Y _ (a i) = resG Y _ ((toLB D).g i j).val * resG Y _ (a j)
    refine GlobalTheory.Cartier.fn_ext fun hij => ?_
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, ha, ha, fnOf_toLB_g]
    have := Units.ne_zero j.1.2
    field_simp
  · have h : genericPoint Y ∈ W ⊓ (toLB D).U (genChart D) := ⟨hW, genChart_mem D⟩
    apply mul_right_cancel₀ (Units.ne_zero (genChart D).1.2)
    rw [ratOf_mul _ _ h]
    exact ha _ h

end Rat

section Push

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {s : Y ⟶ X} [IsDominant s]
  {D : CartierDiv Y}

theorem gen_mem_preimage {V : X.Opens} (hV : genericPoint X ∈ V) : genericPoint Y ∈ s ⁻¹ᵁ V := by
  obtain ⟨y, hy⟩ := s.denseRange.exists_mem_open V.isOpen ⟨_, hV⟩
  exact gen_mem (show y ∈ s ⁻¹ᵁ V from hy)

theorem fnMap_fnOf {U : X.Opens} {y : Y} (hy : y ∈ s ⁻¹ᵁ U) (a : Γ(X, U)) :
    functionFieldMap s (fnOf U (gen_mem (show s y ∈ U from hy)) a) =
      fnOf (s ⁻¹ᵁ U) (gen_mem hy) (s.app U a) := by
  rw [← algebraMap_germ (show s y ∈ U from hy), functionFieldMap_algebraMap, ← algebraMap_germ hy]
  congr 1
  exact Scheme.Hom.germ_stalkMap_apply s U y hy a


variable (s D) in
def tw {V : X.Opens}
    (σ : Γ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)), V)) :
    Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V) := σ


variable (s D) in
def untw {V : X.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    Γ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)), V) := σ

variable (hbij : Function.Bijective (functionFieldMap s))

def finv : Y.functionField →+* X.functionField :=
  (RingEquiv.ofBijective (functionFieldMap s) hbij).symm.toRingHom

theorem fnMap_finv (f : Y.functionField) : functionFieldMap s (finv hbij f) = f :=
  (RingEquiv.ofBijective (functionFieldMap s) hbij).apply_symm_apply f

theorem finv_fnMap (f : X.functionField) : finv hbij (functionFieldMap s f) = f :=
  (RingEquiv.ofBijective (functionFieldMap s) hbij).symm_apply_apply f

theorem finv_injective : Function.Injective (finv hbij) :=
  (RingEquiv.ofBijective (functionFieldMap s) hbij).symm.injective

variable (hReg : ∀ (x : X) (f : X.functionField),
  (∀ y : Y, s y ⤳ x → D.RegularAt y (functionFieldMap s f)) → GlobalTheory.Cartier.RegAt x f)

include hReg in
theorem regAt_finv {V : X.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) {x : X}
    (hx : x ∈ V) : GlobalTheory.Cartier.RegAt x (finv hbij (ratOf σ)) :=
  hReg x _ fun y hy => by
    rw [fnMap_finv]
    exact regularAt_ratOf σ (show s y ∈ V from hy.mem_open V.isOpen hx)


open Classical in
def funOf (V : X.Opens) (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) : Γ(X, V) :=
  if hV : genericPoint X ∈ V then
    (exists_fnOf_eq hV fun x hx => regAt_finv hbij hReg σ hx).choose else 0

theorem fnOf_funOf {V : X.Opens} (hV : genericPoint X ∈ V)
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    fnOf V hV (funOf hbij hReg V σ) = finv hbij (ratOf σ) := by
  rw [funOf, dite_eq_left hV]
  exact (exists_fnOf_eq hV fun x hx => regAt_finv hbij hReg σ hx).choose_spec

theorem funOf_add {V : X.Opens} (σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    funOf hbij hReg V (σ + τ) = funOf hbij hReg V σ + funOf hbij hReg V τ :=
  GlobalTheory.Cartier.fn_ext fun hV => by rw [map_add (f := _), fnOf_funOf, fnOf_funOf, fnOf_funOf, ratOf_add, map_add (f := _)]

theorem funOf_smul {V : X.Opens} (a : Γ(X, V))
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    funOf hbij hReg V (s.app V a • σ) = a * funOf hbij hReg V σ :=
  GlobalTheory.Cartier.fn_ext fun hV => by
    have hY := gen_mem_preimage (s := s) hV
    rw [map_mul, fnOf_funOf, fnOf_funOf, ratOf_smul hY, map_mul, ← fnMap_fnOf hY, finv_fnMap]

theorem funOf_res {V W : X.Opens} (h : W ≤ V)
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    funOf hbij hReg W (resM _ (s.preimage_mono h) σ) = resG X h (funOf hbij hReg V σ) :=
  GlobalTheory.Cartier.fn_ext fun hW => by
    rw [fnOf_resG, fnOf_funOf, fnOf_funOf, ratOf_res _ (gen_mem_preimage hW)]

theorem funOf_injective {V : X.Opens}
    {σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)}
    (e : funOf hbij hReg V σ = funOf hbij hReg V τ) : σ = τ := by
  by_cases hY : genericPoint Y ∈ s ⁻¹ᵁ V
  · have hV : genericPoint X ∈ V := gen_mem (show s (genericPoint Y) ∈ V from hY)
    have := congrArg (fnOf V hV) e
    rw [fnOf_funOf, fnOf_funOf] at this
    exact ratOf_injective (finv_injective hbij this)
  · exact sec_ext' fun i h => (hY h.1).elim

end Push

section Ideal

variable {X : Scheme.{0}} (J : X.IdealSheafData)

theorem exists_ideal {V : X.Opens} (f : Γ(X, V))
    (h : ∀ (U : X.affineOpens) (hU : U.1 ≤ V), resG X hU f ∈ J.ideal U) :
    ∃ t, structureModuleSectionsEquiv V ((idealModuleι J).app V t) = f := by
  have hc : V ≤ ⨆ k : {U : X.affineOpens // U.1 ≤ V}, k.1.1 := fun x hx => by
    obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
    exact Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩
  choose t ht using fun k : {U : X.affineOpens // U.1 ≤ V} =>
    (exists_idealModuleι_app_eq_iff_mem J k.1 (resG X k.2 f)).2 (h k.1 k.2)
  have e1 : ∀ (k : {U : X.affineOpens // U.1 ≤ V}) (W : X.Opens) (hW : W ≤ k.1.1),
      structureModuleSectionsEquiv W (resM _ hW ((idealModuleι J).app _ (t k))) =
        resG X (hW.trans k.2) f := fun k W hW => by
    change resG X hW (structureModuleSectionsEquiv _ ((idealModuleι J).app _ (t k))) = _
    rw [ht k, GlobalTheory.LB.resG_resG]
  obtain ⟨T, hT⟩ := exists_sec_of_cover (F := idealModule J)
    (fun k : {U : X.affineOpens // U.1 ≤ V} => k.1.1) (fun k => k.2) hc t fun k l =>
      injective_app_of_mono (idealModuleι J) _ ((structureModuleSectionsEquiv _).injective (by
        rw [app_resM, app_resM, e1, e1]))
  refine ⟨T, GlobalTheory.LB.fun_ext_of_cover (fun k : {U : X.affineOpens // U.1 ≤ V} => k.1.1)
    (fun k => k.2) hc fun k => ?_⟩
  change structureModuleSectionsEquiv _ (resM _ k.2 ((idealModuleι J).app V T)) = _
  rw [← app_resM, hT, ht]

theorem mem_ideal_of {V : X.Opens} (t : Γ(idealModule J, V)) (U : X.affineOpens) (hU : U.1 ≤ V) :
    resG X hU (structureModuleSectionsEquiv V ((idealModuleι J).app V t)) ∈ J.ideal U :=
  (exists_idealModuleι_app_eq_iff_mem J U _).1 ⟨resM _ hU t, by
    rw [app_resM]; rfl⟩

end Ideal

end GlobalTheory.PushIdeal

namespace GlobalTheory

open GlobalTheory.Twist GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.PushIdeal

theorem pushforward_twist_iso_idealModule : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (D : CartierDiv Y) (J : X.IdealSheafData), (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) → (∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → D.RegularAt y (functionFieldMap s f)) → RegAt x f) → Nonempty ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)) ≅ idealModule J) := by
  intro X Y _ _ s _ hbij D J hJ hReg

  have mem : ∀ (V : X.Opens)
      (σ : Γ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)), V)),
      ∃ t, structureModuleSectionsEquiv V ((idealModuleι J).app V t) =
        funOf hbij hReg V (tw s D σ) :=
    fun V σ => exists_ideal J _ fun U hU => by
      rw [hJ]
      intro y hy
      have hV : genericPoint X ∈ V := gen_mem (hU hy)
      rw [fnOf_resG, fnOf_funOf hbij hReg hV, fnMap_finv]
      exact regularAt_ratOf (tw s D σ) (show s y ∈ V from hU hy)
  choose l hl using mem
  have hι : ∀ V, Function.Injective fun t : Γ(idealModule J, V) =>
      structureModuleSectionsEquiv V ((idealModuleι J).app V t) := fun V =>
    (structureModuleSectionsEquiv V).injective.comp (injective_app_of_mono (idealModuleι J) V)
  let lin : ∀ V : X.Opens,
      Γ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)), V) →ₗ[Γ(X, V)]
        Γ(idealModule J, V) := fun V =>
    { toFun := l V
      map_add' := fun σ τ => hι V (by
        simp only [map_add (f := _), hl]
        exact funOf_add hbij hReg (tw s D σ) (tw s D τ))
      map_smul' := fun a σ => hι V (by
        simp only [Scheme.Modules.Hom.app_smul, LinearEquiv.map_smul, hl, smul_eq_mul,
          RingHom.id_apply]
        exact funOf_smul hbij hReg a (tw s D σ)) }
  let φ := GlobalTheory.LB.homOfLinear lin fun {V W} h σ => hι W (by
    change structureModuleSectionsEquiv W ((idealModuleι J).app W (l W _)) =
      structureModuleSectionsEquiv W ((idealModuleι J).app W (resM _ h (l V σ)))
    rw [hl, app_resM]
    change funOf hbij hReg W (resM _ (s.preimage_mono h) (tw s D σ)) =
      resG X h (structureModuleSectionsEquiv V ((idealModuleι J).app V (l V σ)))
    rw [hl, funOf_res])
  have hbj : ∀ V, Function.Bijective (φ.app V) := fun V => by
    refine ⟨fun σ τ e => funOf_injective hbij hReg ?_, fun t => ?_⟩
    · have e' := congrArg (fun t => structureModuleSectionsEquiv V ((idealModuleι J).app V t)) e
      change structureModuleSectionsEquiv V ((idealModuleι J).app V (l V σ)) =
        structureModuleSectionsEquiv V ((idealModuleι J).app V (l V τ)) at e'
      rwa [hl, hl] at e'
    · by_cases hV : genericPoint X ∈ V
      · have hY := gen_mem_preimage (s := s) hV
        obtain ⟨σ, hσ⟩ := exists_ratOf_eq (D := D) hY (f := functionFieldMap s (fnOf V hV
          (structureModuleSectionsEquiv V ((idealModuleι J).app V t)))) fun y hy => by
          obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
            (show s y ∈ V from hy)
          have := (hJ ⟨U, hU⟩ _).1 (mem_ideal_of J t ⟨U, hU⟩ hUV) y hxU
          rwa [fnOf_resG] at this
        refine ⟨untw s D σ, hι V ?_⟩
        change structureModuleSectionsEquiv V ((idealModuleι J).app V (l V (untw s D σ))) = _
        rw [hl]
        apply fnOf_injective V hV
        exact (fnOf_funOf hbij hReg hV _).trans ((congrArg _ hσ).trans (finv_fnMap hbij _))
      · refine ⟨0, hι V ?_⟩
        exact GlobalTheory.Cartier.fn_ext fun h => (hV h).elim
  haveI := isIso_of_bijective φ hbj
  exact ⟨asIso φ⟩

end GlobalTheory
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealIndependent
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealLocalMembership
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.MultLoc

theorem isProper_of_isProjOver_nadel_vanishing {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

noncomputable def multHom (z : Y) : CartierDiv Y →+ ℤ :=
  AddMonoidHom.mk' (fun D => D.mult z) (fun D E => CartierDiv.mult_add D E z)

theorem mult_neg' (D : CartierDiv Y) (z : Y) : (-D).mult z = -D.mult z :=
  map_neg (multHom z) D

theorem mult_sub' (D E : CartierDiv Y) (z : Y) : (D - E).mult z = D.mult z - E.mult z :=
  map_sub (multHom z) D E

theorem mult_nsmul' (D : CartierDiv Y) (r : ℕ) (z : Y) : (r • D).mult z = r * D.mult z := by
  rw [← nsmul_eq_mul]; exact map_nsmul (multHom z) r D

end GlobalTheory.MultLoc


open GlobalTheory.MultLoc in
theorem GlobalTheory.Discrepancy.inMultAt_iff_regularAt_logRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (u : X.functionFieldˣ), InMultAt p n η m G x u ↔ ∀ y : Y, s y = x → (-F).RegularAt y (functionFieldMap s (u : X.functionField)) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm hres hF x u
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hres.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.isNormalScheme_of_smooth (s ≫ p)
  haveI : IsProper s := by
    haveI := isProper_of_isProjOver_nadel_vanishing hp
    haveI := isProper_of_isProjOver_nadel_vanishing hres.proj
    exact IsProper.of_comp s p
  set Γ := pullCart s G - m • K with hΓ
  set η' := EtaleKlt.ratPull p s n η with hη'def
  have hη' : η' ≠ 0 := fun h =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s hres.bir n).1 (h.trans (map_zero _).symm))
  have hdisc : ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E →
      ∀ g : X.functionFieldˣ, discrep E' η' m (fnPull s g) = discrep E η m g := by
    intro E' E hO g
    simp only [discrep, hη'def, GlobalTheory.BirOrd.formOrd_ratPull_of_over k X Y p s hres.bir E' E hO n η hη,
      GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hO g]
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have eu : functionFieldMap s (u : X.functionField) = ((fnPull s u : Y.functionFieldˣ) : Y.functionField) := rfl
  constructor
  · intro hu y hy
    rw [eu, GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg Y (-F) y (fnPull s u)]
    intro z hz
    rw [mult_neg', hF z]
    by_cases hc : Order.coheight z = 1
    · obtain ⟨E', hE'⟩ : ∃ E' : DivOver (s ≫ p), E'.IsAt z :=
        DivOver.exists_isAt_of_coheight_eq_one hc
      obtain ⟨E, hO⟩ := GlobalTheory.T.exists_primeDivisor_over_target_birational k X Y p s hres.bir E'
      have hEx : E.Through x := hy ▸ GlobalTheory.T.primeDivisorCentre_through_image k X Y p s E' E hO y (hE'.through hz)
      obtain ⟨g, hg⟩ := G.exists_isEqn x
      have h1 := hu g hg E hEx
      have h2 : E.ord u = Scheme.ord ((fnPull s u : Y.functionFieldˣ) : Y.functionField) z := by
        rw [← GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hO u, hE'.ord_eq]
      have hgy : (pullCart s G).IsEqn y (fnPull s g) := isEqn_pullCart s (by rw [hy]; exact hg)
      obtain ⟨V, hV, hgV⟩ := hgy.exists_nhds
      have h3 := GlobalTheory.T.discrepancy_formula_divisor k Y (s ≫ p) n η' hη' K (pullCart s G) m hm hres.div E' z
        (fnPull s g) hE' (hgV z (hz.mem_open V.isOpen hV))
      rw [hdisc E' E hO g, ← hΓ] at h3
      rw [h2, h3] at h1
      set o := Scheme.ord ((fnPull s u : Y.functionFieldˣ) : Y.functionField) z
      have h4 : ((Γ.mult z : ℤ) : ℚ) < ((((o + 1) * m : ℤ)) : ℚ) := by
        push_cast
        have h6 : ((Γ.mult z : ℤ) : ℚ) / m < o + 1 := by rw [neg_div] at h1; linarith
        rwa [div_lt_iff₀ hmq] at h6
      have h5 := Int.ediv_lt_of_lt_mul hmz (by exact_mod_cast h4)
      omega
    · have h0 : Γ.mult z = 0 := by
        by_contra h; exact hc (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
      rw [Scheme.ord_eq_zero_of_coheight_neq_one hc, h0]
      simp
  · intro hR g hg E hE
    obtain ⟨E', hO⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational k X Y p s hres.bir E
    obtain ⟨y, hy, hE'y⟩ := GlobalTheory.T.divisor_center_proper_lift k X Y p s hres.bir inferInstance E' E hO x hE
    obtain ⟨f, hf⟩ := F.exists_isEqn y
    have hreg := hf.neg.regularAt_iff.1 (hR y hy)
    have hord : E'.ord f ≤ E'.ord (fnPull s u) := by
      have h0 : 0 ≤ E'.ord (fnPull s u * f⁻¹) := (E'.ord_nonneg_iff _).2 (hE'y _ hreg)
      rw [E'.ord_mul, E'.ord_inv] at h0
      omega
    set G' := pullCart s G - m • F with hG'
    have hg' : G'.IsEqn y (fnPull s g / f ^ m) :=
      (isEqn_pullCart s (by rw [hy]; exact hg)).sub (hf.nsmul m)
    have hmod : ∀ w, (G' - m • K).mult w = Γ.mult w % m := by
      intro w
      have e : G' - m • K = Γ - m • F := by rw [hG', hΓ]; abel
      rw [e, mult_sub', mult_nsmul', hF w, Int.emod_def]
    have hsupp : (G' - m • K).supp ≤ B := by
      intro w hw
      obtain ⟨z, hzw, hz0⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y (G' - m • K)).2.1 w).1 hw
      refine hres.supp (((GlobalTheory.T.cartier_divisor_mult_characterize Y Γ).2.1 w).2 ⟨z, hzw, fun h0 => hz0 ?_⟩)
      rw [hmod, h0, Int.zero_emod]
    have hcrit := (GlobalTheory.T.klt_of_snc_coefficients k Y (s ≫ p) n η' hη' K G' m B hm hres.div hres.snc hsupp y _ hg'
      E' hE'y).1 fun w _ => by rw [hmod]; exact Int.emod_lt_of_pos _ hmz
    have hd : discrep E' η' m (fnPull s g / f ^ m) = discrep E η m g + E'.ord f := by
      rw [← hdisc E' E hO g]
      simp only [discrep, div_eq_mul_inv, E'.ord_mul, E'.ord_inv, E'.ord_pow]
      push_cast
      field_simp
      ring
    rw [hd] at hcrit
    have h6 : (E'.ord f : ℚ) ≤ E.ord u := by
      rw [← GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hO u]; exact_mod_cast hord
    linarith
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealIndependent
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isMultIdeal_iff_regularAt : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J ↔ (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), (-F).RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  intro k _ _ X _ p n hproj η m G Y _ _ s _ K B F hη hm hres hF J
  have key := inMultAt_iff_regularAt_logRes k X p n hproj η m G Y s K B F hη hm hres hF
  unfold IsMultIdeal
  refine forall_congr' fun U => forall_congr' fun f => iff_congr Iff.rfl ?_
  constructor
  · intro H y hy
    by_cases h0 : fnOf U.1 (gen_mem hy) f = 0
    · rw [h0, map_zero]
      obtain ⟨g, hg⟩ := (-F).exists_isEqn y
      refine ⟨g, hg, ?_⟩
      rw [zero_mul]
      exact (regAt_zero (X := Y) (x := y))
    · have := (key (s y) (Units.mk0 _ h0)).1 (H (s y) hy _ rfl) y rfl
      simpa using this
  · intro H x hx u hu
    rw [key]
    rintro y rfl
    rw [hu]
    exact H y hx

end GlobalTheory.Discrepancy
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealIndependentStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_ideal_independent : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J ↔ (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), (-F).RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  first | exact @_root_.GlobalTheory.Discrepancy.isMultIdeal_iff_regularAt | exact _root_.GlobalTheory.Discrepancy.isMultIdeal_iff_regularAt | (intros; apply _root_.GlobalTheory.Discrepancy.isMultIdeal_iff_regularAt <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingTheorem
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealBoundaryMonotone
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealEffectiveBoundary
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealEffectiveBoundary
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem regAt_of_regularAt_neg_roundDown : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → (-F).RegularAt y (functionFieldMap s f)) → RegAt x f := by
  intro k _ _ X _ _ _ p n hproj _ Δ η m G Y _ _ s _ K B F hΔ hmult hres hF x f hf
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  by_cases hf0 : f = 0
  · subst hf0; exact regAt_zero x
  refine regAt_of_forall_coheight_eq_one fun z hzx hz1 => ?_
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hz1
  obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational k X Y p s hres.bir E
  obtain ⟨w, rfl, hE'⟩ := GlobalTheory.T.divisor_point_proper_lift k X Y p s hres.bir inferInstance E' E hE'E _ hE
  obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
  have hg' := isEqn_pullCart s hg
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hmult.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  have hd := GlobalTheory.T.discrepancy_formula_divisor k Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m
    hmult.pos hres.div E' w (fnPull s g) hE' hg'
  have hd2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
    simp only [discrep]
    have hform := GlobalTheory.T.form_order_birational_pullback k X Y p s hres.bir E' E hE'E n η hmult.ne_zero
    change E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η at hform
    rw [hform, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hE'E g]
  have hd3 := (hmult.eqn _ g hg).discrep_eq_neg hmult.pos (specializes_refl _) hE
  have hm : (0 : ℚ) < m := by exact_mod_cast hmult.pos
  have hnn : 0 ≤ (pullCart s G - m • K).mult w := by
    have e : ((pullCart s G - m • K).mult w : ℚ) / m = Δ (s w) := by
      rw [← hd2, hd] at hd3
      rw [neg_div] at hd3
      exact neg_injective hd3
    have h0 : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) / m := e ▸ hΔ (s w)
    have := (div_nonneg_iff.1 h0)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (not_le.2 hm)
  have hFn : 0 ≤ F.mult w := by
    rw [hF]; exact Int.ediv_nonneg hnn (by exact_mod_cast hmult.pos.le)
  obtain ⟨h, hh⟩ := F.exists_isEqn w
  have hreg := (hh.neg.regularAt_iff).1 (hf w hzx)
  set u : X.functionFieldˣ := Units.mk0 f hf0 with hu
  have hv : ((fnPull s u * h⁻¹ : Y.functionFieldˣ) : Y.functionField) =
      functionFieldMap s f * ((h⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
    simp [hu, fnPull]
  have h1 : 0 ≤ E'.ord (fnPull s u * h⁻¹) :=
    (E'.ord_nonneg_iff _).2 (hv ▸ (hE' _).2 hreg)
  rw [E'.ord_mul, E'.ord_inv, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hE'E u, hE'.ord_eq h,
    ← hh.mult_eq] at h1
  have h2 : 0 ≤ E.ord u := by omega
  exact (hE f).1 ((E.ord_nonneg_iff u).1 h2)

end GlobalTheory.Discrepancy
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealEffectiveBoundaryStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_ideal_effective_boundary : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → (-F).RegularAt y (functionFieldMap s f)) → RegAt x f := by
  first | exact @_root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown | exact _root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown | (intros; apply _root_.GlobalTheory.Discrepancy.regAt_of_regularAt_neg_roundDown <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.PushforwardIdealRegularity
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.pushforward_ideal_regularity : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (D : CartierDiv Y) (J : X.IdealSheafData), (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) → (∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → D.RegularAt y (functionFieldMap s f)) → RegAt x f) → Nonempty ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)) ≅ idealModule J) := by
  first | exact @_root_.GlobalTheory.pushforward_twist_iso_idealModule | exact _root_.GlobalTheory.pushforward_twist_iso_idealModule | (intros; apply _root_.GlobalTheory.pushforward_twist_iso_idealModule <;> assumption)
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

theorem nadel_of_logRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) N) i) := by
  intro k _ _ X _ _ _ p n hp hdim Δ η m G Y _ _ s _ K B hΔ hLM hR N M T hN hMlb r hT hr hcls hMnef
    a Fd A hA hFd J hJ i hi
  haveI := hR.smooth
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor k Y (s ≫ p) n hR.proj (pullCart s G - m • K) m
  have hJ' := (GlobalTheory.T.multiplier_ideal_independent k X p n hp η m G Y s K B F hLM.ne_zero hLM.pos hR hF J).1 hJ
  obtain ⟨e⟩ := GlobalTheory.T.pushforward_ideal_regularity X Y s hR.bir (-F) J hJ'
    (GlobalTheory.T.multiplier_ideal_effective_boundary k X p n hp hdim Δ η m G Y s K B F hΔ hLM hR hF)
  have hv := (GlobalTheory.T.multiplier_vanishing_nef_twist_ample k X p n hp η m G Y s K B F hLM.ne_zero hLM.pos hR hF N M T hN hMlb r hT hr
    hcls hMnef a Fd A hA hFd).1 i hi
  exact @Equiv.subsingleton _ _ (cohOn.mapIso ℤ ⊤ i ((twistFunctor N).mapIso e)).symm.toEquiv hv

end GlobalTheory
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem GlobalTheory.nadelVanishing : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → (letI := algebraΓOfHom p; IsBig k M) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) N) i) := by
  intro hP k _ _ X _ _ _ p n hproj hdim Δ η m G hΔ hlm N M T hN hM r hT hr hcls hMnef hMbig J hJ i hi
  have hZ : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hx : x ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at hx
    exact hx
  obtain ⟨Y, _, s, _, K, B, hres, -, a, Fd, A, hA, hkod⟩ :=
    GlobalTheory.LogResBig.exists_logRes_smul_eq_ample_add_eff hP k X p n hproj hdim η m G hlm.ne_zero ⊥ hZ M hM hMbig
  haveI : IsLocallyNoetherian Y :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y (s ≫ p) hres.smooth.smooth).2.2
  exact GlobalTheory.nadel_of_logRes k X p n hproj hdim Δ η m G Y s K B hΔ hlm hres N M T hN hM r hT hr hcls hMnef a Fd A hA hkod J hJ i hi
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealSupportNonKlt
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsMultiplierIdeal
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPushforwardRegularIdeal
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_pushforward_regular_ideal : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [QuasiCompact s] (D : CartierDiv Y), ∃ J : X.IdealSheafData, (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  first | exact @_root_.GlobalTheory.Cartier.PullIdeal.exists_idealSheaf | exact _root_.GlobalTheory.Cartier.PullIdeal.exists_idealSheaf | (intros; apply _root_.GlobalTheory.Cartier.PullIdeal.exists_idealSheaf <;> assumption)
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.MultIdealExists

theorem isProper_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem exists_isMultIdeal : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → ∃ J : X.IdealSheafData, IsMultIdeal p n η m G J := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B hη hm hres
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hres.smooth
  haveI : IsProper (s ≫ p) := isProper_of_isProjOver' hres.proj
  haveI : IsProper p := isProper_of_isProjOver' hp
  haveI : QuasiCompact s := QuasiCompact.of_comp s p
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor k Y (s ≫ p) n hres.proj (pullCart s G - m • K) m
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_pushforward_regular_ideal X Y s (-F)
  exact ⟨J, (GlobalTheory.T.multiplier_ideal_independent k X p n hp η m G Y s K B F hη hm hres hF J).2 hJ⟩

end GlobalTheory.MultIdealExists
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealLogResolution
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem inMultAt_one_iff_kltAt {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {p : X ⟶ Sp k} {n : ℕ} (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) {Δ : X → ℚ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    (hM : IsLogMult p n Δ η m G) (y : X) : InMultAt p n η m G y 1 ↔ KltAt p n Δ y := by
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  have hkey : ∀ g, G.IsEqn y g → (KltAt p n Δ y ↔ ∀ (E : DivOver p), E.Through y → -1 < discrep E η m g) :=
    fun g hg => IsLogEqn.kltAt_iff hn hM.ne_zero hM.pos (hM.eqn y g hg)
  constructor
  · intro h
    obtain ⟨g, hg⟩ := G.exists_isEqn y
    rw [hkey g hg]
    intro E hE
    have h1 := h g hg E hE
    simpa [DivOver.ord_one] using h1
  · intro h g hg E hE
    have h1 := (hkey g hg).1 h E hE
    simpa [DivOver.ord_one] using h1

theorem one_mem_ideal_iff {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {p : X ⟶ Sp k} {n : ℕ} (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) {Δ : X → ℚ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    (hM : IsLogMult p n Δ η m G) {J : X.IdealSheafData} (hJ : IsMultIdeal p n η m G J)
    (U : X.affineOpens) : (1 : Γ(X, U.1)) ∈ J.ideal U ↔ ∀ y ∈ U.1, KltAt p n Δ y := by
  rw [hJ U 1]
  constructor
  · intro h y hy
    exact (inMultAt_one_iff_kltAt hp hn hM y).1 (h y hy 1 (by simp))
  · intro h y hy u hu
    have : u = 1 := Units.ext (by simpa using hu)
    subst this
    exact (inMultAt_one_iff_kltAt hp hn hM y).2 (h y hy)

theorem mem_support_multIdeal_iff : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  intro k _ _ X _ _ _ p n hp hn Δ η m G Y _ _ s _ K B hM hR J hJ x
  have hO := (isOpen_kltAt_and_lcAt_of_isLogRes k X p n hp hn Δ η m G Y s K B hM hR).1
  have hb : ∀ {U : X.Opens} {z : X}, z ∈ U → ∃ U' ∈ X.affineOpens, z ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
  constructor
  · intro hx hk
    obtain ⟨V, hV, hxV, hVO⟩ := hb (show x ∈ (⟨_, hO⟩ : X.Opens) from hk)
    have h1 : (1 : Γ(X, V)) ∈ J.ideal ⟨V, hV⟩ :=
      (one_mem_ideal_iff hp hn hM hJ ⟨V, hV⟩).2 (fun y hy => hVO hy)
    have h2 := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).1 hx
    rw [Scheme.mem_zeroLocus_iff] at h2
    exact h2 1 h1 (by rw [Scheme.basicOpen_one]; exact hxV)
  · intro hnk
    by_contra hx
    obtain ⟨V, hV, hxV, -⟩ := hb (show x ∈ (⊤ : X.Opens) from trivial)
    have h2 : ¬ x ∈ X.zeroLocus (J.ideal ⟨V, hV⟩ : Set Γ(X, V)) := fun h =>
      hx ((Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).2 h)
    rw [Scheme.mem_zeroLocus_iff] at h2
    push_neg at h2
    obtain ⟨f, hf, hfx⟩ := h2
    rw [Scheme.mem_basicOpen X f x hxV] at hfx
    haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hgen : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hxV f) =
        X.germToFunctionField V f := by simp
    have hunit : IsUnit (X.germToFunctionField V f) := by
      rw [← hgen]
      exact hfx.map _
    have hmem := (hJ ⟨V, hV⟩ f).1 hf x hxV hunit.unit (by rw [IsUnit.unit_spec]; rfl)
    apply hnk
    rw [← inMultAt_one_iff_kltAt hp hn hM x]
    intro g hg E hE
    have h3 := hmem g hg E hE
    have h4 : E.ord hunit.unit = 0 :=
      DivOver.ord_eq_zero_of_unitAt hE _ ⟨_, hfx, by rw [IsUnit.unit_spec]; exact hgen⟩
    simpa [h4, DivOver.ord_one] using h3

end GlobalTheory.Discrepancy
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem exists_isMultIdeal_support_iff_not_kltAt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), IsLogMult p n Δ η m G → ∃ J : X.IdealSheafData, IsMultIdeal p n η m G J ∧ ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  intro hP k _ _ X _ _ _ p n hp hdim Δ η m G hL
  have hne : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    have hx : genericPoint X ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at hx
    exact hx
  obtain ⟨Y, hYi, s, hsd, K, B, hR, -⟩ :=
    LogResExist.exists_logRes hP k X p n hp hdim η m G hL.ne_zero ⊥ hne
  haveI := hYi
  haveI := hsd
  haveI := hR.smooth
  have hsm : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth (n := n) (f := s ≫ p)
  obtain ⟨-, -, hYn⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y (s ≫ p) hsm
  haveI := hYn
  obtain ⟨J, hJ⟩ := MultIdealExists.exists_isMultIdeal k X p n hp η m G Y s K B hL.ne_zero hL.pos hR
  exact ⟨J, hJ, mem_support_multIdeal_iff k X p n hp hdim Δ η m G Y s K B hL hR J hJ⟩

end GlobalTheory.Discrepancy
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem nadelVanishingPair_of_principalisation (hP : GlobalTheory.Published.Principalisation) :
    GlobalTheory.Published.NadelVanishingPair := by
  intro X _ _ _ p n hproj hdim N Δ m G r M₀ hN hΔ hm hlc hr hnef hbig hcurve
  letI := algebraΓOfHom p
  obtain ⟨η, hlm⟩ := hlc.exists_isLogMult hm
  obtain ⟨J, hJ, hsupp⟩ :=
    exists_isMultIdeal_support_iff_not_kltAt hP ℂ X p n hproj hdim Δ η m G hlm
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hproj
  have hM : M₀.IsLB := hnef.isLB
  have hG : (toLB G).IsLB := isLB_toLB G
  have hP1 : (lbPow N (m * r)).IsLB := isLB_lbPow hN _
  have hP2 : (lbPow (toLB G) r).IsLB := isLB_lbPow hG _
  have hP3 : (lbPow M₀ m).IsLB := isLB_lbPow hM _
  have hD2 : (dual (lbPow (toLB G) r)).IsLB := isLB_dual hP2
  have hD3 : (dual (lbPow M₀ m)).IsLB := isLB_dual hP3
  have hS : (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m))).IsLB := isLB_tens hD2 hD3
  have hTl : (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m)))).IsLB :=
    isLB_tens hP1 hS
  have hclsS : cls _ hS = cls _ hD2 + cls _ hD3 := cls_tens hD2 hD3 hS
  have hclsT : cls _ hTl = cls _ hP1 + cls _ hS := cls_tens hP1 hS hTl
  have hT : IsNef ℂ (tens (lbPow N (m * r)) (tens (dual (lbPow (toLB G) r)) (dual (lbPow M₀ m)))) := by
    refine ⟨hTl, fun Z hZ => ?_⟩
    have e1 := hZ.interNumRed_of_cls_eq_add hH hTl hP1 hS hclsT
    have e2 := hZ.interNumRed_of_cls_eq_add hH hS hD2 hD3 hclsS
    have e3 := hZ.interNumRed_dual (L := lbPow (toLB G) r) hH hP2
    have e4 := hZ.interNumRed_dual (L := lbPow M₀ m) hH hP3
    have e5 := hZ.interNumRed_lbPow hH hN (m * r)
    have e6 := hZ.interNumRed_lbPow hH hG r
    have e7 := hZ.interNumRed_lbPow hH hM m
    have hq := hcurve Z hZ
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    have hz : ((m : ℤ) * r) * interNumRed ℂ Z ![N] = r * interNumRed ℂ Z ![toLB G] + m * interNumRed ℂ Z ![M₀] := by
      have : ((m : ℚ) * r) * (interNumRed ℂ Z ![N] : ℚ) = r * (interNumRed ℂ Z ![toLB G] : ℚ) + m * (interNumRed ℂ Z ![M₀] : ℚ) := by
        rw [hq]
        field_simp
      exact_mod_cast this
    rw [e1, e2, e3, e4, e5, e6, e7]
    push_cast
    linarith
  have hcls : cls _ hT.isLB = (m * r) • cls N hN - r • toPic G - m • cls M₀ hM := by
    rw [hclsT, hclsS, cls_dual hP2 hD2, cls_dual hP3 hD3, cls_lbPow hN (m * r) hP1, cls_lbPow hG r hP2,
      cls_lbPow hM m hP3]
    have : cls (toLB G) hG = toPic G := rfl
    rw [this]
    abel
  exact ⟨J, hsupp, fun i hi =>
    GlobalTheory.nadelVanishing hP ℂ X p n hproj hdim Δ η m G hΔ.nonneg hlm N M₀ _ hN hM r hT hr hcls hnef hbig J hJ i hi⟩

end GlobalTheory.Discrepancy

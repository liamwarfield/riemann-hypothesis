module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SharedDedup_Exists_int_basis

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem de_mem {Ω : Type} [Field Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v) (x : Ω) :
    x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
  rw [placeJ, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

private theorem de_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {v : ℕ} [Fact v.Prime] {A : ValuationSubring Ω} {j : Ω →+* Om v} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (g : ↥(Dec (F := F) A)) (σ : GQ v) (hi : ∀ y, σ (j y) = j ((g : G F Ω) y)) :
    σ ∈ Iq v ↔ (g : G F Ω) ∈ Ine (F := F) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hnorm : ∀ y, ‖j y‖ < 1 ↔ A.valuation y < 1 := GlobalTheory.DecLocal.norm_lt_one_iff A j hj
  have hle : ∀ y, A.valuation y ≤ 1 ↔ ‖j y‖ ≤ 1 := fun y => by
    rw [A.valuation_le_one_iff y, hj]
  rw [(iqBasic v).2.2.1 σ]
  change _ ↔ (g : G F Ω) ∈ ValuationSubring.decompositionSubgroup F A ∧
    ∀ x, A.valuation x ≤ 1 → A.valuation ((g : G F Ω) x - x) < 1
  constructor
  · intro h
    refine ⟨g.2, fun x hx => ?_⟩
    rw [← hnorm, map_sub, ← hi]
    exact h (j x) ((hle x).mp hx)
  · rintro ⟨-, h⟩ y hy
    obtain ⟨x, hx⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt y one_pos
    rw [dist_eq_norm] at hx
    have hjx : ‖j x‖ ≤ 1 := by
      have hm := IsUltrametricDist.norm_add_le_max y (-(y - j x))
      rw [norm_neg, ← sub_eq_add_neg, sub_sub_cancel] at hm
      exact hm.trans (max_le hy hx.le)
    have h3 : ‖σ (j x) - j x‖ < 1 := by
      rw [hi, ← map_sub, hnorm]
      exact h x ((hle x).mpr hjx)
    have hdecomp : σ y - y = (σ (y - j x) - (y - j x)) + (σ (j x) - j x) := by
      rw [map_sub]
      ring
    have h1 : ‖σ (y - j x)‖ < 1 := by
      rw [GlobalTheory.PlaceBridge.norm_algEquiv]
      exact hx
    have h5 : ‖σ (y - j x) - (y - j x)‖ < 1 := by
      have hm := IsUltrametricDist.norm_add_le_max (σ (y - j x)) (-(y - j x))
      rw [norm_neg, ← sub_eq_add_neg] at hm
      exact lt_of_le_of_lt hm (max_lt h1 hx)
    rw [hdecomp]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h5 h3)

private theorem de_cyc {F Ω : Type} [Field F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosed Ω]
    {v : ℕ} [Fact v.Prime] {j : Ω →+* Om v} (l : ℕ) [Fact l.Prime]
    (g : G F Ω) (σ : GQ v) (hi : ∀ y, σ (j y) = j (g y)) :
    UpperTheory.V.Loc.cyc v l σ = cycZ F Ω l g := by
  have hjinj : Function.Injective j := j.injective
  simp only [UpperTheory.V.Loc.cyc, ReciprocityTheory.Gal.cycZ, MonoidHom.comp_apply]
  apply Units.ext
  apply (PadicInt.ext_of_toZModPow).mp
  intro n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one
  have h2 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  rw [show (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ = g ζ from rfl] at h1
  rw [show (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ) = σ (j ζ) from rfl] at h2
  rw [hi, h1, ← map_pow] at h2
  have h4 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hjinj h2)
  exact (ZMod.val_injective _ h4).symm

theorem UpperTheory.V.Loc.decEmb :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {v : ℕ} [Fact v.Prime], (∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)), IsPlaceOver A w → ((v : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ j : Ω →+* Om v, placeJ j = A) ∧ ∀ j : Ω →+* Om v, (∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver (placeJ j) w ∧ ((v : ℕ) : 𝓞 F) ∈ w.asIdeal) ∧ ∃ φ : ↥(Dec (F := F) (placeJ j)) →* GQ v, IsOpenEmbedding φ ∧ (∀ g y, φ g (j y) = j ((g : G F Ω) y)) ∧ (∀ σ : GQ v, σ ∈ φ.range ↔ ∀ x : F, σ (j (algebraMap F Ω x)) = j (algebraMap F Ω x)) ∧ (∀ g, φ g ∈ Iq v ↔ (g : G F Ω) ∈ Ine (F := F) (placeJ j)) ∧ (∀ (l : ℕ) [Fact l.Prime] g, UpperTheory.V.Loc.cyc v l (φ g) = cycZ F Ω l (g : G F Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 F), IsPlaceOver (placeJ j) w → φ.range.index = locDeg w := by
  intro F Ω _ _ _ _ _ _ v _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  refine ⟨?_, ?_⟩
  · intro A w hA hw
    obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := v) F Ω w A hw hA
    refine ⟨j, ?_⟩
    ext x
    rw [de_mem, hj]
  · intro j
    have hj : ∀ x, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := de_mem j
    refine ⟨?_, ?_⟩
    · have hlt : (placeJ j).valuation ((v : ℕ) : Ω) < 1 := by
        rw [← GlobalTheory.DecLocal.norm_lt_one_iff _ j hj, map_natCast]
        exact GlobalTheory.PlaceBridge.norm_l_lt_one
      obtain ⟨w, hw, hpo⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := F) (placeJ j) hlt
      exact ⟨w, hpo, hw⟩
    · let K : FinExt v := ⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x)),
        GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
      haveI : FiniteDimensional ℚ_[v] (K : IntermediateField ℚ_[v] (Om v)) := K.2
      have hK : (K : IntermediateField ℚ_[v] (Om v)) =
          IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x)) := rfl
      obtain ⟨e, hec, hesc, he⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K hK
      let φ : ↥(Dec (F := F) (placeJ j)) →* GQ v := (GK K).subtype.comp e.toMonoidHom
      have hφ : ∀ g, φ g = (e g : GQ v) := fun g => rfl
      have hrange : ∀ σ : GQ v, σ ∈ φ.range ↔ σ ∈ GK K := by
        intro σ
        constructor
        · rintro ⟨g, rfl⟩
          exact (e g).2
        · intro h
          exact ⟨e.symm ⟨σ, h⟩, by rw [hφ, MulEquiv.apply_symm_apply]⟩
      have hopen : IsOpen ((GK K : Subgroup (GQ v)) : Set (GQ v)) :=
        IntermediateField.fixingSubgroup_isOpen (K : IntermediateField ℚ_[v] (Om v))
      refine ⟨φ, ?_, fun g y => he g y, fun σ => by rw [hrange, GlobalTheory.PlaceBridge.mem_GK_iff (E := F) K hK],
        fun g => de_ine hj g (φ g) (he g), fun l _ g => de_cyc l (g : G F Ω) (φ g) (he g), fun w hw => ?_⟩
      · let h : ↥(Dec (F := F) (placeJ j)) ≃ₜ ↥(GK K) :=
          { e.toEquiv with continuous_toFun := hec, continuous_invFun := hesc }
        exact hopen.isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding
      · have hr : φ.range = GK K := by
          ext σ
          exact hrange σ
        rw [hr, ← GlobalTheory.DecLocal.finrank_closure_eq_locDeg v F Ω (placeJ j) j hj w hw,
          IntermediateField.finrank_eq_fixingSubgroup_index]
        rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem exists_int_basis {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V), ∀ g i j, ‖e.repr (ρ g (e j)) i‖ ≤ 1 := _root_.DedupShared.dedup_exists_int_basis_2 (l := l) (G := G) (V := V) ρ hρ


open GlobalTheory.UnramifiedRep GlobalTheory.UnramifiedCrys GlobalTheory.Cyc in
private theorem isCrys_of_inertia {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI)
    (K : FinExt l) (hχ : Continuous fun g => (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]))
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (hρ : ∀ x, Continuous fun g => ρ g x) (w : ℤ)
    (hI : ∀ g ∈ IK K, ∀ x, ρ g x = (((P.PD K).χ g ^ w : ℚ_[l]ˣ) : ℚ_[l]) • x) : IsCrys (P.PD K) ρ := by
  have := compactSpace_GK K
  let χ := (P.PD K).χ
  let ρ' : Representation ℚ_[l] ↥(GK K) V := twist (χ ^ (-w)) ρ
  have hρ' : ∀ g x, ρ' g x = ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • ρ g x := fun g x => rfl
  have hcont : ∀ x, Continuous fun g => ρ' g x := fun x => by
    simp only [hρ', Units.val_zpow_eq_zpow_val]
    exact (hχ.zpow₀ _ fun g => Or.inl (Units.ne_zero _)).smul (hρ x)
  have hI' : ∀ g ∈ IK K, ∀ x, ρ' g x = x := fun g hg x => by
    rw [hρ', hI g hg, smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_smul]
  obtain ⟨n, e, hint⟩ := exists_int_basis ρ' hcont
  obtain ⟨M, hM⟩ := exists_matrixHom ρ' e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hcont (e j))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI' g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      rw [hM, hM, h, map_one, Module.End.one_apply])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (ρ' g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  obtain ⟨u, hu⟩ := (P.PD K).t_unit
  have hact : ∀ g, (P.PD K).actB g ((u ^ (-w) : (P.R.B)ˣ) : P.R.B) =
      algebraMap ℚ_[l] P.R.B ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) * ((u ^ (-w) : (P.R.B)ˣ) : P.R.B) := fun g => by
    have h1 : Units.map ((P.PD K).actB g : P.R.B →* P.R.B) u =
        Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (χ g) * u := by
      ext
      change (P.PD K).actB g u = algebraMap ℚ_[l] P.R.B (χ g : ℚ_[l]ˣ) * u
      rw [hu, (P.PD K).t_act, Algebra.smul_def]
    have h2 := congrArg (fun x : (P.R.B)ˣ => ((x ^ (-w) : (P.R.B)ˣ) : P.R.B)) h1
    beta_reduce at h2
    rw [mul_zpow, ← map_zpow, ← map_zpow, Units.val_mul] at h2
    exact h2
  refine GlobalTheory.T.isCrys_of_split_alt (P.PD K) ρ e (((u ^ (-w) : (P.R.B)ˣ) : P.R.B) • AI.ιA.mapMatrix W) ?_ fun g => ?_
  · rw [Matrix.det_smul, ← RingHom.map_det]
    exact ((Units.isUnit _).pow _).mul (hW.map _)
  · conv_rhs => rw [← hB g]
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, map_mul, hact,
      hρ', map_smul, Finsupp.smul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem UpperTheory.V.Loc.crUnr :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Algebra ℤ_[l] A] [IsScalarTower ℤ_[l] ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → ∀ w : ℤ, (∀ g, φ g ∈ Iq l → ∀ x, ρ g x = ((cycA l l A (φ g) ^ w : Aˣ) : A) • x) → IsCr φ ρ := by
  intro l _ G _ _ _ φ hφ A _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ w hI
  obtain ⟨K, e, -, he, hφe, hr, -⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  obtain ⟨hc, -, hq⟩ := cycFacts l l
  have hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by
    rw [← hφe]
    simp
  let ρ' : Representation A ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have hχ : ∀ g : ↥(GK K), ((((PP l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) :=
    fun g => by rw [(PP l).PD_χ, hq]
  have h1 : Crys K ρ' := by
    refine isCrys_of_inertia (PP l) (AIP l) T K ?_ _ (fun x => ?_) w fun g hg x => ?_
    · simp only [hχ]
      have h0 : Continuous fun g : ↥(GK K) => ((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) :=
        Units.continuous_val.comp (hc.comp continuous_subtype_val)
      exact continuous_subtype_val.comp h0
    · exact hρ.comp (he.prodMk continuous_const)
    · change ρ (e.symm g) x = _
      rw [hI _ (by rw [hφ']; exact (memIK K g).1 hg), hφ']
      have h2 : cycA l l A g = Units.map (algebraMap ℚ_[l] A : ℚ_[l] →* A) (((PP l).PD K).χ g) := by
        ext
        change algebraMap ℤ_[l] A _ = algebraMap ℚ_[l] A _
        rw [hχ, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] A]
        rfl
      rw [h2, ← map_zpow]
      exact algebraMap_smul A _ x
  have h2 := (isCrIff K ρ').1.2 h1
  have h3 : Dcr φ (resCoef ℚ_[l] ρ) = Dcr (GK K).subtype (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    refine (e.symm.surjective.iInf_congr _ fun g => ?_).symm
    unfold actC
    rw [hφ']
    rfl
  unfold IsCr at h2 ⊢
  rw [h3, h2, hr, Subgroup.range_subtype]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
noncomputable section

namespace UpperTheory.V.Loc

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV IsLocalRing

def wtDer {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : X → Submodule O R) (x : R →ₐ[O] O)
    (E : Type) [Field E] [Algebra O E] (j : X) : Submodule E (R →ₗ[O] E) where
  carrier := {D | D ∈ PtDer ((Algebra.ofId O E).comp x) E ∧ HasWt 𝒜 j D}
  zero_mem' := ⟨zero_mem _, fun _ _ _ _ => rfl⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun i hi f hf => by
    rw [LinearMap.add_apply, ha.2 i hi f hf, hb.2 i hi f hf, add_zero]⟩
  smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun i hi f hf => by
    rw [LinearMap.smul_apply, ha.2 i hi f hf, smul_zero]⟩

def dimsL (w : ℤ × ℤ) : ℕ :=
  if w = wAl ∨ w = wBe ∨ w = wPs ∨ w = wTh ∨ w = 0 then 2 else if w ∈ wts then 1 else 0

def dimsP (w : ℤ × ℤ) : ℕ := if w = 0 then 2 else if w ∈ wts then 1 else 0

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {B : Type} [CommRing B] [Algebra c.O B]

def EqL (r : D.Gp l →* M4 B) : Prop :=
  (∀ g : D.Gp l, IsGSp (algebraMap c.O B (D.th g)) (r g)) ∧
    Ord ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O B (D.ps i g)) D.s0 r

def EqP (p : ℕ) (r : D.Gp p →* M4 B) : Prop :=
  (∀ g : D.Gp p, IsGSp (algebraMap c.O B (D.th g)) (r g)) ∧
    ∀ g : D.Gp p, (g : G ℚ Ω) ∈ D.Ip p ⊓ D.ψ.ker → r g = 1

structure IsContinuousLiftOfRZero [Algebra ℚ_[l] B] {E : Type} [CommRing E] [Algebra c.O E] (π : B →+* E) (v : ℕ)
    (r : D.Gp v →* M4 B) : Prop where
  red : mapRep π r = mapRep (algebraMap c.O E) (D.r0At v)
  cont : ∀ a b, QCont l fun g => r g a b

def IsFirstOrderDeformationOfRZero {E : Type} [CommRing E] [Algebra c.O E] (v : ℕ) (γ : D.Gp v → M4 E) (r' : D.Gp v →* M4 (DualNumber E)) :
    Prop :=
  ∀ g a b, r' g a b = ⟨algebraMap c.O E (D.r0At v g a b), (γ g * (D.r0At v g).map (algebraMap c.O E)) a b⟩

def FlagIn {H K : Type} [Group H] [CommRing K] (r : H →* M4 K) (h : (M4 K)ˣ) (κ : Fin 4 → H →* Kˣ) : Prop :=
  ∀ g, (∀ i j, j < i → ((h⁻¹ : (M4 K)ˣ) * r g * h : M4 K) i j = 0) ∧
    ∀ i, ((h⁻¹ : (M4 K)ˣ) * r g * h : M4 K) i i = (κ i g : K)

def PtOn {v : ℕ} (P : Cond c.O (D.rbarAt v)) {K : Type} [CommRing K] [Algebra c.O K] (r : D.Gp v →* M4 K) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O (D.rbarAt v) R) (y : R →ₐ[c.O] K),
    OnComp P (D.r0At v) ρ ∧ r = mapRep (y : R →+* K) ρ.hom

end UpperTheory.V.Loc
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section Generic

variable {G Q B : Type} [Group G] [Field Q] [AddCommGroup B] [Module Q B] (a : G → B →ₗ[Q] B)

private noncomputable def invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) :
    Submodule Q (V ⊗[Q] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g) (a g) - LinearMap.id)

private theorem mem_invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) (x : V ⊗[Q] B) :
    x ∈ invT a ρ ↔ ∀ g, AlgebraTensorModule.map (ρ g) (a g) x = x := by
  simp only [invT, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

private theorem rT_comm {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (y : V ⊗[Q] B) :
    f.rTensor B (AlgebraTensorModule.map (ρ g) (a g) y) =
      AlgebraTensorModule.map (ρ' g) (a g) (f.rTensor B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hf g]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private noncomputable def invMap {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : invT a ρ →ₗ[Q] invT a ρ' :=
  (f.rTensor B).restrict fun x hx => (mem_invT a ρ' _).2 fun g => by
    rw [← rT_comm a hf, (mem_invT a ρ _).1 hx]

private theorem of_exact {V₀ V V' : Type} [AddCommGroup V₀] [Module Q V₀] [AddCommGroup V] [Module Q V]
    [AddCommGroup V'] [Module Q V'] [FiniteDimensional Q V]
    {ρ₀ : Representation Q G V₀} {ρ : Representation Q G V} {ρ' : Representation Q G V'}
    {i : V₀ →ₗ[Q] V} {p : V →ₗ[Q] V'}
    (hi : ∀ g x, i (ρ₀ g x) = ρ g (i x)) (hp : ∀ g x, p (ρ g x) = ρ' g (p x))
    (h1 : Function.Injective i) (h2 : Function.Exact i p) (h3 : Function.Surjective p) (n : ℕ)
    [Module.Finite Q (invT a ρ)] [Module.Finite Q (invT a ρ')]
    (c₀ : finrank Q (invT a ρ₀) ≤ n * finrank Q V₀) (c' : finrank Q (invT a ρ') ≤ n * finrank Q V')
    (h : finrank Q (invT a ρ) = n * finrank Q V) :
    finrank Q (invT a ρ₀) = n * finrank Q V₀ ∧ finrank Q (invT a ρ') = n * finrank Q V' := by
  have hex : Function.Exact (i.rTensor B) (p.rTensor B) := rTensor_exact B h2 h3
  have hinj : Function.Injective (i.rTensor B) := Module.Flat.rTensor_preserves_injective_linearMap _ h1
  have e1 : Function.Injective (invMap a hi) := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have e2 : Function.Exact (invMap a hi) (invMap a hp) := by
    refine fun x => ⟨fun h => ?_, ?_⟩
    · obtain ⟨y, hy⟩ := (hex x).1 (congrArg Subtype.val h)
      refine ⟨⟨y, (mem_invT a ρ₀ y).2 fun g => hinj ?_⟩, Subtype.ext hy⟩
      rw [rT_comm a hi, hy]
      exact (mem_invT a ρ _).1 x.2 g
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((hex _).2 ⟨_, rfl⟩)
  have h4 := (invMap a hp).finrank_range_add_finrank_ker
  rw [e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1] at h4
  have h5 := p.finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
  have h6 := (LinearMap.range (invMap a hp)).finrank_le
  rw [← h5, mul_add] at h
  exact ⟨by omega, by omega⟩

private theorem sub_quot (n : ℕ)
    (hb : ∀ (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W),
      Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ n * finrank Q W)
    {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    [FiniteDimensional Q V] [FiniteDimensional Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    (Function.Injective f → finrank Q (invT a ρ') = n * finrank Q V' → finrank Q (invT a ρ) = n * finrank Q V) ∧
    (Function.Surjective f → finrank Q (invT a ρ) = n * finrank Q V →
      finrank Q (invT a ρ') = n * finrank Q V') := by
  have := (hb V ρ).1
  have := (hb V' ρ').1
  refine ⟨fun hi h => ?_, fun hs h => ?_⟩
  · have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ' g) := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hf g v⟩
    have := (hb _ (ρ'.quotient (LinearMap.range f) hst)).1
    exact (of_exact a (ρ' := ρ'.quotient (LinearMap.range f) hst) hf (fun g v => rfl) hi
      (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective n (hb V ρ).2 (hb _ _).2 h).1
  · have hst : ∀ g, LinearMap.ker f ≤ (LinearMap.ker f).comap (ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]
    exact (of_exact a (ρ₀ := ρ.subrepresentation (LinearMap.ker f) hst) (fun g v => rfl) hf
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) hs n (hb _ _).2 (hb V' ρ').2 h).2

end Generic

private theorem bound {G H Q K B : Type} [Group G] [Group H] [Field Q] [Field K] [Algebra Q K] [CommRing B]
    [IsDomain B] [Algebra Q B] [Algebra K B] [IsScalarTower Q K B] [FiniteDimensional Q K]
    (e : G ≃* H) (act : H →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (a : G → B →ₗ[Q] B) (ha : ∀ g b, a g b = act (e g) b)
    (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W) :
    Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ finrank Q K * finrank Q W := by
  have h := GlobalTheory.Per.FontaineBound.finite_finrank_le_base (Qp := Q) (act.comp e.toMonoidHom)
    (fun b b' hb h => hreg b b' hb fun g => by simpa using h (e.symm g)) σ
  have : a = fun g => ((act.comp e.toMonoidHom g).toAlgHom.toLinearMap).restrictScalars Q :=
    funext fun g => LinearMap.ext fun b => ha g b
  subst this
  exact h

theorem UpperTheory.V.Loc.isCrys_isDR_sub_quot :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {A' : Type} [CommRing A'] [Algebra ℚ_[l] A'] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A G V) (ρ' : Representation A' G V'), ContAction ρ → ContAction ρ' → ∀ f : V →ₗ[ℚ_[l]] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → (IsCr φ ρ' → IsCr φ ρ) ∧ (IsDr φ ρ' → IsDr φ ρ)) ∧ (Function.Surjective f → (IsCr φ ρ → IsCr φ ρ') ∧ (IsDr φ ρ → IsDr φ ρ')) := by
  intro l _ G _ _ _ φ hφ A _ _ A' _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' _ _ f hf
  obtain ⟨K, e, -, -, he, -, hK, hK0⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  have hF := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have := GlobalTheory.Per.FontaineBound.isDomain_cris (PD := (PP l).PD K) hF
  have := hF.isDomain
  have := ((PP l).PD K).finK₀
  have := K.2
  have hφe : ∀ g, φ g = (e g : GQ l) := fun g => by rw [← he]; rfl
  have hc := sub_quot (fun g => ((PP l).actQ (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actB (fun b b' hb h =>
      GlobalTheory.Per.FracInv.tied_frac_invariant l (PP l) (AIP l) T K b' b hb fun g hg => by
        have h1 := h ⟨g, hg⟩
        rw [(PP l).PD_actB, (PP l).PD_actB] at h1
        rw [mul_comm, h1, mul_comm]) _ fun g b => by rw [(PP l).PD_actB, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  have hd := sub_quot (fun g => ((PP l).actQdR (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actdR (GlobalTheory.Per.FontaineBound.frac_dR ((PP l).PD K) hF) _
      fun g b => by rw [(PP l).PD_actdR, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  unfold IsCr IsDr
  rw [hK, hK0]
  exact ⟨fun h => ⟨hc.1 h, hd.1 h⟩, fun h => ⟨hc.2 h, hd.2 h⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.AdmRes

variable {l : ℕ} [Fact l.Prime]

section Transport

variable {G G' A A' V : Type} [Group G] [Group G'] [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A']
  [AddCommGroup V] [Module A V] [Module A' V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [IsScalarTower ℚ_[l] A' V]
  {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A' G' V}

private theorem transport (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : (IsCr φ ρ ↔ IsCr φ' ρ') ∧ (IsDr φ ρ ↔ IsDr φ' ρ') := by
  have hr : φ.range = φ'.range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, h1 g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, (h1 g).symm⟩
  have hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g := fun g => LinearMap.ext fun x => h2 g x
  have hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    rw [he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actC
    rw [hρ, h1]
  have hd : Ddr φ (resCoef ℚ_[l] ρ) = Ddr φ' (resCoef ℚ_[l] ρ') := by
    unfold Ddr
    rw [he.iInf_comp (fun g => LinearMap.ker (actD φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actD
    rw [hρ, h1]
  unfold IsCr IsDr
  rw [hr, hc, hd]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

private theorem field_case (K K' LL : FinExt l) (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) := by
  have := LL.2
  have : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 V
  obtain ⟨T⟩ := tiedP l
  have hres := GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K K' LL h V ρ
  rw [(isCrIff K ρ).1, (isCrIff K ρ).2, (isCrIff K' _).1, (isCrIff K' _).2, (isCrField K ρ).1, (isCrField K ρ).2.1,
    (isCrField K' _).1, (isCrField K' _).2.1]
  exact ⟨fun hc => (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (PP l) (AIP l) T K LL V ρ hc).1, hres.1, hres.2⟩

private theorem gal_case (K K' : FinExt l) (h : K.1 ≤ K'.1) {A V : Type} [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    (ρ : Representation A ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) := by
  let β : ↥(botExt l).1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI : Module ↥(botExt l).1 V := Module.compHom V (β : ↥(botExt l).1 →+* ℚ_[l])
  have hs : ∀ (c : ↥(botExt l).1) (x : V), c • x = β c • x := fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥(botExt l).1 V := ⟨fun a c x => by
    rw [hs, hs, Algebra.smul_def, map_mul, β.commutes, mul_smul]; rfl⟩
  haveI : ContinuousConstSMul ↥(botExt l).1 V := ⟨fun c => continuous_const_smul (β c)⟩
  let ρ' : Representation ↥(botExt l).1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := map_add _
          map_smul' := fun c x => by
            rw [RingHom.id_apply, hs, hs]
            exact LinearMap.map_smul_of_tower _ _ _ }
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  have t1 := transport (φ := (GK K).subtype) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρ') id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  have t2 := transport (φ := (GK K').subtype) (ρ := (ρ.comp (incl h) : Representation A ↥(GK K') V))
    (φ' := (GK K').subtype) (ρ' := (ρ'.comp (incl h) : Representation ↥(botExt l).1 ↥(GK K') V)) id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  rw [t1.1, t1.2, t2.1, t2.2]
  exact field_case K K' (botExt l) h ρ'

end UpperTheory.V.Loc.AdmRes

open UpperTheory.V.Loc.AdmRes in
theorem UpperTheory.V.Loc.isCrys_isDR_restrict_openSubgroup :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → (IsCr φ ρ → IsDr φ ρ) ∧ ∀ H : Subgroup G, IsOpen (H : Set G) → (IsCr φ ρ → CrOn φ ρ H) ∧ (IsDr φ ρ ↔ IsDr (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ _
  obtain ⟨K, e, -, -, he, hK, -, -⟩ := openField φ hφ
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  let ρK : Representation A ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have t1 := transport (φ := φ) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρK) e e.surjective he'
    (fun g x => by simp [ρK])
  refine ⟨?_, fun H hH => ?_⟩
  · rw [t1.1, t1.2]
    exact (gal_case K K le_rfl ρK).1
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  obtain ⟨K', e', -, -, hf, hK', -, -⟩ := openField (φ.comp H.subtype) hφH
  have hf' : ∀ g, ((e' g : ↥(GK K')) : GQ l) = φ g := fun g => DFunLike.congr_fun hf g
  have hle : GK K' ≤ GK K := by
    rw [← hK, ← hK']
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h : K.1 ≤ K'.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup K'.1]
    exact IntermediateField.fixedField_le hle
  have t2 := transport (φ := φ.comp H.subtype) (ρ := (ρ.comp H.subtype : Representation A H V))
    (φ' := (GK K').subtype) (ρ' := (ρK.comp (incl h) : Representation A ↥(GK K') V)) e' e'.surjective hf'
    (fun g x => by
      have : incl h (e' g) = e g := Subtype.ext ((hf' g).trans (he' g).symm)
      simp [ρK, this])
  unfold CrOn
  rw [t1.1, t1.2, t2.1, t2.2]
  exact (gal_case K K' h ρK).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IofAdd
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk7.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qk7.iof_add :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] {x y : UpperTheory.Reformulated.B.Qk7.Om v}, ‖x‖ < (1 : ℝ) → ‖y‖ < (1 : ℝ) → ‖x + y‖ < (1 : ℝ) := by
  intro v inst x y hx hy
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
end

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v)

omit [CharZero Ω] in
private theorem iof_mem (x : Ω) : x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := Examples₂.LB.mem_placeJ j x

omit [CharZero Ω] in
private theorem iof_lt (x : Ω) : (placeJ j).valuation x < 1 ↔ ‖j x‖ < 1 :=
  Examples₂.LB.val_lt_one_iff (iof_mem j) x

omit [CharZero Ω] in
private theorem iof_le (x : Ω) : (placeJ j).valuation x ≤ 1 ↔ ‖j x‖ ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, iof_mem]

private theorem iof_add {x y : Om v} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.Qk7.iof_add hx hy

private theorem iof_pow {x y : Om v} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [e]
    refine iof_add ?_ ?_
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt ih
    · rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)).trans_lt h

variable [IsAlgClosure ℚ Ω]

private theorem iof_dense : DenseRange j :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  Examples₂.LB.denseRange_emb v j

private theorem iof_pw (σ : GQ v) (n : ℕ) :
    (∀ x : Om v, ‖x‖ ≤ 1 → ‖σ x - x ^ n‖ < 1) ↔
      ∀ y : Ω, (placeJ j).valuation y ≤ 1 → (placeJ j).valuation (iota j σ y - y ^ n) < 1 := by
  simp only [iof_le, iof_lt, map_sub, map_pow, iota_spec]
  refine ⟨fun h y hy => h _ hy, fun h x hx => ?_⟩
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1 (iof_dense j) x 1 one_pos
  rw [dist_eq_norm] at hy
  have hy' : ‖j y - x‖ < 1 := by rwa [norm_sub_rev]
  have hy1 : ‖j y‖ ≤ 1 := by
    have e : j y = (j y - x) + x := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy'.le hx)
  have e : σ x - x ^ n = σ (x - j y) + ((σ (j y) - j y ^ n) + (j y ^ n - x ^ n)) := by
    rw [map_sub]; ring
  rw [e]
  exact iof_add (by rwa [Examples₂.LB.norm_aut]) (iof_add (h y hy1) (iof_pow hy1 hx hy' n))

private theorem iof_dec (σ : GQ v) : iota j σ ∈ Dec (F := ℚ) (placeJ j) := by
  rw [mem_Dec]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← map_inv, iof_mem, iof_mem,
    iota_spec, Examples₂.LB.norm_aut]

private theorem iof_range : (iota j).range = Dec (F := ℚ) (placeJ j) := by
  ext g
  constructor
  · rintro ⟨σ, rfl⟩
    exact iof_dec j σ
  · intro hg
    obtain ⟨σ, hσ⟩ := Examples₂.LB.exists_ext (E := ℚ) (iof_mem j) g hg
    exact ⟨σ, AlgEquiv.ext fun x => j.injective (by rw [iota_spec, hσ])⟩

private theorem iof_inj : Function.Injective (iota j) := by
  intro σ τ h
  refine AlgEquiv.ext fun y => ?_
  have e : σ ∘ j = τ ∘ j := funext fun x => by
    show σ (j x) = τ (j x)
    rw [← iota_spec, ← iota_spec, h]
  exact congrFun ((iof_dense j).equalizer (Examples₂.LB.continuous_aut _) (Examples₂.LB.continuous_aut _) e) y

private theorem iof_cont : Continuous (iota j) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨M, hM, hMU⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω U).mp hU
  let b := Module.finBasis ℚ M
  let N : IntermediateField ℚ_[v] (Om v) :=
    IntermediateField.adjoin ℚ_[v] (Set.range fun i => j (b i : Ω))
  have hN : FiniteDimensional ℚ_[v] N :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((IntermediateField.fixingSubgroup_isOpen N).mem_nhds
    (show (1 : GQ v) ∈ N.fixingSubgroup from one_mem _)) fun σ hσ => hMU ?_
  have hb : ∀ i, iota j σ (b i : Ω) = (b i : Ω) := fun i => j.injective (by
    rw [iota_spec]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩))
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have e : (iota j σ).toLinearMap ∘ₗ M.val.toLinearMap = M.val.toLinearMap := b.ext hb
  exact LinearMap.congr_fun e ⟨x, hx⟩

private theorem iof_ine (σ : GQ v) : iota j σ ∈ Ine (F := ℚ) (placeJ j) ↔ σ ∈ Iq v := by
  have h := iof_pw j σ 1
  simp only [pow_one] at h
  rw [(iqBasic v).2.2.1 σ, h]
  exact ⟨fun hg => hg.2, fun hg => ⟨iof_dec j σ, hg⟩⟩

private theorem iof_cyc (l : ℕ) [Fact l.Prime] (σ : GQ v) :
    cycZ ℚ Ω l (iota j σ) = UpperTheory.V.Loc.cyc v l σ := by
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.1 fun m => ?_)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have hζ' := hζ.map_of_injective j.injective
  have ha : iota j σ ζ = ζ ^ (((cycZ ℚ Ω l (iota j σ) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω (iota j σ)) ζ hζ.pow_eq_one
  have hb : σ (j ζ) = j ζ ^ (((UpperTheory.V.Loc.cyc v l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) σ) _ hζ'.pow_eq_one
  rw [← iota_spec, ha, map_pow] at hb
  exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)

omit [IsAlgClosure ℚ Ω] in
private theorem iof_place (w : HeightOneSpectrum (𝓞 ℚ)) :
    IsPlaceOver (placeJ j) w ↔ ((v : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  have h0 : (placeJ j).valuation ((v : ℕ) : Ω) < 1 := by
    rw [iof_lt, map_natCast]
    have h1 : ‖((v : ℕ) : PadicAlgCl v)‖ = ‖((v : ℕ) : ℚ_[v])‖ := by
      rw [← PadicAlgCl.norm_extends, map_natCast]
    rw [h1]
    exact Padic.norm_p_lt_one
  constructor
  · intro h
    refine (h _).1 ?_
    simpa using h0
  · intro h
    have e : Examples₂.LB.vQ v = w := HeightOneSpectrum.ext
      ((Examples₂.LB.vQ v).isMaximal.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h))
    rw [← e]
    exact Examples₂.LB.isPlaceOver_vQ _ h0

end SlopeTestRemainingChoices

theorem UpperTheory.V.Loc.iotaFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v), IsEmbedding (iota j) ∧ (iota j).range = Dec (F := ℚ) (placeJ j) ∧ (Ine (F := ℚ) (placeJ j)).comap (iota j) = Iq v ∧ (Iq v).map (iota j) = Ine (F := ℚ) (placeJ j) ∧ (∀ (l : ℕ) [Fact l.Prime], (cycZ ℚ Ω l).comp (iota j) = UpperTheory.V.Loc.cyc v l) ∧ (∀ w : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver (placeJ j) w ↔ ((v : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) ∧ ∀ σ : GQ v, UpperTheory.V.Loc.IsFrob σ ↔ Formalism.ConjugateSelfDual.IsFrob (F := ℚ) (placeJ j) v (iota j σ) := by
  intro Ω _ _ _ v _ j
  haveI : IsGalois ℚ_[v] (Om v) := {}
  refine ⟨((iof_cont j).isClosedEmbedding (iof_inj j)).isEmbedding, iof_range j, Subgroup.ext (iof_ine j), ?_,
    fun l _ => MonoidHom.ext (iof_cyc j l), iof_place j, fun σ => ?_⟩
  · ext g
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (iof_ine j σ).2 hσ
    · intro hg
      have h1 : g ∈ (iota j).range := by
        rw [iof_range]
        exact hg.1
      obtain ⟨σ, rfl⟩ := h1
      exact ⟨σ, (iof_ine j σ).1 hg, rfl⟩
  · exact (iof_pw j σ v).trans ⟨fun hg => ⟨iof_dec j σ, hg⟩, fun hg => hg.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem UpperTheory.V.Loc.adicCont_zpow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R)
    (Ψ : Γ → Rˣ) (h : AdicCont I fun g => (Ψ g : R)) (j : ℤ) : AdicCont I fun g => ((Ψ g ^ j : Rˣ) : R) := by
  intro N
  have h1 : IsLocallyConstant (fun g => Units.map (Ideal.Quotient.mk (I ^ N) : R →+* R ⧸ I ^ N).toMonoidHom (Ψ g)) :=
    IsLocallyConstant.desc _ (fun u : (R ⧸ I ^ N)ˣ => (u : R ⧸ I ^ N)) (by simpa [Function.comp_def] using h N)
      (fun a b hab => Units.ext hab)
  have h2 := h1.comp (fun u => ((u ^ j : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N))
  convert h2 using 1
  ext g
  change ((Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (Ψ g ^ j) : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N) = _
  rw [map_zpow]
  rfl

theorem UpperTheory.V.Loc.univEx :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)), ∃! x, IsBase D.η D.Ψ U.r.hom x := by
  intro l _ O _ _ _ _ _ _ _ D U
  have hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((D.Ψ g ^ j : Oˣ) : O) :=
    fun j => adicCont_zpow _ _ D.Ψ_cont j
  obtain ⟨f, hf, hu⟩ := (U.rep O).2 (baseLift O D.η D.Ψ hΨ) trivial
  refine ⟨f, congrArg GLift.hom hf, fun y hy => hu y (GLift.ext hy)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.z1fCoef :
    ∀ {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l) {A A' V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A'] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A H V) (ρ' : Representation A' H V') (f : V →ₗ[ℚ_[l]] V'), Continuous f → (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c ∈ finiteCocycles φ ρ, (fun g => f (c g)) ∈ finiteCocycles φ ρ' := by
  intro l _ H _ _ φ A A' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' f hfc hf c hc
  obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
  refine ⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
  · simp only [hcc g h, map_add (f := _), hf]
  · have key : ∀ y : TensorProduct ℚ_[l] V (Bcr l), LinearMap.rTensor (Bcr l) f (actC φ ρ g y) =
        actC φ ρ' g (LinearMap.rTensor (Bcr l) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [actC, hf]
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PhiCond
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.phiCond :
    LocalPublishedTheorems → ∀ (v l : ℕ) [Fact v.Prime] [Fact l.Prime] (H : Subgroup (GQ v)), IsOpen (H : Set (GQ v)) → Finite {f : H →* Multiplicative (ZMod l) // IsOpen (f.ker : Set H)} := by
  intro hP v l _ _ H hH
  letI : Algebra ℤ_[l] (ZMod l) := (PadicInt.toZMod (p := l)).toAlgebra
  letI : TopologicalSpace (ZMod l) := ⊥
  haveI : DiscreteTopology (ZMod l) := ⟨rfl⟩
  let ρ : Representation (ZMod l) H (ZMod l) := 1
  have hρ : ContAction ρ := continuous_snd
  have hfin := (tateFin hP (v := v) (l := l) H.subtype hH.isOpenEmbedding_subtypeVal (ZMod l) (ZMod l) ρ hρ).1
  haveI : Finite (H1 ρ) := Module.finite_of_finite (ZMod l)
  have hc : ∀ f : {f : H →* Multiplicative (ZMod l) // IsOpen (f.ker : Set H)},
      (fun g => Multiplicative.toAdd (f.1 g)) ∈ Z1 ρ := by
    intro f
    refine ⟨?_, fun g h => ?_⟩
    · refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)
      refine ⟨(fun x => g⁻¹ * x) ⁻¹' (f.1.ker : Set H), f.2.preimage (by fun_prop), by simp, fun x hx => ?_⟩
      have : f.1 (g⁻¹ * x) = 1 := hx
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      rw [this]
    · simp [ρ]
  refine Finite.of_injective (fun f => (Submodule.Quotient.mk ⟨_, hc f⟩ : H1 ρ)) fun f f' hff => ?_
  have h1 := (Submodule.Quotient.eq ((ReciprocityTheory.Gal.B1 ρ).comap (Z1 ρ).subtype)).1 hff
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 (Submodule.mem_comap.1 h1)
  refine Subtype.ext (MonoidHom.ext fun g => Multiplicative.toAdd.injective ?_)
  have := hm g
  simpa [ρ, sub_eq_zero] using this
end

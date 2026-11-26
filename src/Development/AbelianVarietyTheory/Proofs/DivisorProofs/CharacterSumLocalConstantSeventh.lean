module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFrLifts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSeventh
noncomputable section

namespace GlobalTheory.ColNorms.DatOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

section Generic

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem mem_lamY_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (v : Sp E (n + c)) :
    v ∈ LocE.lamY P q n c ex ↔ ∀ l : Fin (n + c), Formalism.L2.Col.IntAt P (((q : E) ^ LocE.scE n ex l.1)⁻¹ * v l) := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap]
  exact mem_localization_standardLattice P _

theorem proj_mem {P : HeightOneSpectrum (𝓞 E)} {q n c : ℕ} {ex : ℕ → ℕ} {v : Sp E (n + c)} (hv : v ∈ LocE.lamY P q n c ex) :
    LinearMap.funLeft E E (Fin.castAdd c) v ∈ stdAt E n P := by
  refine (mem_localization_standardLattice P _).2 fun i => ?_
  have h := (mem_lamY_iff P q n c ex v).1 hv (Fin.castAdd c i)
  simpa [LocE.scE, LinearMap.funLeft_apply] using h

theorem proj_inX {n c : ℕ} (y : Sp E n) : LinearMap.funLeft E E (Fin.castAdd c) (Loc.inX E n c y) = y := by
  funext i
  simp [LinearMap.funLeft_apply, Loc.inX]

theorem inX_mem_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (y : Sp E n) :
    Loc.inX E n c y ∈ LocE.lamY P q n c ex ↔ y ∈ stdAt E n P := by
  constructor
  · intro h
    simpa [proj_inX] using proj_mem h
  · intro h
    refine (mem_lamY_iff P q n c ex _).2 fun l => ?_
    by_cases hl : l.1 < n
    · have := (mem_localization_standardLattice P _).1 h ⟨l.1, hl⟩
      simpa [LocE.scE, Loc.inX, hl] using this
    · have := Formalism.L2.Col.IntAt.coe P (0 : 𝓞 E)
      simpa [Loc.inX, hl] using this

theorem joinCol_inX {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (y : Sp E n') :
    (joinCol x₀ y' : HomE E (n' + c') (n + c)) (Loc.inX E n' c' y) = Loc.inX E n c (x₀ y) := by
  have h0 : atNL E (n' + c') n' (Loc.inX E n' c' y) = 0 := by
    unfold atNL
    split_ifs with h
    · simp [Loc.inX]
    · rfl
  simp [joinCol, proj_inX, h0]

theorem joinCol_add {n' c' n c : ℕ} (x₀ z : HomE E n' n) (t : E) (y' : Sp E n) :
    (joinCol (x₀ + t • z) y' : HomE E (n' + c') (n + c)) =
      joinCol x₀ y' + t • (Loc.inX E n c ∘ₗ z ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) := by
  refine LinearMap.ext fun v => ?_
  simp only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul]
  abel

theorem locSmall_joinCol {P : HeightOneSpectrum (𝓞 E)} {q n' c' n c : ℕ} {ex' ex : ℕ → ℕ} {Φ : HomE E (n' + c') (n + c) → K} {β : ℝ}
    (h : LocSmall q (LocE.lamY P q n' c' ex') (LocE.lamY P q n c ex) Φ β) (y' : Sp E n) :
    LocSmall q (stdAt E n' P) (stdAt E n P) (fun x₀ => Φ (joinCol x₀ y')) β := by
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => h.2.2 σ _⟩
  · have := h.1 _ hx _ ((inX_mem_iff P q n' c' ex' y).2 hy)
    rw [joinCol_inX] at this
    exact (inX_mem_iff P q n c ex _).1 this
  · show Φ (joinCol (x + (q : E) • z) y') = Φ (joinCol x y')
    rw [joinCol_add]
    exact h.2.1 _ _ fun v hv => (inX_mem_iff P q n c ex _).2 (hz _ (proj_mem hv))

theorem smallDatum_of_frames {a b : ℕ} {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} [DecidableEq (HeightOneSpectrum (𝓞 E))]
    (d : Deco E a ST SG) (d' : DecoSet (E := E) (n := b) (ST := ST) (SG := SG'))
    (f : Frs E a SB) (f' : Frs E b SB) (hf : ∀ (P : SB) x, f P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1)
    (hf' : ∀ (P : SB) x, f' P x ∈ d'.1.at P.1 ↔ x ∈ stdAt E b P.1) (c : ℕ) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (hT : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (Ψ : SB → HomE E a b → K) (β : SB → ℝ)
    (hΨ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Ψ P) (β P)) :
    SmallDatum (ST ∪ SB) d.N d'.1.N c (fun x => phiT K d d'.1 x * ∏ P : SB, Ψ P (inFr (f P) (f' P) x)) (∏ P, β P) := by
  refine ⟨fun x hx P hP y hy => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rcases Finset.mem_union.1 hP with hP | hP
    · unfold phiT at h1
      split_ifs at h1 with h
      · exact (h ⟨P, hP⟩ y hy).1
      · exact absurd rfl h1
    · have h3 := Finset.prod_ne_zero_iff.1 h2 ⟨P, hP⟩ (Finset.mem_univ _)
      have h4 : (f ⟨P, hP⟩).symm y ∈ stdAt E a P := (hf ⟨P, hP⟩ _).1 (by simpa using hy)
      have h5 := (hf' ⟨P, hP⟩ _).2 ((hΨ ⟨P, hP⟩).1 _ h3 _ h4)
      simpa [inFr] using h5
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    have hz' : ∀ P ∈ ST ∪ SB, ∀ y ∈ d.at P, z y ∈ d'.1.at P := hz
    have e0 : (((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z) = (c : 𝓞 E) • z := rfl
    rw [e0]
    show phiT K d d'.1 _ * _ = phiT K d d'.1 _ * _
    congr 1
    · unfold phiT
      classical
      refine @if_congr _ _ _ (_) (_) _ _ _ _ (forall_congr' fun P => forall_congr' fun y => forall_congr' fun hy => ?_) rfl rfl
      have hzy : z y ∈ d'.1.at P.1 := hz' P.1 (Finset.mem_union_left _ P.2) y hy
      have hc : (c : 𝓞 E) • z y ∈ d'.1.at P.1 := Submodule.smul_mem _ _ hzy
      have e : (x + (c : 𝓞 E) • z) y = x y + (c : 𝓞 E) • z y := rfl
      rw [e, Submodule.add_mem_iff_left _ hc]
      refine and_congr_right fun hx => ?_
      rw [d'.2.f_add P _ hx _ hc, d'.2.f_smul P _ _ hzy, Ideal.Quotient.eq_zero_iff_mem.2 (hT P.1 P.2), zero_mul, add_zero]
    · refine Finset.prod_congr rfl fun P _ => ?_
      obtain ⟨k, hk⟩ := hq P
      have e : inFr (f P) (f' P) (x + (c : 𝓞 E) • z) =
          inFr (f P) (f' P) x + (q P : E) • inFr (f P) (f' P) (k • z) := by
        refine LinearMap.ext fun v => ?_
        have : (c : 𝓞 E) • z = (q P : E) • (k • z) := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hk, mul_smul]
        rw [this]
        simp [inFr]
      rw [e]
      refine (hΨ P).2.1 _ _ fun v hv => (hf' P _).1 ?_
      have := nsmul_mem (hz' P.1 (Finset.mem_union_right _ P.2) _ ((hf P v).2 hv)) k
      simpa [inFr] using this
  · show ‖σ (phiT K d d'.1 x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ‖σ (phiT K d d'.1 x)‖ ≤ 1 := by
      unfold phiT
      split_ifs <;> simp
    have h2 : ∏ P : SB, ‖σ (Ψ P (inFr (f P) (f' P) x))‖ ≤ ∏ P, β P :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun P _ => (hΨ P).2.2 σ _
    calc _ ≤ 1 * ∏ P, β P := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = _ := one_mul _

end Generic

end GlobalTheory.ColNorms.DatOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingStalk
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve (scheme toSpec chartZ)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

theorem valuationRing_stalk {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp K)
    [hf : SmoothOfRelativeDimension 1 f] (x : X) : ValuationRing (X.presheaf.stalk x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have h : Order.coheight x ≤ 1 := by simpa using GlobalTheory.AffineCover.coheight_le_of_smooth f hf x
  rcases h.eq_or_lt with h | h
  · have := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk h
    infer_instance
  · have h0 : Order.coheight x = 0 := by simpa using h
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h0.le
    letI := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    exact ValuationRing.of_field _

end GlobalTheory.ProjHol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedOfLocally
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeISupOfUniformisationParametersCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeISupOfUniformisationParametersCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem le_iSup_of_pre_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (K : Type) (W : K → A.left.Opens), (∀ z ∈ pre u.ex U, ∃ i, z ∈ pre u.ex (W i)) → U ≤ ⨆ i, W i := by
  intro A _ g L u hA U K W h x hx
  obtain ⟨-, -, -, -, hinf, hmono, hsup, -, -, -, hbasic, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
  have hV' : IsAffineOpen V := hV
  let p : Ideal Γ(A.left, V) :=
    (IsLocalRing.maximalIdeal (A.left.presheaf.stalk x)).comap (A.left.presheaf.germ V x hxV).hom
  have hp : p ≠ ⊤ := Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp
  obtain ⟨z, hzV, hz⟩ := GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint A g L u hA V hV' m hm
  obtain ⟨i, hi⟩ := h z (hmono U V hVU hzV)
  have hzi : z ∈ pre u.ex (W i ⊓ V) := by rw [hinf]; exact ⟨hi, hzV⟩
  have hle : W i ⊓ V ≤ ⨆ b : {b : Γ(A.left, V) // A.left.basicOpen b ≤ W i}, A.left.basicOpen b.1 := by
    intro y hy
    obtain ⟨f, hf, hyf⟩ := hV'.exists_basicOpen_le (V := W i) ⟨y, hy.1⟩ hy.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hyf⟩
  obtain ⟨⟨b, hb⟩, hzb⟩ := (hsup _ _ z).mp (hmono _ _ hle hzi)
  have hbm : b ∉ m := fun hh ↦ (hbasic V b z).mp hzb ((hz b).mp hh)
  have hxb : x ∈ A.left.basicOpen b := by
    rw [Scheme.mem_basicOpen _ b x hxV]
    by_contra hn
    exact hbm (hpm (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn)))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hb hxb⟩

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeISupOfUniformisationParametersCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_iSup_of_uniformisationParameters_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (K : Type) (W : K → A.left.Opens), (∀ z ∈ pre u.ex U, ∃ i, z ∈ pre u.ex (W i)) → U ≤ ⨆ i, W i := by
  first | exact @GlobalTheory.CechPer.le_iSup_of_pre_cover | exact GlobalTheory.CechPer.le_iSup_of_pre_cover | (intros; apply GlobalTheory.CechPer.le_iSup_of_pre_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedOfLocally
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_locally : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (k : (Fin g → ℂ) → ℂ), (∀ z ∈ pre u.ex U, ∃ W : A.left.Opens, W ≤ U ∧ z ∈ pre u.ex W ∧ IsReg u.ex W k) → IsReg u.ex U k := by
  intro A _ g L u hA U k h
  choose! W hWU hzW hreg using h
  let K : Type := {z // z ∈ pre u.ex U}
  let V : K → A.left.Opens := fun z => W z.1
  have hVU : ∀ i : K, V i ≤ U := fun i => hWU i.1 i.2
  have hb : ∀ i : K, ∃ b : Γ(A.left, V i), ∀ z ∈ pre u.ex (V i), k z = val u.ex (V i) b z := fun i => hreg i.1 i.2
  choose b hb using hb
  have hcov : U ≤ ⨆ i, V i := GlobalTheory.T.le_iSup_of_uniformisationParameters_cover A g L u hA U K V fun z hz => ⟨⟨z, hz⟩, hzW z hz⟩
  have hcompat : TopCat.Presheaf.IsCompatible A.left.sheaf.1 V b := by
    intro i j
    rw [← sub_eq_zero]
    refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA (V i ⊓ V j) _ fun z hz => ?_
    have hz' := (GlobalTheory.top_le_preimage_inf (u.ex z).left (V i) (V j)).1 hz
    have e1 := GlobalTheory.valAt'_map (u.ex z).left (TopologicalSpace.Opens.infLELeft (V i) (V j)).op (b i) hz
    have e2 := GlobalTheory.valAt'_map (u.ex z).left (TopologicalSpace.Opens.infLERight (V i) (V j)).op (b j) hz
    refine (GlobalTheory.valAt'_sub (u.ex z).left (V i ⊓ V j) _ _).trans ?_
    rw [sub_eq_zero]
    exact e1.trans (((hb i z hz'.1).symm.trans (hb j z hz'.2)).trans e2.symm)
  obtain ⟨s, hs, -⟩ := A.left.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hVU i)) hcov b hcompat
  refine ⟨s, fun z hz => ?_⟩
  have h1 := hb ⟨z, hz⟩ z (hzW z hz)
  have h2 := GlobalTheory.valAt'_map (u.ex z).left (homOfLE (hVU ⟨z, hz⟩)).op s (hzW z hz)
  rw [h1, ← hs ⟨z, hz⟩]
  exact h2

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedOfLocallyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularOnOpenUniformised_of_locally : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (k : (Fin g → ℂ) → ℂ), (∀ z ∈ pre u.ex U, ∃ W : A.left.Opens, W ≤ U ∧ z ∈ pre u.ex W ∧ IsReg u.ex W k) → IsReg u.ex U k := by
  first | exact @GlobalTheory.CechPer.isReg_of_locally | exact GlobalTheory.CechPer.isReg_of_locally | (intros; apply GlobalTheory.CechPer.isReg_of_locally <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalMulVecApply
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory.OrthSumGram

open Matrix

theorem blockDiagonal'_mulVec_apply' {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (M : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (u : (Σ i, Fin (n i)) → ℂ) (i : ι) (j : Fin (n i)) :
    (blockDiagonal' M *ᵥ u) ⟨i, j⟩ = (M i *ᵥ fun l => u ⟨i, l⟩) j := by
  simp only [mulVec, dotProduct, Fintype.sum_sigma, blockDiagonal'_apply]
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [dite_eq_right (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem orth_sum_hasGram : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ) (W : ι → Submodule K V), (∀ σ x, 0 ≤ N σ x) → iSupIndep W → ⨆ i, W i = ⊤ → (∀ i, HasGram (fun σ (x : W i) => N σ x)) → (∀ σ, ∀ f : ∀ i, W i, N σ (∑ i, (f i : V)) ^ 2 = ∑ i, N σ (f i) ^ 2) → HasGram N := by
  classical
  intro K V _ _ _ _ ι _ N W hN hind htop hG hpy
  have hint : DirectSum.IsInternal W :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).2 ⟨hind, htop⟩
  let g := fun i => (hG i).some
  let n : ι → ℕ := fun i => (g i).1
  let b : ∀ i, Module.Basis (Fin (n i)) K (W i) := fun i => (g i).2.1.1
  let X : ∀ i, InfinitePlace K → Matrix (Fin (n i)) (Fin (n i)) ℂ := fun i => (g i).2.1.2
  have hX : ∀ i, IsGram (b i) (X i) (fun σ (x : W i) => N σ x) := fun i => (g i).2.2
  let B := hint.collectedBasis b
  have hB : ∀ a, B a = (b a.1 a.2 : V) := fun a => by
    simp only [B, DirectSum.IsInternal.collectedBasis_coe]
  let Xv : InfinitePlace K → Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℂ := fun v => blockDiagonal' fun i => X i v
  have hmul : ∀ v, Xv v * blockDiagonal' (fun i => (X i v)⁻¹) = 1 := fun v => by
    simp only [Xv, ← blockDiagonal'_mul]
    rw [← blockDiagonal'_one]
    congr 1
    funext i
    exact Matrix.mul_nonsing_inv _ ((hX i v).1)
  refine IsGram.hasGram (b := B) (X := Xv) fun v => ⟨Matrix.isUnit_det_of_right_inverse (hmul v), fun x => ?_⟩
  have hinv : (Xv v)⁻¹ = blockDiagonal' (fun i => (X i v)⁻¹) := Matrix.inv_eq_right_inv (hmul v)
  let c := B.repr x
  let f : ∀ i, W i := fun i => ∑ j, c ⟨i, j⟩ • b i j
  have hx : x = ∑ i, (f i : V) := by
    conv_lhs => rw [← B.sum_repr x]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [f, Submodule.coe_sum, Submodule.coe_smul, hB]
    rfl
  have hrep : ∀ i j, (b i).repr (f i) j = c ⟨i, j⟩ := fun i j => by
    simp only [f, Module.Basis.repr_sum_self]
  have hcoord : ∀ i j, Formalism.HermitianLatticesTheory.fcoord B Xv v x ⟨i, j⟩ = Formalism.HermitianLatticesTheory.fcoord (b i) (X i) v (f i) j := fun i j => by
    simp only [Formalism.HermitianLatticesTheory.fcoord, hinv, blockDiagonal'_mulVec_apply']
    congr 1
    funext l
    simp only [Formalism.HermitianLatticesTheory.vecAt, hrep, c]
  have hsq : Formalism.HermitianLatticesTheory.normAt B Xv v x ^ 2 = N v.embedding x ^ 2 := by
    rw [hx, hpy, ← hx]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : Formalism.HermitianLatticesTheory.normAt (b i) (X i) v (f i) = N v.embedding (f i) := (hX i v).2 (f i)
    rw [← e]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoord]
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt B Xv v x := Real.sqrt_nonneg _
  exact (sq_eq_sq₀ h0 (hN _ _)).1 hsq

end GlobalTheory.OrthSumGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralCoeIff
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.EigenlineBaseChange

theorem isIntegral_coe_iff {M : IntermediateField ℚ ℂ} (x : M) : IsIntegral ℤ (x : ℂ) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective

theorem span_eq_top {D : D7} {M : IntermediateField ℚ ℂ} [NumberField M]
    (hM : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M) (τ : D.what₂.Tau) (s : M)
    (hs : TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s}) :
    Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0, ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)} = ⊤ := by
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm
  have hsm : s ∈ TaylorLogMetric.ellT D M τ := hs ▸ Submodule.mem_span_singleton_self s
  rw [GlobalTheory.Glob.mem_ellT_iff hM] at hsm
  let g : ∀ y ∈ D.host.AA0, 𝓞 M := fun y hy =>
    ⟨s * ⟨_, hM τ (D.host.conj y)⟩, (isIntegral_coe_iff _).1 (hsm y hy)⟩
  set I : Ideal (𝓞 M) := Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0,
    ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)} with hI
  have hg : ∀ y hy, g y hy ∈ I := fun y hy => Ideal.subset_span ⟨y, hy, rfl⟩
  by_contra hI1
  have hI0 : I ≠ ⊥ := by
    intro h
    have h1 := hg 1 (GlobalTheory.AdelicApprox.one_mem_inverse_halfDifferent D)
    rw [h, Ideal.mem_bot] at h1
    have h2 : (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj 1) = 0 :=
      congrArg (fun a : 𝓞 M => ((a : M) : ℂ)) h1
    rw [map_one, map_one, mul_one] at h2
    exact hs0 (Subtype.ext h2)
  obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := M) hI0 hI1
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI0)] at hx
  have hxs : x * s ∈ TaylorLogMetric.ellT D M τ := by
    rw [GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
      (hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ (hg y hy)))
    have h1 : IsIntegral ℤ (((c : M) : ℂ)) := (isIntegral_coe_iff _).2 c.isIntegral_coe
    have h2 : ((c : M) : ℂ) = (x : ℂ) * ((s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)) :=
      congrArg (fun a : M => (a : ℂ)) hc
    rw [h2, ← mul_assoc] at h1
    exact h1
  rw [hs, Submodule.mem_span_singleton] at hxs
  obtain ⟨c, hc⟩ := hxs
  refine hx1 ((FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩)
  exact mul_right_cancel₀ hs0 hc

theorem ellT_eq_span_of_le : ∀ (D : D7) (M M' : IntermediateField ℚ ℂ) [NumberField M] [NumberField M'] (hle : M ≤ M'), (∀ τ x, TaylorLogMetric.embT D τ x ∈ M) → ∀ (τ : D.what₂.Tau) (s : M), TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s} → TaylorLogMetric.ellT D M' τ = Submodule.span (𝓞 M') {(⟨(s : ℂ), hle s.2⟩ : M')} := by
  intro D M M' _ _ hle hM τ s hs
  have hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M' := fun τ x => hle (hM τ x)
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm
  have hs0' : (s : ℂ) ≠ 0 := fun h => hs0 (Subtype.ext h)
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM'] at hx
    have key : ∀ a ∈ Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0,
        ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)},
        IsIntegral ℤ ((x : ℂ) * (s : ℂ)⁻¹ * ((a : M) : ℂ)) := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y, hy, e⟩ := ha
        rw [e, mul_assoc, inv_mul_cancel_left₀ hs0']
        exact hx y hy
      | zero => simpa using isIntegral_zero
      | add a b _ _ ha hb =>
        have e : (((a + b : 𝓞 M) : M) : ℂ) = ((a : M) : ℂ) + ((b : M) : ℂ) := rfl
        rw [e, mul_add]
        exact ha.add hb
      | smul c a _ ha =>
        have hc : IsIntegral ℤ (((c : M) : ℂ)) := (isIntegral_coe_iff _).2 c.isIntegral_coe
        have e : (((c • a : 𝓞 M) : M) : ℂ) = ((c : M) : ℂ) * ((a : M) : ℂ) := rfl
        rw [e, mul_left_comm]
        exact hc.mul ha
    have h1 := key 1 (by rw [span_eq_top hM τ s hs]; trivial)
    have e : (((1 : 𝓞 M) : M) : ℂ) = 1 := rfl
    rw [e, mul_one] at h1
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x * (⟨(s : ℂ), hle s.2⟩ : M')⁻¹, (isIntegral_coe_iff _).1 h1⟩, ?_⟩
    exact inv_mul_cancel_right₀ (fun h => hs0' (congrArg (fun a : M' => (a : ℂ)) h)) x
  · rw [Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM']
    exact (GlobalTheory.Glob.mem_ellT_iff hM τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)

end GlobalTheory.EigenlineBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAddLeDegOfIdealSmulLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAddLeDegOfIdealSmulLe
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.TwistIdeal

theorem htMap_le {K V W ι κ : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ} {b' : Module.Basis κ K W}
    {X' : InfinitePlace K → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K →+* ℂ) → W → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (φ : V →ₗ[K] W) (hφ : φ ≠ 0) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (hN : ∀ σ x, N' σ (φ x) ≤ t σ * N σ x) :
    Formalism.HN.htMap b X b' X' φ ≤ 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) := by
  have hop : ∀ v : InfinitePlace K, Formalism.HN.opNormAt b X b' X' v φ ^ 2 ≤ t v.embedding ^ 2 := fun v =>
    opNormAt_sq_le b X b' X' (fun v => (hG v).1) v (IsTotallyComplex.isComplex v) φ _ (sq_nonneg _) fun x => by
      rw [← normAt_sq_eq_majAt, ← normAt_sq_eq_majAt, (hG v).2, (hG' v).2, ← mul_pow]
      exact pow_le_pow_left₀ (normAt_nonneg _ _ _ _ |>.trans_eq ((hG' v).2 _)) (hN _ _) 2
  have hpos : ∀ v : InfinitePlace K, 0 < Formalism.HN.opNormAt b X b' X' v φ := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1) v φ hφ
  have hs : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← GlobalTheory.SlopeExt.sum_mk K fun v => Real.log (t v.embedding)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have e : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
      rw [e, htc σ]
  have hd : (Module.finrank ℚ K : ℝ) = 2 * Formalism.HN.nPl K := by
    have := GlobalTheory.SlopeExt.sum_mk K fun _ => (1 : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Embeddings.card] at this
    rw [this]; rfl
  have hn : (0 : ℝ) < Formalism.HN.nPl K := by
    have : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    linarith
  unfold Formalism.HN.htMap
  rw [hs, hd]
  have hsum : ∑ v, Real.log (Formalism.HN.opNormAt b X b' X' v φ ^ 2) ≤ ∑ v : InfinitePlace K, 2 * Real.log (t v.embedding) :=
    Finset.sum_le_sum fun v _ => by
      have := Real.log_le_log (pow_pos (hpos v) 2) (hop v)
      rw [Real.log_pow, Real.log_pow] at this
      rw [Real.log_pow]
      push_cast at this ⊢
      exact this
  rw [← Finset.mul_sum] at hsum
  rw [one_div, inv_mul_le_iff₀ hn]
  have : 2 * (2 * ∑ v : InfinitePlace K, Real.log (t v.embedding)) / (2 * (Formalism.HN.nPl K : ℝ)) * Formalism.HN.nPl K =
      2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    field_simp
  linarith

end GlobalTheory.TwistIdeal

namespace GlobalTheory.TwistIdeal

theorem deg_add_le_deg_of_ideal_smul_le : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (φ : V →ₗ[K] W) (t : (K →+* ℂ) → ℝ) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)), HasGram N → HasGram N' → Function.Injective φ → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ (φ x) ≤ t σ * N σ x) → L.FG → L'.FG → 𝔞 ≠ ⊥ → 𝔞 • L.map (φ.restrictScalars (𝓞 K)) ≤ L' → Formalism.HN.rkK L' = Formalism.HN.rkK L → deg N L + (Formalism.HN.rkK L : ℝ) * (-((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) ≤ deg N' L' := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N N' φ t L L' 𝔞 hN hN' hinj htpos htc hNb hL hL' h𝔞 hsub hrk
  by_cases h0 : L = ⊥
  · subst h0
    have h1 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) V) = 0 := by simp [Formalism.HN.rkK]
    rw [h1] at hrk
    simp [deg, h1, hrk]
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  obtain ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hI : ((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔞
  have hsm : Formalism.HermitianLatticesTheory.idealSmul (((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) : Submodule (𝓞 K) K)
      (L.map (φ.restrictScalars (𝓞 K))) ≤ L' := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal (S := (nonZeroDivisors (𝓞 K))) (P := K)).1 ha
    rw [algebraMap_smul]
    exact hsub (Submodule.smul_mem_smul hr hx)
  have key := Formalism.ExtensionFiltration.twistLower K V (Fin n) W (Fin n') b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1)
    φ L L' (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) hI hL hL' h0 hinj hsm hrk
  have hφ : φ ≠ 0 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact hx0 (hinj (by rw [h, map_zero, LinearMap.zero_apply]))
  have hht := htMap_le hG hG' φ hφ t htpos htc hNb
  rw [FractionalIdeal.coeIdeal_absNorm] at key
  have hb : slope_sq N L / 2 - (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ slope_sq N' L' / 2 := by
    rw [slope_sq_eq hG hL, slope_sq_eq hG' hL']
    have e1 : 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) =
        2 * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by ring
    have e2 : 2 * Real.log ((Ideal.absNorm 𝔞 : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) =
        2 * (Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) := by push_cast; ring
    rw [e1] at hht
    rw [e2] at key
    linarith
  have hr : (0 : ℝ) ≤ Formalism.HN.rkK L := Nat.cast_nonneg _
  unfold deg GlobalTheory.AllWt.slope
  rw [hrk]
  nlinarith [mul_le_mul_of_nonneg_left hb hr]

end GlobalTheory.TwistIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAddLeDegOfIdealSmulLeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_add_le_deg_of_ideal_smul_le_alt : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (φ : V →ₗ[K] W) (t : (K →+* ℂ) → ℝ) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)), HasGram N → HasGram N' → Function.Injective φ → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ (φ x) ≤ t σ * N σ x) → L.FG → L'.FG → 𝔞 ≠ ⊥ → 𝔞 • L.map (φ.restrictScalars (𝓞 K)) ≤ L' → Formalism.HN.rkK L' = Formalism.HN.rkK L → deg N L + (Formalism.HN.rkK L : ℝ) * (-((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) ≤ deg N' L' := by
  first | exact @GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le | exact GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le | (intros; apply GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularSectionOfRegularDifferences
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCocycleAffineOpenIsCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCocycleAffineOpenIsCoboundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer


open GlobalTheory.AbLaw in
theorem cech_one_cocycle_split : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (K : Type) (W : K → X.Opens), (∀ i, W i ≤ U) → U ≤ ⨆ i, W i → ∀ f : ∀ i j, Γ(X, W i ⊓ W j), (∀ i j k, (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j)).op).hom (f i j) + (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k)).op).hom (f j k) = (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k)).op).hom (f i k)) → ∃ a : ∀ i, Γ(X, W i), ∀ i j, f i j = (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (a i) - (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (a j) := by
  intro X U hU K W hW hc f hf
  have hM := ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB X
  obtain ⟨ψ, hψ⟩ := GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen hM hU K W hW hc
    (fun a b => (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).symm (f a b)) (by
      intro a b d O ha hb hd
      apply (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).injective
      have h : rs X inf_le_left (f a b) + rs X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (f b d) =
        rs X (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W a ⊓ W b ⊓ W d ≤ W a ⊓ W d) (f a d) := hf a b d
      have h := congrArg (rs X (le_inf (le_inf ha hb) hd)) h
      simp only [map_add (f := _), rs_rs] at h
      rw [map_add (f := _), GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]
      simpa only [LinearEquiv.apply_symm_apply] using h)
  refine ⟨fun a => GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top (ψ a), fun a b => ?_⟩
  have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
  rw [h, map_sub, GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
    GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCocycleAffineOpenIsCoboundaryStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechOneCocycle_affineOpen_isCoboundary : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (K : Type) (W : K → X.Opens), (∀ i, W i ≤ U) → U ≤ ⨆ i, W i → ∀ f : ∀ i j, Γ(X, W i ⊓ W j), (∀ i j k, (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j)).op).hom (f i j) + (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k)).op).hom (f j k) = (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k)).op).hom (f i k)) → ∃ a : ∀ i, Γ(X, W i), ∀ i j, f i j = (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (a i) - (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (a j) := by
  first | exact @GlobalTheory.CechPer.cech_one_cocycle_split | exact GlobalTheory.CechPer.cech_one_cocycle_split | (intros; apply GlobalTheory.CechPer.cech_one_cocycle_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularSectionOfRegularDifferences
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_section_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ →
    (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ U : A.left.affineOpens, ∃ k : (Fin g → ℂ) → ℂ,
    ∀ i, IsReg u.ex (U.1 ⊓ W i) (k - h i) := by
  intro A _ g L u hA K W h hcov hreg U
  obtain ⟨-, -, -, -, hinf, -, -, -, hres, he, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hres' : ∀ (V V' : A.left.Opens) (hle : V' ≤ V) (b : Γ(A.left, V)), ∀ z ∈ pre u.ex V',
      val u.ex V' ((A.left.presheaf.map (homOfLE hle).op).hom b) z = val u.ex V b z :=
    fun V V' hle b z hz ↦ hres V V' hle b z hz
  have vsub : ∀ (V : A.left.Opens) (b c : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (b - c) z = val u.ex V b z - val u.ex V c z := by
    intro V b c z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he', he']
    exact map_sub e (show Sec (str A) V from b) c
  have vadd : ∀ (V : A.left.Opens) (b c : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (b + c) z = val u.ex V b z + val u.ex V c z := by
    intro V b c z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he', he']
    exact map_add e (show Sec (str A) V from b) c
  have vneg : ∀ (V : A.left.Opens) (b : Γ(A.left, V)), ∀ z ∈ pre u.ex V,
      val u.ex V (-b) z = - val u.ex V b z := by
    intro V b z hz
    obtain ⟨e, he'⟩ := he V z hz
    rw [he', he']
    exact map_neg e (show Sec (str A) V from b)
  choose b hb using hreg
  have hle : ∀ i j, (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ≤ W i ⊓ W j :=
    fun i j ↦ inf_le_inf inf_le_right inf_le_right
  let f : ∀ i j, Γ(A.left, (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)) := fun i j ↦
    (A.left.presheaf.map (homOfLE (hle i j)).op).hom (b i j)
  have hf : ∀ i j, ∀ z ∈ pre u.ex ((U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)), val u.ex _ (f i j) z = h i z - h j z := by
    intro i j z hz
    rw [hres' _ _ (hle i j) (b i j) z hz]
    have hz' : z ∈ pre u.ex (W i ⊓ W j) := (hinf _ _).symm ▸ (by
      rw [hinf, hinf, hinf] at hz
      exact ⟨hz.1.2, hz.2.2⟩)
    rw [← hb i j z hz']
    rfl
  have hcoc : ∀ i j k, (A.left.presheaf.map (homOfLE (inf_le_left : (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j))).op).hom (f i j) +
      (A.left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k))).op).hom (f j k) =
      (A.left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (U.1 ⊓ W i) ⊓ (U.1 ⊓ W j) ⊓ (U.1 ⊓ W k) ≤ (U.1 ⊓ W i) ⊓ (U.1 ⊓ W k))).op).hom (f i k) := by
    intro i j k
    rw [← sub_eq_zero]
    refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA _ _ fun z hz ↦ ?_
    have hz3 := hz
    rw [hinf, hinf, hinf, hinf, hinf] at hz3
    rw [vsub _ _ _ z hz, vadd _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz,
      hf i j z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.1.1, hz3.1.1.2⟩, hz3.1.2.1, hz3.1.2.2⟩),
      hf j k z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.2.1, hz3.1.2.2⟩, hz3.2.1, hz3.2.2⟩),
      hf i k z (by rw [hinf, hinf, hinf]; exact ⟨⟨hz3.1.1.1, hz3.1.1.2⟩, hz3.2.1, hz3.2.2⟩)]
    ring
  have hcov' : U.1 ≤ ⨆ i, U.1 ⊓ W i := by
    rw [← inf_iSup_eq, hcov, inf_top_eq]
  obtain ⟨a, ha⟩ := GlobalTheory.T.cechOneCocycle_affineOpen_isCoboundary A.left U.1 U.2 K (fun i ↦ U.1 ⊓ W i) (fun i ↦ inf_le_left) hcov' f hcoc
  have key : ∀ i j z, z ∈ pre u.ex (U.1 ⊓ W i) → z ∈ pre u.ex (U.1 ⊓ W j) →
      h i z - val u.ex _ (a i) z = h j z - val u.ex _ (a j) z := by
    intro i j z hi hj
    have hz : z ∈ pre u.ex ((U.1 ⊓ W i) ⊓ (U.1 ⊓ W j)) := by rw [hinf]; exact ⟨hi, hj⟩
    have h1 := hf i j z hz
    rw [ha i j, vsub _ _ _ z hz, hres' _ _ _ _ z hz, hres' _ _ _ _ z hz] at h1
    linear_combination -h1
  classical
  refine ⟨fun z ↦ if hz : ∃ i, z ∈ pre u.ex (U.1 ⊓ W i) then
      h hz.choose z - val u.ex _ (a hz.choose) z else 0, fun i ↦ ⟨-(a i), fun z hz ↦ ?_⟩⟩
  have hex : ∃ i, z ∈ pre u.ex (U.1 ⊓ W i) := ⟨i, hz⟩
  simp only [Pi.sub_apply, dif_pos hex]
  rw [key _ i z hex.choose_spec hz, vneg _ _ z hz]
  ring

end GlobalTheory.CechPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularSectionOfRegularDifferencesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_section_of_regular_differences : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ U : A.left.affineOpens, ∃ k : (Fin g → ℂ) → ℂ, ∀ i, IsReg u.ex (U.1 ⊓ W i) (k - h i) := by
  first | exact @GlobalTheory.CechPer.exists_section_of_isReg_sub | exact GlobalTheory.CechPer.exists_section_of_isReg_sub | (intros; apply GlobalTheory.CechPer.exists_section_of_isReg_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerRealizeEqZero
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem gram_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (v : InfinitePlace K) : N v.embedding 0 = 0 := by
  rw [← (hG v).2 0]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord_zero]

theorem inner_realize_eq_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {x y : V}
    (h : ∀ v : InfinitePlace K, N v.embedding (x + y) ^ 2 = N v.embedding x ^ 2 + N v.embedding y ^ 2) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  have hs : ∀ z, ‖Formalism.HermitianLatticesTheory.realize b X z‖ ^ 2 = ∑ v : InfinitePlace K, N v.embedding z ^ 2 := fun z => by
    rw [GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2]
  have h1 := hs (x + y)
  rw [map_add (f := _), norm_add_sq_real, hs x, hs y] at h1
  rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib] at h1
  linarith

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inner_pair [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2)
    {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ M i) (hy : y ∈ M j) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  refine inner_realize_eq_zero hG fun v => ?_
  have hmem : ∀ (k : ι) (z : V) (_ : z ∈ M k) (l : ι),
      (Pi.single k z : ι → V) l ∈ Submodule.span K (M l : Set V) := by
    intro k z hz l
    by_cases hl : l = k
    · subst hl; simpa using Submodule.subset_span hz
    · simp [Pi.single_apply, hl]
  have h := hN v.embedding (Pi.single i x + Pi.single j y) fun l =>
    Submodule.add_mem _ (hmem i x hx l) (hmem j y hy l)
  have hsum : ∑ l, (Pi.single i x + Pi.single j y : ι → V) l = x + y := by
    simp [Finset.sum_add_distrib]
  have hpt : ∀ l, N v.embedding ((Pi.single i x + Pi.single j y : ι → V) l) ^ 2 =
      (Pi.single i (N v.embedding x ^ 2) : ι → ℝ) l + (Pi.single j (N v.embedding y ^ 2) : ι → ℝ) l := by
    intro l
    by_cases hli : l = i
    · subst hli; simp [Pi.single_apply, hij]
    · by_cases hlj : l = j
      · subst hlj; simp [Pi.single_apply, hli]
      · simp [Pi.single_apply, hli, hlj, gram_zero hG v]
  rw [hsum, Finset.sum_congr rfl fun l _ => hpt l, Finset.sum_add_distrib] at h
  simpa using h

theorem deg_eq [_root_.NumberField.IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    GlobalTheory.AllWt.deg N L = 1 / (Module.finrank ℚ K : ℝ) * Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L +
      (Formalism.HN.rkK L : ℝ) * ((-Real.log 2 + Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) / 2) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  rw [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, GlobalTheory.AllWt.slope_sq_eq hG hL]
  by_cases h0 : L = ⊥
  · subst h0
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX]
  · have hr : Formalism.HN.rkK L ≠ 0 := fun h => h0 (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.eq_bot_of_rkK b h)
    have hrk := (Formalism.HN.plLat K V (Fin n) b X hX L hL).2.1
    have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize b X) L =
        Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L / (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) := rfl
    have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)).ne'
    have hr' : (Formalism.HN.rkK L : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [Formalism.HN.muDef, hs, hrk]
    push_cast
    field_simp
    ring

end GlobalTheory.OrthRankDeg

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sum_finset [_root_.NumberField.IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hM : ∀ i, (M i).FG)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) (s : Finset ι) :
    (⨆ i ∈ s, M i).FG ∧ Formalism.HN.rkK (⨆ i ∈ s, M i) = ∑ i ∈ s, Formalism.HN.rkK (M i) ∧
      Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, M i) =
        ∑ i ∈ s, Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (M i) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  induction s using Finset.induction_on with
  | empty =>
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX, Submodule.fg_bot]
  | insert a s ha ih =>
    obtain ⟨ihfg, ihrk, ihdeg⟩ := ih
    rw [Finset.iSup_insert]
    set B := ⨆ i ∈ s, M i with hB
    have ho : ∀ x ∈ M a, ∀ y ∈ B,
        inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
      intro x hx y hy
      obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum M y).1 hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hμ, map_sum, inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact inner_pair hG M hN (by rintro rfl; exact ha hi) hx (μ i).2
    have hlA := (Formalism.HN.plLat K V (Fin n) b X hX (M a) (hM a)).1
    have hlB := (Formalism.HN.plLat K V (Fin n) b X hX B ihfg).1
    obtain ⟨hl, hdeg, -⟩ :=
      (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X)).2 (M a) B hlA hlB ho
    have hfg : (M a ⊔ B).FG := (hM a).sup ihfg
    have hinf : M a ⊓ B = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have h1 := ho x hx.1 x hx.2
      rw [inner_self_eq_zero] at h1
      exact Formalism.HN.HeightGram.realize_injective b X hX (by rw [h1, map_zero])
    have hrk := (Formalism.HN.degSupermod (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) (M a ⊔ B) (M a) B hl
      le_sup_left le_sup_right).1
    rw [hinf, (Formalism.HN.plLat K V (Fin n) b X hX _ hfg).2.1, (Formalism.HN.plLat K V (Fin n) b X hX _ (hM a)).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ ihfg).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ Submodule.fg_bot).2.1, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, mul_zero, add_zero,
      ← mul_add] at hrk
    have hrk' := Nat.eq_of_mul_eq_mul_left (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)) hrk
    refine ⟨hfg, ?_, ?_⟩
    · rw [hrk', Finset.sum_insert ha, ihrk]
    · rw [hdeg, Finset.sum_insert ha, ihdeg]

theorem rkK_deg_iSup : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ)
    (M : ι → Submodule (𝓞 K) V), HasGram N → (∀ i, (M i).FG) →
    (∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) → N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) →
    Formalism.HN.rkK (⨆ i, M i) = ∑ i, Formalism.HN.rkK (M i) ∧ deg N (⨆ i, M i) = ∑ i, deg N (M i) := by
  intro K V _ _ _ _ _ _ _ ι _ N M hG hM hN
  classical
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨⟨b, X⟩, hbX⟩⟩⟩ := hG
  obtain ⟨hfg, hrk, hdeg⟩ := sum_finset hbX M hM hN Finset.univ
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), M i) = ⨆ i, M i := by simp
  rw [hu] at hfg hrk hdeg
  refine ⟨hrk, ?_⟩
  rw [deg_eq hbX _ hfg, hdeg, hrk, Finset.mul_sum]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (deg_eq hbX _ (hM i)).symm

end GlobalTheory.OrthRankDeg
end
end

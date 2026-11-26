module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionPSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
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

namespace GlobalTheory.LogKSLoc

theorem leibniz_frac {B C : Type} [CommRing B] [CommRing C] (ψ : B →+* C) (d : C → C)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (D : Derivation ℤ B B) {b u r : B} (hu : IsUnit u)
    (h : b * u = r) (h₁ : d (ψ u) = ψ (D u)) (h₂ : d (ψ r) = ψ (D r)) : d (ψ b) = ψ (D b) := by
  subst h
  rw [map_mul, hd, h₁, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul] at h₂
  exact (hu.map ψ).mul_left_cancel (add_left_cancel h₂)

theorem exists_frac {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1))
    (hf : W.1 = X.basicOpen f) (b : Γ(X, W.1)) :
    ∃ u r : Γ(X, U.1), IsUnit ((X.presheaf.map (homOfLE hW).op).hom u) ∧
      b * (X.presheaf.map (homOfLE hW).op).hom u = (X.presheaf.map (homOfLE hW).op).hom r := by
  letI : Algebra Γ(X, U.1) Γ(X, W.1) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
  have hl : IsLocalization.Away f Γ(X, W.1) := U.2.isLocalization_of_eq_basicOpen f (homOfLE hW) hf
  obtain ⟨⟨r, u⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) b
  exact ⟨u.1, r, IsLocalization.map_units Γ(X, W.1) u, h⟩

theorem spMap_res_chart {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE hW).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  U.2.map_fromSpec W.2 (homOfLE hW).op

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem isKS_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (D r)) → GlobalTheory.LogKS.IsKS t V U v D Θ → GlobalTheory.LogKS.IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) DW ((X.presheaf.map (homOfLE hW).op).hom.mapMatrix Θ) := by
  intro E _ _ _ H X t V U W hW f hf n v D DW Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩
  have hWU : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, fun i => Wc i ⊓ t.G.hom ⁻¹ᵁ W.1, j, d, ?_, fun i => inf_le_left.trans (hj i), fun i => ?_,
    fun i h b => ?_, fun i i' O hO g S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [← iSup_inf_eq, hsup, ← Scheme.Hom.preimage_inf, inf_right_comm, inf_eq_right.mpr hW]
  · exact ⟨fun O hO => (hfld i).1 O (hO.trans inf_le_left), fun O hO => (hfld i).2.1 O (hO.trans inf_le_left),
      fun O O' h hO => (hfld i).2.2 O O' h (hO.trans inf_le_left)⟩
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r) =
        resG t.G.left (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i) ((t.G.hom.appLE U.1 (Wc i) (hWU i)).hom r) := by
      intro r
      have e1 := congrArg (fun k => k.hom r) (t.G.hom.map_appLE h (homOfLE hW).op)
      have e2 := congrArg (fun k => k.hom r) (t.G.hom.appLE_map (hWU i)
        (homOfLE (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i)).op)
      exact e1.trans e2.symm
    have key : ∀ r : Γ(X, U.1), d i _ ((t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r)) = (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        (DW ((X.presheaf.map (homOfLE hW).op).hom r)) := by
      intro r
      rw [hD, e, e, (hfld i).2.2 _ _ _ le_rfl, hcomp]
    obtain ⟨u, r, hu, hb⟩ := exists_frac U W hW f hf b
    exact leibniz_frac _ _ ((hfld i).2.1 _ inf_le_left) DW hu hb (key u) (key r)
  · refine htest i i' O (hO.trans (inf_le_inf inf_le_left inf_le_left)) g S
      (φ.comp (X.presheaf.map (homOfLE hW).op).hom) g₀ w ?_ hO' fun a => ?_
    · rw [hg₀, ← spMap_res_chart U W hW, ← Category.assoc, spMap_comp']
    · obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, spMap_comp', dualMap_comp']

end GlobalTheory.LogKSLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffineStatement
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
theorem _root_.GlobalTheory.T.kodairaSpencer_condition_restrict_basicOpen_of_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (D r)) → GlobalTheory.LogKS.IsKS t V U v D Θ → GlobalTheory.LogKS.IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) DW ((X.presheaf.map (homOfLE hW).op).hom.mapMatrix Θ) := by
  first | exact @GlobalTheory.LogKSLoc.isKS_basicOpen | exact GlobalTheory.LogKSLoc.isKS_basicOpen | (intros; apply GlobalTheory.LogKSLoc.isKS_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.NormBlowupInt

theorem isFinite_fromNormalization_int_of_isReduced {X Y : Scheme.{0}} {o : CommRingCat.{0}}
    [Algebra.FiniteType ℤ o] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o)
    [LocallyOfFiniteType g] [IsReduced X] [IsLocallyNoetherian X]
    (hess : ∀ x ∈ genericPoints X, (f.residueFieldMap x).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := (f.app U).hom.toAlgebra
  letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  haveI : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  haveI : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance
  haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  let D : Set X := genericPoints X
  have hD : Dense D := dense_iff_closure_eq.mpr genericPoints.closure
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  haveI : Finite ι := (GlobalTheory.finite_genericPoints_inter _ (f.isCompact_preimage hU.isCompact)).to_subtype
  letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType) (hess _ x.2.1)
  haveI (x : ι) := GlobalTheory.ZMain.finite_integralClosure_field Γ(Y, U) (X.residueField x.1)
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)

theorem dense_preimage_of_blowup {Z X' : Scheme.{0}} (J : Z.IdealSheafData) (b : X' ⟶ Z)
    (hb : FinalTheorems.Blowup b J) (hiso : ∀ V : Z.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (b ∣_ V))
    (W : Z.Opens) (hWd : Dense (W : Set Z)) : Dense ((b ⁻¹ᵁ W : X'.Opens) : Set X') := by
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hD' : Dense (((J.comap b).support : Set X')ᶜ) := by
    rw [← hD, ← D.coe_nonzeroLocus_canonical]
    exact D.dense_nonzeroLocus_canonical
  let Uc : Z.Opens := J.support.compl
  haveI : IsIso (b ∣_ Uc) := hiso Uc fun x hx => hx
  haveI hoi : IsOpenImmersion ((b ⁻¹ᵁ Uc).ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨y, hyO, hy⟩ := hD'.inter_open_nonempty O hO hne
  have hyU : y ∈ b ⁻¹ᵁ Uc := by
    change b y ∉ J.support
    intro h
    exact hy ((GlobalTheory.ProjBlowup.mem_support_comap J b y).2 h)
  let O' : (b ⁻¹ᵁ Uc).toScheme.Opens := (b ⁻¹ᵁ Uc).ι ⁻¹ᵁ ⟨O, hO⟩
  have hopen : IsOpen (((b ⁻¹ᵁ Uc).ι ≫ b) '' (O' : Set (b ⁻¹ᵁ Uc).toScheme)) :=
    ((b ⁻¹ᵁ Uc).ι ≫ b).isOpenEmbedding.isOpenMap _ O'.isOpen
  obtain ⟨w, ⟨t, htO, rfl⟩, hwW⟩ := hWd.inter_open_nonempty _ hopen ⟨_, ⟨⟨y, hyU⟩, hyO, rfl⟩⟩
  refine ⟨(b ⁻¹ᵁ Uc).ι t, htO, ?_⟩
  change b ((b ⁻¹ᵁ Uc).ι t) ∈ W
  rwa [← Scheme.Hom.comp_apply]

end GlobalTheory.NormBlowupInt

namespace GlobalTheory.NormBlowupInt

theorem exists_normBl : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens),
    Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z)
    (BD : EffCartierData S), IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ BD.idealSheaf = J.comap π ∧
    IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  intro n Z z hz hZ J W hWd hWJ
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : Algebra.FiniteType ℤ (CommRingCat.of (cycAway n)) := ‹Algebra.FiniteType ℤ (cycAway n)›
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨X', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  haveI : LocallyOfFiniteType (b ≫ z) := by
    obtain ⟨m, i, hi, e⟩ := hbs
    have := isProper_str (cycAway n) m
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)
  let V : X'.Opens := b ⁻¹ᵁ W
  haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx
  haveI hoi : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI : GlobalTheory.IsNormalScheme Z := .of_pred hZ
  haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)
  haveI : IsReduced V.toScheme := by
    exact inferInstance
  haveI hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of (cycAway n)) V.ι (b ≫ z)
      fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap
  let ν := V.ι.fromNormalization
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization := IsNormalScheme.pred _
  have hν : IsIso (ν ∣_ V) := by
    have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  have hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization) := by
    refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2
  have hVd : Dense (V : Set X') := dense_preimage_of_blowup J b hb hiso W hWd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)
    show ν t ∉ D.idealSheaf.support
    rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
    exact fun h => hWJ _ h ht
  refine ⟨V.ι.normalization, ν ≫ b, D.pull ν hK,
    ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact isProjOver_comp_of_isFinite ν hbs
  · rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]
  · rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbW
  · convert hd using 1
    ext t
    simp [V]

end GlobalTheory.NormBlowupInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjectiveStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_blowup_cyclotomicAway_projective : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens), Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z) (BD : EffCartierData S), IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ BD.idealSheaf = J.comap π ∧ IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  first | exact @GlobalTheory.NormBlowupInt.exists_normBl | exact GlobalTheory.NormBlowupInt.exists_normBl | (intros; apply GlobalTheory.NormBlowupInt.exists_normBl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarised
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.NormIso

theorem prod_zpow_eq_one {K U : Type} [Fintype K] [CommGroup U] (ε : K → ℤ) (hε : ∑ k, ε k = 0) (c : U) :
    ∏ k, c ^ ε k = 1 := by
  have h : ∀ s : Finset K, ∏ k ∈ s, c ^ ε k = c ^ (∑ k ∈ s, ε k) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  rw [h, hε, zpow_zero]

theorem gm_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (ε : K → ℤ) (hε : ∑ k, ε k = 0)
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a a' : M.ι)
    (ha : r y ∈ LB.wchart M φ (fun _ => a)) (ha' : r y ∈ LB.wchart M φ (fun _ => a')) :
    gm r y (LB.wchart M φ (fun _ => a) ⊓ LB.wchart M φ (fun _ => a'))
      ((LB.LinComb M φ ε).g (fun _ => a) (fun _ => a')) = 1 :=
  (gm_linComb M φ ε r y _ _ ha ha').trans ((Finset.prod_congr rfl fun k _ => by rw [hq k]).trans
    (prod_zpow_eq_one ε hε (gm q y (M.U a ⊓ M.U a') (M.g a a'))))

theorem mem_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B))
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a : M.ι) (ha : q y ∈ M.U a) :
    r y ∈ LB.wchart M φ (fun _ => a) :=
  Set.mem_iInter.2 fun k => show (r ≫ φ k) y ∈ M.U a by rw [hq k]; exact ha

theorem exists_normalised {S X X' B B' : Scheme.{0}} (M : LB B) (M' : LB B') (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (φ' : K → (X' ⟶ B')) (ε : K → ℤ) (hε : ∑ k, ε k = 0) (F : X' ⟶ X)
    (e : S ⟶ X') (π : X' ⟶ S) (he : e ≫ π = 𝟙 S) (q : S ⟶ B) (q' : S ⟶ B') (hq : ∀ k, (e ≫ F) ≫ φ k = q)
    (hq' : ∀ k, e ≫ φ' k = q') (w₀ : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (z : Z) (a : M.ι) (b : M'.ι), q (t z) ∈ M.U a → q' (t z) ∈ M'.U b →
        gw w (t ≫ e) z (fun _ => a) (fun _ => b) = 1 := by
  let C : M.ι × M'.ι → X'.Opens := fun i =>
    ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)
  have mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b) := fun x a b ha hb =>
    ⟨mem_pull.2 (mem_const M φ (e ≫ F) q hq x a ha), mem_const M' φ' e q' hq' x b hb⟩
  obtain ⟨u, hu⟩ := glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hM (q x)
      obtain ⟨b, hb⟩ := exists_chart hM' (q' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)
    (fun i => pullU e (C i) (w₀.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by
      have hi : e x ∈ C i := hx.1
      have hj : e x ∈ C j := hx.2
      refine (gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)
      rw [Category.id_comp]
      have h := (isGen_iff w₀).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2)
        (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
      refine h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹)
        (gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1))
        (gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))
  let c : Γ(X', ⊤)ˣ := res (fun _ _ => trivial : (⊤ : X'.Opens) ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ u⁻¹)
  refine ⟨DVR.scaleGen c w₀, DVR.scaleGen_isGen c w₀ hw, fun Z t z a b ha hb => ?_⟩
  have hm : e (t z) ∈ C (a, b) := mem (t z) a b ha hb
  have h₁ : gm (t ≫ e) z (C (a, b)) (res le_top c) = (gm t z ⊤ u)⁻¹ := by
    refine (gm_res (t ≫ e) z le_top hm c).trans ((gm_res (t ≫ e) z (V := ⊤) _ trivial _).trans
      ((gm_pull (t ≫ e) π z ⊤ trivial _).trans ?_))
    rw [Category.assoc, he, Category.comp_id, map_inv]
  have h₂ : gm (t ≫ e) z (C (a, b)) (w₀.s (fun _ _ => a, fun _ => b)) = gm t z ⊤ u :=
    (gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans
      (gm_res t z le_top hm u))
  exact (map_mul (gm (t ≫ e) z (C (a, b))) _ _).trans ((congrArg₂ (· * ·) h₁ h₂).trans (inv_mul_cancel _))

theorem lift_one_psum {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (I : Finset (Fin 2)) :
    lift (1 : T ⟶ G) 1 ≫ psum G (x2 G) I = 1 := by
  have h : (fun k => lift (1 : T ⟶ G) 1 ≫ x2 G k) = fun _ => 1 := by
    funext k
    fin_cases k
    · exact lift_fst _ _
    · exact lift_snd _ _
  rw [comp_psum, h, psum_one]

theorem origin_square {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {β : G'.left ⟶ G.left} {β₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (T : Over S') :
    (lift (1 : T ⟶ G') 1).left ≫ β₂ = (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left := by
  have h₁ : (1 : T ⟶ G').left ≫ β = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h T))
  have a₁ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.1, ← Category.assoc, ← Over.comp_left, lift_fst, h₁]
  have a₂ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.2, ← Category.assoc, ← Over.comp_left, lift_snd, h₁]
  have b₁ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_fst (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  have b₂ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_snd (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  exact pullback.hom_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)

theorem exists_lamVal_origin {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} {β₂ : (G2 G').left ⟶ (G2 G).left} {M : LB G.left}
    {M' : LB G'.left} (hM : M.IsLB) (hM' : M'.IsLB) (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (H : LBIso (abelian₂ G' M') ((abelian₂ G M).pull β₂)) :
    ∃ w : LB.Iso (abelian₂ G' M') ((abelian₂ G M).pull β₂), w.IsGen ∧ ∀ (T : Over S') z J J', Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J J' = 1 := by
  obtain ⟨w₀, hw₀⟩ := H
  let e : (𝟙_ (Over S')).left ⟶ (G2 G').left := (lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
  let q : (𝟙_ (Over S')).left ⟶ G.left := (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left
  let q' : (𝟙_ (Over S')).left ⟶ G'.left := (1 : 𝟙_ (Over S') ⟶ G').left
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum G (x2 G) I.down).left = q := fun I =>
    (congrArg (· ≫ (psum G (x2 G) I.down).left) (origin_square h hs (𝟙_ (Over S')))).trans
      (congrArg (fun z => z.left) (lift_one_psum G (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) I.down))
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum G' (x2 G') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (lift_one_psum G' (T := 𝟙_ (Over S')) I.down)
  obtain ⟨w, hw, hv⟩ := exists_normalised M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum G (x2 G) I.down).left) (fun I => (psum G' (x2 G') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e (toUnit (G2 G')).left
    (congrArg (fun z => z.left) (toUnit_unique (lift (1 : 𝟙_ (Over S') ⟶ G') 1 ≫ toUnit (G2 G')) (𝟙 _))) q q' hq hq'
    w₀ hw₀
  refine ⟨w, hw, fun T z J J' hJ hJ' => ?_⟩
  have hp : (lift (1 : T ⟶ G') (1 : T ⟶ G')).left = (toUnit T).left ≫ e := by
    show _ = (toUnit T ≫ lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
    rw [comp_lift, MonObj.comp_one]
  have key : ∀ (p : T.left ⟶ (G2 G').left) (j : (abelian₂ G M).ι) (k : (abelian₂ G' M').ι),
      (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum G (x2 G) I.down).left)) = j →
      (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum G' (x2 G') I.down).left)) = k →
      lamVal w p z J J' = gw (L := abelian₂ G M) (L' := abelian₂ G' M') w p z j k := by
    rintro p _ _ rfl rfl
    rfl
  rw [hp]
  refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
    (funext fun I => ?_)).trans (hv T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
  · rw [← hq I, Category.assoc, Category.assoc]
  · rw [← hq' I, Category.assoc]

theorem exists_normalised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → letI := P.isAb.comm; ∃ w : LB.Iso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂), w.IsGen ∧ ∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good P.L z J' → lamVal w (lift (1 : T ⟶ P.A) (1 : T ⟶ P.A)).left z J J' = 1 :=
  fun _ _ _ _ _ _ Q _ P _ _ hpb hs H =>
    letI := P.isAb.comm
    exists_lamVal_origin Q.M.isLB P.isLB hpb hs H

end GlobalTheory.PolDeg.NormIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordBundleIso_value_one_origin_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → letI := P.isAb.comm; ∃ w : LB.Iso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂), w.IsGen ∧ ∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good P.L z J' → lamVal w (lift (1 : T ⟶ P.A) (1 : T ⟶ P.A)).left z J J' = 1 := by
  first | exact @GlobalTheory.PolDeg.NormIso.exists_normalised_iso | exact GlobalTheory.PolDeg.NormIso.exists_normalised_iso | (intros; apply GlobalTheory.PolDeg.NormIso.exists_normalised_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgree
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualLocus

theorem exists_ideal_locTriv_noeth (hG : GlobalFnsSt) (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [GrpObj B] (hB : IsAbelianScheme B) (F : LB B.left) (hF : F.IsLB) :
    ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) →
      ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧
        Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  haveI := hB.proper
  haveI := hB.geomConnected
  haveI := hB.smooth
  have hP := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom hF
  have hQ := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom (isLB_pw hF (-1))
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := TrivRep.exists_ideal (TrivRep.TrivOn B.hom F) (TrivRep.TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact TrivRep.trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => TrivRep.loc_iff B.hom F h q

variable {S : Scheme.{0}} (A : Over S)

theorem isPullback_lift {Y T : Over S} (y : Y ⟶ T) :
    IsPullback (lift (fst A Y) (snd A Y ≫ y)).left (snd A Y).left (snd A T).left y.left := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  have e₁ : (lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom = (fst A Y).left := by
    rw [show pullback.fst A.hom T.hom = (fst A T).left from rfl, ← Over.comp_left, lift_fst]
  have big : IsPullback ((lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom) (snd A Y).left A.hom
      (y.left ≫ T.hom) := by
    have := IsPullback.of_hasPullback A.hom Y.hom
    rw [e₁, Over.w y]
    exact this
  exact IsPullback.of_right big (by rw [← Over.comp_left, lift_snd, Over.comp_left]) h₀

theorem exists_closed_locTriv_noeth (hG : GlobalFnsSt) {T : Over S} [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (F : LB (A ⊗ T).left) (hF : F.IsLB) :
    ∃ (G : Over S) (i : G ⟶ T), IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T),
      TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  obtain ⟨I, hI⟩ := TrivSubscheme.exists_idealSheaf (TrivSubscheme.LocTrivOver (snd A T).left F)
    TrivSubscheme.LocTrivOver.comp TrivSubscheme.locTrivOver_of_affine (fun U => by
      haveI := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(T.left, U)) ⟶ S := U.2.fromSpec ≫ T.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ T.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A T).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth hG Γ(T.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hA t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun R g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI R g.hom _ _ _ h₃, TrivSubscheme.locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((TrivSubscheme.triv_pull_iff _ _ _).trans (TrivSubscheme.triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ T.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun Y y => ?_⟩
  rw [hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ y.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι y.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w y)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨z, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp z.left I.subschemeι)

variable {A} [GrpObj A]

theorem same_iff_locTriv (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {T : Over S} {N N' : LB (A ⊗ T).left}
    (hN : Fam A N) (hN' : Fam A N') {F : LB (A ⊗ T).left} (hF : F.IsLB)
    (hc : cls F hF = cls N hN.isLB - cls N' hN'.isLB) (Y : Over S) (y : Y ⟶ T) :
    Same A N N' y y ↔ TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left := by
  let ψ := (lift (fst A Y) (snd A Y ≫ y)).left
  let p := (snd A Y).left
  let e := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  have he : e ≫ p = 𝟙 Y.left := by
    simp only [e, p]
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hs : Same A N N' y y ↔ CechPic.pull ψ (cls F hF) = 0 := by
    rw [same_iff hN.isLB hN'.isLB, hc, map_sub, sub_eq_zero]
    rfl
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
      Triv (F.pull (r ≫ ψ)) ↔ CechPic.pull r (CechPic.pull ψ (cls F hF)) = 0 := fun r => by
    rw [← pull_comp, ← cls_pull hF _ (pull_isLB hF _)]
    exact (cls_eq_zero_iff (pull_isLB hF _)).symm
  have z₀ : CechPic.pull (e ≫ ψ) (cls F hF) = 0 := by
    have ee : e ≫ ψ = (lift (1 : Y ⟶ A) y).left := by
      simp only [e, ψ]
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [ee, hc, map_sub]
    have a := hN.add.evc_one hN.isLB y
    have b := hN'.add.evc_one hN'.isLB y
    simp only [evc] at a b
    rw [a, b, sub_zero]
  rw [TrivSubscheme.locTrivOver_iff (isPullback_lift A y), hs]
  constructor
  · intro h q
    exact ⟨⊤, trivial, (key _).2 (by rw [h, map_zero])⟩
  · intro h
    have cl : ∀ {Z : Scheme.{0}} (φ' : Fin 2 → (Z ⟶ (A ⊗ T).left)),
        Triv (LB.LinComb F φ' ![1, -1]) ↔
          CechPic.pull (φ' 0) (cls F hF) - CechPic.pull (φ' 1) (cls F hF) = 0 := fun φ' => by
      refine (cls_eq_zero_iff (LB.isLB_linComb hF _ _)).symm.trans ?_
      rw [cls_linComb hF, Fin.sum_univ_two]
      simp [sub_eq_add_neg]
    have sec : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
        CechPic.pull (r ≫ p ≫ e ≫ ψ) (cls F hF) = 0 := fun r => by
      rw [pull_comp, pull_comp, z₀, map_zero, map_zero]
    have T₀ : Triv (LB.LinComb F ![ψ, p ≫ e ≫ ψ] ![1, -1]) := by
      refine CubeGen.triv_of_local hF _ _ p e he (fun Z b U _ k => ?_) (fun V => ?_) (fun s => ?_)
      · have w : b ≫ e ≫ p ≫ e ≫ ψ = b ≫ e ≫ ψ := by
          rw [reassoc_of% he]
        simp [Fin.prod_univ_two, w]
      · let YV : Over S := Over.mk (V.ι ≫ Y.hom)
        let v : YV ⟶ Y := Over.homMk V.ι rfl
        exact ⟨_, _, (snd A YV).left, isPullback_lift A v, surj_snd hG hA YV⟩
      · obtain ⟨U, hU, ht⟩ := h s
        refine ⟨U, hU, ?_⟩
        unfold CubeGen.TrivAt
        rw [cl]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [sec, sub_zero, pull_comp]
        exact (key _).1 ht
    have := (cl _).1 T₀
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
    have s₁ := sec (𝟙 _)
    rw [Category.id_comp] at s₁
    rwa [s₁, sub_zero] at this

theorem exists_closed_same : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left],
    IsAbelianScheme A → ∀ (N N' : LB (A ⊗ T).left), Fam A N → Fam A N' → ∃ (G : Over S) (i : G ⟶ T),
      IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T), Same A N N' y y ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  intro S A T _ _ hA N N' hN hN'
  obtain ⟨F, hF, hc⟩ := cls_surj (cls N hN.isLB - cls N' hN'.isLB)
  obtain ⟨G, i, hi, hG⟩ := exists_closed_locTriv_noeth A ExpansionTotal.globalFns hA F hF
  exact ⟨G, i, hi, fun Y y => (same_iff_locTriv ExpansionTotal.globalFns hA hN hN' hF hc Y y).trans (hG Y y)⟩

end GlobalTheory.DualLocus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgreeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left], IsAbelianScheme A → ∀ (N N' : LB (A ⊗ T).left), Fam A N → Fam A N' → ∃ (G : Over S) (i : G ⟶ T), IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T), Same A N N' y y ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  first | exact @GlobalTheory.DualLocus.exists_closed_same | exact GlobalTheory.DualLocus.exists_closed_same | (intros; apply GlobalTheory.DualLocus.exists_closed_same <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompleteOfFinite
open IsLocalRing

namespace GlobalTheory.FiniteLocalCompleteness

theorem precomplete_of_finite {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (M : Type) [AddCommGroup M]
    [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨a • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    have : AdicCompletion.of I R a = algebraMap R (AdicCompletion I R) a := rfl
    rw [this, algebraMap_smul]
  | add s t hs ht =>
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem precomplete_of_pow_le {S : Type} [CommRing S] (I J : Ideal S) [hI : IsPrecomplete I S] (hIJ : I ≤ J) (k : ℕ)
    (hk : J ^ (k + 1) ≤ I) : IsPrecomplete J S := by
  refine ⟨fun f hf => ?_⟩
  have h1 : ∀ n, (J ^ ((k + 1) * n) • ⊤ : Submodule S S) ≤ I ^ n • ⊤ := fun n => by
    refine Submodule.smul_mono_left ?_
    rw [pow_mul]
    exact Ideal.pow_right_mono hk n
  obtain ⟨L, hL⟩ := hI.prec (f := fun n => f ((k + 1) * n))
    (fun {m n} h => (hf (Nat.mul_le_mul_left _ h)).mono (h1 m))
  refine ⟨L, fun n => ?_⟩
  refine (hf (show n ≤ (k + 1) * n by nlinarith)).trans ((hL n).mono ?_)
  exact Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)

theorem isLocalRing_of_complete {S : Type} [CommRing S] [IsDomain S] (I : Ideal S) [IsAdicComplete I S]
    [IsArtinianRing (S ⧸ I)] : IsLocalRing S := by
  have hjac := IsAdicComplete.le_jacobson_bot I
  have hu : ∀ z ∈ I, IsUnit (1 - z) := fun z hz => by
    have := Ideal.mem_jacobson_bot.1 (hjac (I.neg_mem hz)) 1
    simpa [sub_eq_add_neg, add_comm] using this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨n, y', hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I x) (1 : S ⧸ I)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
  simp only [smul_eq_mul, mul_one] at hy
  set X := Ideal.Quotient.mk I x with hX
  set Y := Ideal.Quotient.mk I y with hY
  have hk : ∀ k : ℕ, X ^ n * (X * Y) ^ k = X ^ n := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      calc X ^ n * (X * Y) ^ (k + 1) = (X ^ (n + 1) * Y) * (X * Y) ^ k := by ring
        _ = X ^ n := by rw [Nat.succ_eq_add_one] at hy; rw [hy, ih]
  have he : ((X * Y) ^ n) ^ 2 = (X * Y) ^ n := by
    calc ((X * Y) ^ n) ^ 2 = (X ^ n * (X * Y) ^ n) * Y ^ n := by ring
      _ = (X * Y) ^ n := by rw [hk]; ring
  have hE : Ideal.Quotient.mk I ((x * y) ^ n) = (X * Y) ^ n := by simp [hX, hY]
  obtain ⟨a, ha, hae⟩ := HenselianRing.is_henselian (I := I) (Polynomial.X ^ 2 - Polynomial.X : Polynomial S)
    (by monicity!) ((x * y) ^ n)
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, map_sub]
      rw [map_pow, hE, he, sub_self])
    (by
      have : Ideal.Quotient.mk I (Polynomial.eval ((x * y) ^ n)
          (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X : Polynomial S))) = 2 * (X * Y) ^ n - 1 := by
        rw [← hE]
        simp [one_add_one_eq_two, map_ofNat]
      rw [this]
      exact IsUnit.of_mul_eq_one (2 * (X * Y) ^ n - 1) (by linear_combination 4 * he))
  have ha' : a * (a - 1) = 0 := by
    have : a ^ 2 - a = 0 := by simpa using ha
    linear_combination this
  rcases mul_eq_zero.1 ha' with h0 | h0
  · right
    subst h0
    have h2 : (X * Y) ^ n = 0 := by
      rw [← hE, Ideal.Quotient.eq_zero_iff_mem]
      simpa using hae
    have h3 : x ^ n ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← hX, ← hk n, h2, mul_zero]
    exact isUnit_of_dvd_unit (one_sub_dvd_one_sub_pow x n) (hu _ h3)
  · obtain rfl : a = 1 := sub_eq_zero.1 h0
    have h2 := hu _ hae
    rw [sub_sub_cancel] at h2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h3 := hk 1
      left
      have h4 : 1 - x * y ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simp only [pow_zero, pow_one, one_mul] at h3
        rw [map_sub, map_one, map_mul, ← hX, ← hY, h3, sub_self]
      have h5 := hu _ h4
      rw [sub_sub_cancel] at h5
      exact isUnit_of_mul_isUnit_left h5
    · left
      exact isUnit_of_mul_isUnit_left ((isUnit_pow_iff hn.ne').1 h2)

theorem local_complete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] :
    ∃ _ : IsLocalRing S, IsAdicComplete (maximalIdeal S) S := by
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  haveI : IsPrecomplete (maximalIdeal R) S := precomplete_of_finite _ S
  haveI : IsAdicComplete (maximalIdeal R) S := ⟨⟩
  set I := (maximalIdeal R).map (algebraMap R S) with hI
  haveI : IsAdicComplete I S := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance
  haveI : IsArtinianRing (S ⧸ I) := by
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R _ _
    exact IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  haveI hl : IsLocalRing S := isLocalRing_of_complete I
  refine ⟨hl, ?_⟩
  have hne : I ≠ ⊤ := by
    intro h
    have := IsAdicComplete.le_jacobson_bot I
    rw [h, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at this
    exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 this)
  have hrad : maximalIdeal S ≤ I.radical := by
    intro x hx
    obtain ⟨n, y', hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I x) (1 : S ⧸ I)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
    simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
    have hu : IsUnit (1 - x * y) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right y (maximalIdeal S) hx)
    refine ⟨n, (Ideal.mul_unit_mem_iff_mem I hu).1 ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_mul, map_pow, map_sub, map_one]
    linear_combination -hy
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal S) S :=
    precomplete_of_pow_le I _ (le_maximalIdeal hne) k ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)
  exact ⟨⟩

theorem exists_normal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : Type) [CommRing D] [IsDomain D]
    [Algebra R D] [Module.Finite R D] [FaithfulSMul R D] (hR : GlobalTheory.TorRef.IsCN R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : D →+* R'),
      GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp (algebraMap R D) = ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := hR
  letI : Algebra (FractionRing R) (FractionRing D) := FractionRing.liftAlgebra R (FractionRing D)
  haveI : IsScalarTower R (FractionRing R) (FractionRing D) := FractionRing.isScalarTower_liftAlgebra R _
  haveI : FiniteDimensional (FractionRing R) (FractionRing D) :=
    Module.Finite.of_isLocalization R D (nonZeroDivisors R) (Rₚ := FractionRing R) (Sₚ := FractionRing D)
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  haveI : Algebra.IsIntegral (FractionRing R) (FractionRing D) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing D) := Algebra.IsSeparable.of_integral _ _
  let S := integralClosure R (FractionRing D)
  haveI : Module.Finite R S := IsIntegralClosure.finite R (FractionRing R) (FractionRing D) S
  haveI : IsIntegrallyClosed S := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have hL : Function.Injective (algebraMap R (FractionRing D)) := FaithfulSMul.algebraMap_injective R _
  have hS : Function.Injective (algebraMap R S) := fun a b h => hL (congrArg Subtype.val h)
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hS
  obtain ⟨hl, hc⟩ := local_complete_of_finite R S
  let ψ : D →ₐ[R] FractionRing D := IsScalarTower.toAlgHom R D _
  let σ : D →ₐ[R] S := ψ.codRestrict S fun c => (Algebra.IsIntegral.isIntegral c).map ψ
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite _ _
  refine ⟨S, inferInstance, inferInstance, hl, algebraMap R S, σ.toRingHom,
    ⟨IsNoetherianRing.of_finite R S, inferInstance, hc, charZero_of_injective_algebraMap hS⟩, hS,
    RingHom.finite_algebraMap.2 inferInstance, Algebra.IsIntegral.isLocalHom R S, σ.comp_algebraMap⟩

theorem main (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [CommRing C] (φ : R →+* C)
    (hR : GlobalTheory.TorRef.IsCN R) (hφ : Function.Injective φ) (hfin : φ.Finite) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : C →+* R'),
      GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp φ = ρ := by
  letI : Algebra R C := φ.toAlgebra
  haveI : Module.Finite R C := hfin
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := C) (⊥ : Ideal R) ⊥
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]; exact ((RingHom.injective_iff_ker_eq_bot _).1 hφ).le)
  have hD : Function.Injective (algebraMap R (C ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ P.comap (algebraMap R C) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    change a ∈ Ideal.under R P at this
    rwa [hPc] at this
  haveI : FaithfulSMul R (C ⧸ P) := (faithfulSMul_iff_algebraMap_injective _ _).2 hD
  obtain ⟨R', i1, i2, i3, ρ, σ, h1, h2, h3, h4, h5⟩ := exists_normal R (C ⧸ P) hR
  exact ⟨R', i1, i2, i3, ρ, σ.comp (Ideal.Quotient.mk P), h1, h2, h3, h4, h5⟩

end GlobalTheory.FiniteLocalCompleteness
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocExt

theorem exists_isCN_cover_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [CommRing C] (φ : R →+* C), IsCN R → Function.Injective φ → φ.Finite → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : C →+* R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp φ = ρ := by
  first
  | exact @_root_.GlobalTheory.FiniteLocalCompleteness.main
  | exact _root_.GlobalTheory.FiniteLocalCompleteness.main
  | (apply _root_.GlobalTheory.FiniteLocalCompleteness.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteLocalCompleteness.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteLocalCompleteness.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteLocalCompleteness.main ..)

end GlobalTheory.LocExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [CommRing C] (φ : R →+* C), IsCN R → Function.Injective φ → φ.Finite → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : C →+* R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp φ = ρ := by
  first | exact @GlobalTheory.LocExt.exists_isCN_cover_of_finite | exact GlobalTheory.LocExt.exists_isCN_cover_of_finite | (intros; apply GlobalTheory.LocExt.exists_isCN_cover_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureGaloisFiniteAutGroupInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureGaloisFiniteAutGroupInvariants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem integralClosure_galois_finite_invariants :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L], letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra; Module.Finite A (integralClosure A L) ∧ Finite (integralClosure A L ≃ₐ[A] integralClosure A L) ∧ Function.Injective (algebraMap A (integralClosure A L)) ∧ ∀ b : integralClosure A L, (∀ σ : integralClosure A L ≃ₐ[A] integralClosure A L, σ b = b) → b ∈ Set.range (algebraMap A (integralClosure A L)) := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable K L := inferInstance
  refine ⟨IsIntegralClosure.finite A K L (integralClosure A L), ?_, ?_, ?_⟩
  · exact Finite.of_equiv _ (galRestrict A K L (integralClosure A L)).toEquiv
  · intro x y h
    have h' := congrArg (algebraMap (integralClosure A L) L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at h'
    exact IsFractionRing.injective A K ((algebraMap K L).injective h')
  · intro b hb
    haveI : IsFractionRing (integralClosure A L) L :=
      integralClosure.isFractionRing_of_finite_extension K L
    have := Algebra.isInvariant_of_isGalois' A K L (integralClosure A L)
    exact this.isInvariant b hb

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureGaloisFiniteAutGroupInvariantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_galois_finite_autGroup_invariants : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L], letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra; Module.Finite A (integralClosure A L) ∧ Finite (integralClosure A L ≃ₐ[A] integralClosure A L) ∧ Function.Injective (algebraMap A (integralClosure A L)) ∧ ∀ b : integralClosure A L, (∀ σ : integralClosure A L ≃ₐ[A] integralClosure A L, σ b = b) → b ∈ Set.range (algebraMap A (integralClosure A L)) := by
  first | exact @GlobalTheory.Poinc.integralClosure_galois_finite_invariants | exact GlobalTheory.Poinc.integralClosure_galois_finite_invariants | (intros; apply GlobalTheory.Poinc.integralClosure_galois_finite_invariants <;> assumption)
end
end

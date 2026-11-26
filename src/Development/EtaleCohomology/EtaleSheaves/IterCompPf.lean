module

public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
public import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.IterCompPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterCompPf

theorem isLine_iso_comp {L L' S : Scheme.{0}} (e : L' ⟶ L) [IsIso e] {l : L ⟶ S} (h : IsLine l) :
    IsLine (e ≫ l) :=
  h.bc (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ l) l (𝟙 S))

theorem iterLine_iso_comp {T S Y : Scheme.{0}} {k : T ⟶ S} (hk : IterLine k) (e : Y ⟶ T) [IsIso e] :
    IterLine (e ≫ k) := by
  cases hk with
  | iso k' hk' => exact IterLine.iso _ inferInstance
  | comp l k' hl hk' =>
    rw [← Category.assoc]
    exact IterLine.comp _ _ (isLine_iso_comp e hl) hk'

theorem IterComp_of : LateralTheory.E.ChowGraphCut.IterComp := by
  intro P T S l k hl hk
  induction hl with
  | iso e he => exact iterLine_iso_comp hk e
  | comp l₁ k₁ hl₁ _ ih =>
    rw [Category.assoc]
    exact IterLine.comp _ _ hl₁ ih

end LateralTheory.E.IterCompPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EmptyH2
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.EmptyH₂

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] :
    Subsingleton (Sec F Y) := by
  have hT := Sheaf.isTerminalOfBotCover F Y (Scheme.bot_mem_grothendieckTopology (P := @Etale) Y)
  exact (ModuleCat.isZero_iff_subsingleton).1 hT.isZero

theorem h_empty (hH : Hyp) {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] (n : ℤ)
    (x : H R (sch.obj Y) F n) : x = 0 := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := (hH.a9 R F).1 (sch.obj Y) n hn
    exact Subsingleton.elim _ _
  · obtain ⟨e, -, -⟩ := (hH.a9 R F).2
    have := sec_subsingleton F Y
    rw [← (e Y).apply_symm_apply x, Subsingleton.elim ((e Y).symm x) 0, map_zero]
  · obtain ⟨Z, f, -, -, hf⟩ := hH.a5 R Y F n hn x
    have : IsIso (sch.map f) := inferInstance
    have h1 : pull R (inv (sch.map f) ≫ sch.map f) F n x = 0 := by rw [pull_comp, hf, map_zero]
    simpa [pull_id] using h1

theorem EmptyH_of : LateralTheory.E.InjStepPf.EmptyH := by
  intro hH q X S p U hU i n x
  have : IsEmpty U := ⟨fun u => by
    have h : (u.1 : S) ∈ (U : Set S) := u.2
    rw [hU] at h; exact h⟩
  have : IsEmpty (overO p U) := ⟨fun z => isEmptyElim ((pullback.snd p U.ι).base z)⟩
  exact h_empty hH _ _ n x

end LateralTheory.E.EmptyH₂
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DiagCompPf
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagCompPf

theorem block_unique {A : Type} [CommRing A] (P R : PartDiagCut.Part A) (e : A) (he : e ∈ R.1) (a b : P.1)
    (ha : e * a.1 = e) (hb : e * b.1 = e) : a = b := by
  by_contra hne
  have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
  have h0 : a.1 * b.1 = 0 := P.orth a.1 a.2 b.1 b.2 hne'
  have : e = 0 := by
    calc e = e * a.1 * b.1 := by rw [ha, hb]
      _ = e * (a.1 * b.1) := by ring
      _ = 0 := by rw [h0, mul_zero]
  exact (R.idem e he).2 this

theorem par_trans {B : Type} [CommRing B] (I : Ideal B) {P Q R : PartDiagCut.Part (B ⧸ I)} (h1 : P ≤ Q) (h2 : Q ≤ R) (e : R.1) :
    par (h1.trans h2) e = par h1 (par h2 e) := by
  apply block_unique P R e.1 e.2
  · exact par_spec _ e
  · calc e.1 * (par h1 (par h2 e)).1 = e.1 * (par h2 e).1 * (par h1 (par h2 e)).1 := by rw [par_spec h2 e]
      _ = e.1 * ((par h2 e).1 * (par h1 (par h2 e)).1) := by ring
      _ = e.1 := by rw [par_spec h1 (par h2 e), par_spec h2 e]

theorem DiagComp_of : DiagComp := by
  intro B _ I P Q R h1 h2
  ext x e
  have key : ∀ (g g' : B →+* B), g = g' → ∀ (a b : P.1), a = b →
      ∀ (hA : S I a.1 ≤ (S I e.1).comap g) (hD : S I b.1 ≤ (S I e.1).comap g'),
      IsLocalization.map (M := S I a.1) (T := S I e.1) (Localization (S I e.1)) g hA (x a)
      = IsLocalization.map (M := S I b.1) (T := S I e.1) (Localization (S I e.1)) g' hD (x b) := by
    rintro g _ rfl a _ rfl hA hD; rfl
  simp only [stageMap, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  erw [IsLocalization.map_map]
  exact key _ _ (RingHom.id_comp _).symm _ _ (par_trans I h1 h2 e) _ _

end LateralTheory.E.DiagCompPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafInjSecInjOf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.InjectiveSections

abbrev MC (q : ℕ) := ModuleCat.{1} (ULift.{1} (ZMod q))

theorem sigma_const_mono (q : ℕ) {α : Type} {d d' : MC q} (f : d ⟶ d') [Mono f] :
    Mono (Limits.Sigma.map (fun _ : α => f)) := by
  have : Mono (Discrete.natTrans (fun (_ : Discrete α) => f) : Discrete.functor (fun _ : α => d) ⟶ Discrete.functor (fun _ : α => d')) :=
    @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ (fun _ => inferInstanceAs (Mono f))
  have : AB4OfSize.{0} (MC q) := AB4OfSize_shrink.{0, 1} (MC q)
  have : HasExactColimitsOfShape (Discrete α) (MC q) := AB4OfSize.ofShape α
  have : PreservesFiniteLimits (colim : (Discrete α ⥤ MC q) ⥤ MC q) := inferInstance
  exact (Functor.map_mono colim (Discrete.natTrans (fun (_ : Discrete α) => f) : Discrete.functor (fun _ : α => d) ⟶ Discrete.functor (fun _ : α => d')) : _)

instance evalLA_mono (q : ℕ) (U : Scheme.{0}) :
    (evaluationLeftAdjoint (MC q) (op U)).PreservesMonomorphisms where
  preserves {d d'} f _ := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ (fun t => ?_)
    change Mono (Limits.Sigma.desc (fun h : op U ⟶ t => f ≫ Sigma.ι (fun _ => d') h))
    have h : Limits.Sigma.desc (fun h : op U ⟶ t => f ≫ Sigma.ι (fun _ => d') h) = Limits.Sigma.map (fun _ => f) := by
      apply Limits.Sigma.hom_ext; intro j; rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_map]
    rw [h]
    exact sigma_const_mono q f

theorem eval_injective (q : ℕ) (M : Shv (ZMod q)) [Injective M] (U : Scheme.{0}) :
    Injective (M.obj.obj (op U)) := by
  have h1 : Injective ((sheafToPresheaf Scheme.etaleTopology.{0} (MC q)).obj M) :=
    Injective.injective_of_adjoint (sheafificationAdjunction Scheme.etaleTopology.{0} (MC q)) M
  have h2 : Injective M.obj := h1
  exact Injective.injective_of_adjoint (evaluationAdjunctionRight (MC q) (op U)) M.obj

end LateralTheory.E.InjectiveSections

open LateralTheory.E.InjectiveSections in
theorem LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj_of : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj := by
  intro q _ M _ U
  have h := eval_injective q M U
  exact Module.injective_module_of_injective_object (ULift.{1} (ZMod q)) (Sec M U)
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PartBPf
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.PartBPf

theorem comp_mem {B : Type} [CommRing B] (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (x : PiLocalization₂ I P)
    (hx : x ∈ I.map (βP I P)) (e : P.1) :
    x e ∈ I.map (algebraMap B (Localization (S I e.1))) := by
  have h1 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) x ∈
      (I.map (βP I P)).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) :=
    Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_map] at h1
  have h2 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e).comp (βP I P) =
      algebraMap B (Localization (S I e.1)) := by
    ext b; rfl
  rw [h2] at h1
  exact h1

theorem comp_unit {B : Type} [CommRing B] (I : Ideal B) (e : B ⧸ I) (y : Localization (S I e))
    (hy : y ∈ I.map (algebraMap B (Localization (S I e)))) : IsUnit (1 + y) := by
  obtain ⟨⟨⟨i, hi⟩, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff (S I e) _).1 hy
  simp only at h
  have hsi : s + i ∈ S I e := by
    obtain ⟨t, ht⟩ := hs
    refine ⟨t, ?_⟩
    have : Ideal.Quotient.mk I i = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hi
    rw [map_add (f := _), this, add_zero]; exact ht
  have hu : IsUnit ((1 + y) * algebraMap B _ s) := by
    rw [add_mul, one_mul, h, ← map_add (f := _)]
    exact IsLocalization.map_units (Localization (S I e)) ⟨s + i, hsi⟩
  exact isUnit_of_mul_isUnit_left hu

theorem PartB_of : LateralTheory.E.PartDiagCut.PartB := by
  intro B _ I P x hx
  rw [Pi.isUnit_iff]
  intro e
  exact comp_unit I e.1 (x e) (comp_mem I P x hx e)

end LateralTheory.E.PartBPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StalkSHSPf
noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial LateralTheory.E.t_E2Cut LateralTheory.E.FibStalkPf

namespace LateralTheory.E.StalkSHSPf

theorem germs (S : Scheme.{0}) (x : S) (c : ℕ → S.presheaf.stalk x) (s : Finset ℕ) :
    ∃ (U : S.Opens) (_ : IsAffineOpen U) (hx : x ∈ U) (f : ℕ → Γ(S, U)),
      ∀ i ∈ s, (S.presheaf.germ U x hx).hom (f i) = c i := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨U, hU, hx, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show x ∈ (⊤ : S.Opens) from trivial)
    exact ⟨U, hU, hx, fun _ => 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨U, hU, hx, f, hf⟩ := ih
    obtain ⟨V, hxV, g, hg⟩ := S.presheaf.exists_germ_eq (c a)
    obtain ⟨W, hW, hxW, hWUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show x ∈ U ⊓ V from ⟨hx, hxV⟩)
    refine ⟨W, hW, hxW, fun i => if i = a then (S.presheaf.map (homOfLE (hWUV.trans inf_le_right)).op).hom g
       else (S.presheaf.map (homOfLE (hWUV.trans inf_le_left)).op).hom (f i), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [if_true]
      rw [← hg, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    · have : i ≠ a := fun h => ha (h ▸ hi)
      simp only [this, if_false]
      rw [← hf i hi, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

theorem stalkAIC : StalkAIC := by
  intro S hS x p hm hd
  obtain ⟨U, hU, hx, f, hf⟩ := germs S x (fun i => p.coeff i) (Finset.range (p.natDegree + 1))
  have hl : p ∈ Polynomial.lifts (S.presheaf.germ U x hx).hom := by
    refine (lifts_iff_coeff_lifts p).2 fun i => ?_
    by_cases hi : i < p.natDegree + 1
    · exact ⟨f i, hf i (Finset.mem_range.2 hi)⟩
    · exact ⟨0, by rw [map_zero, coeff_eq_zero_of_natDegree_lt (by omega)]⟩
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  obtain ⟨r, hr⟩ := hS.2 U hU ⟨x, hx⟩ P hPm (by omega)
  exact ⟨(S.presheaf.germ U x hx).hom r, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hr, map_zero]⟩

end LateralTheory.E.StalkSHSPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.RestrPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf LateralTheory.E.StepKPf

namespace LateralTheory.E.RestrPf

theorem pull_zero {q : ℕ} {n i : ℤ} {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (y : Ht q (sch.obj C) n i)
    (h : pull _ (sch.map b) _ _ y = 0) : pull _ (sch.map (a ≫ b)) _ _ y = 0 := by
  rw [Functor.map_comp, pull_comp, h, map_zero]

theorem Restr_of : Restr := by
  intro h q J _ _ D c hc ha hcs hqs hu j0 X e U hU pU
  have : ∀ {a b : J} (g : a ⟶ b), IsAffineHom (D.map g) := ha
  let W : (D.obj j0).Opens := e.hom ⁻¹ᵁ U
  have haff : ∀ {a b : Over j0} (g : a ⟶ b), IsAffineHom ((opensDiagram D j0 W).map g) := fun g => inferInstance
  have hcpt : ∀ a : Over j0, CompactSpace ((opensDiagram D j0 W).obj a) := fun a =>
    isCompact_iff_compactSpace.mp ((D.map a.hom).isCompact_preimage hU)
  have hqs' : ∀ a : Over j0, QuasiSeparatedSpace ((opensDiagram D j0 W).obj a) := fun a => by
    have := hqs a.left
    exact (D.map a.hom ⁻¹ᵁ W).isOpen.isOpenEmbedding_subtypeVal.quasiSeparatedSpace
  have hu' : ∀ a : Over j0, IsUnit (q : Γ((opensDiagram D j0 W).obj a, ⊤)) := fun a => by
    show IsUnit (q : Γ((D.map a.hom ⁻¹ᵁ W).toScheme, ⊤))
    simpa using (hu a.left).map (Scheme.Hom.appTop (Scheme.Opens.ι (D.map a.hom ⁻¹ᵁ W))).hom
  have hiso : Nonempty ((opensDiagram D j0 W).obj (Over.mk (𝟙 j0)) ≅ U.toScheme) := by
    refine ⟨(D.obj j0).isoOfEq ?_ ≪≫ asIso (e.hom ∣_ U)⟩
    simp [W]
  have P := pU q (opensDiagram D j0 W) (opensCone D c j0 W) (isLimitOpensCone D c hc j0 W) haff hcpt hqs' hu'
    (Over.mk (𝟙 j0)) hiso
  intro n i
  obtain ⟨P1, P2⟩ := P n i
  refine ⟨fun x => ?_, fun k f y hy => ?_⟩
  · obtain ⟨j', y, hy⟩ := P1 x
    exact ⟨j'.left, j'.hom, y, hy⟩
  · obtain ⟨k', g', hg'⟩ := P2 (Over.mk f) y hy
    refine ⟨k'.left, g'.left, ?_⟩
    have hle : lv D e U (g'.left ≫ f) ≤ D.map k'.hom ⁻¹ᵁ W := by
      rw [← Over.w g']; exact le_rfl
    let ι0 : (lv D e U (g'.left ≫ f)).toScheme ⟶ (opensDiagram D j0 W).obj k' := (D.obj k'.left).homOfLE hle
    have heq : rD D e U f g'.left = ι0 ≫ (opensDiagram D j0 W).map g' := by
      apply (cancel_mono (lv D e U f).ι).mp
      have e1 : (opensDiagram D j0 W).map g' ≫ (D.map (Over.mk f).hom ⁻¹ᵁ W).ι =
          (D.map k'.hom ⁻¹ᵁ W).ι ≫ D.map g'.left := Scheme.Hom.resLE_comp_ι _ _
      have e2 : ι0 ≫ (D.map k'.hom ⁻¹ᵁ W).ι = (lv D e U (g'.left ≫ f)).ι := Scheme.homOfLE_ι _ _
      calc rD D e U f g'.left ≫ (lv D e U f).ι = (lv D e U (g'.left ≫ f)).ι ≫ D.map g'.left :=
            Scheme.Hom.resLE_comp_ι _ _
        _ = (ι0 ≫ (D.map k'.hom ⁻¹ᵁ W).ι) ≫ D.map g'.left := by rw [e2]
        _ = ι0 ≫ ((D.map k'.hom ⁻¹ᵁ W).ι ≫ D.map g'.left) := Category.assoc _ _ _
        _ = ι0 ≫ ((opensDiagram D j0 W).map g' ≫ (D.map (Over.mk f).hom ⁻¹ᵁ W).ι) :=
            congrArg (fun t => ι0 ≫ t) e1.symm
        _ = (ι0 ≫ (opensDiagram D j0 W).map g') ≫ (lv D e U f).ι := (Category.assoc _ _ _).symm
    rw [heq]; exact pull_zero ι0 ((opensDiagram D j0 W).map g') y hg'

end LateralTheory.E.RestrPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StdChartsOf
section -- merged from Development.EtaleCohomology.EtaleSheaves.ChartsPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChartsPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev D (i : Fin 2) : P1.Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

lemma X_mem (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℤ i)

lemma D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem i) one_pos

lemma D_cover : ⨆ i, D i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · exact fun i => ⟨1, X_mem i⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) := by
      rw [MvPolynomial.adjoin_range_X]; trivial
    have h : Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) ≤
        (Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ))).restrictScalars ℤ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact h hx

end LateralTheory.E.ChartsPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StdChartsProof₂

theorem StdCharts_of : LateralTheory.E.StandardEtaleChartsMultivariableHensel.StdCharts := by
  intro A _ _ Z p hp
  obtain ⟨L, u, l, hu, ⟨hl, f, hf⟩, hul⟩ := hp
  have hf' : IsAffineHom f := MorphismProperty.of_isPullback hf.flip inferInstance
  let g : Z ⟶ P1 := u ≫ f
  have hU : ∀ i, IsAffineOpen (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D i) := fun i => (LateralTheory.E.ChartsPf.D_affine i).preimage g
  refine ⟨g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0, g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1, (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 0).ι,
    (g ⁻¹ᵁ LateralTheory.E.ChartsPf.D 1).ι, inferInstance, inferInstance, hU 0, hU 1, ?_, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hx : g x ∈ (⨆ i, LateralTheory.E.ChartsPf.D i : P1.Opens) := by rw [LateralTheory.E.ChartsPf.D_cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · refine ⟨L, u, l, f, hu, hl, hf, hul, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]; rfl
    · rw [Scheme.Opens.range_ι]; rfl

end LateralTheory.E.StdChartsProof₂
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.NonunitCase
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.AlgGlue₂

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mS_mul (S : Subalgebra A K) {x b : K} (hx : x ∈ mS S) (hb : b ∈ S) : x * b ∈ mS S := by
  unfold mS at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha s hs
    rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul ha (S.mul_mem hs hb)
  · intro x y hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy

theorem unit_case (S : Subalgebra A K) {u h e : K} (hu : u ∈ S) (hh : h ∈ S) (huh : u * h = 1)
    (he : e ∈ S) (hue : u - e ∈ mS S) (hee : e * e - e ∈ mS S) : e - 1 ∈ mS S := by
  have key : e - 1 = (e * e - e) * h + (u - e) * ((e - 1) * h) := by
    linear_combination (1 - e) * huh
  rw [key]
  exact Submodule.add_mem _ (mS_mul S hee hh)
    (mS_mul S hue (S.mul_mem (S.sub_mem he (S.one_mem)) hh))

theorem nonunit_case (S : Subalgebra A K) {u h e : K} (hu : u ∈ S) (hh : h ∈ S) (huh : (1 - u) * h = 1)
    (he : e ∈ S) (hue : u - e ∈ mS S) (hee : e * e - e ∈ mS S) : e ∈ mS S := by
  have h1 := unit_case S (u := 1 - u) (e := 1 - e) (S.sub_mem S.one_mem hu) hh huh
    (S.sub_mem S.one_mem he)
    (by
      have : (1 - u) - (1 - e) = (u - e) * (-1) := by ring
      rw [this]; exact mS_mul S hue (S.neg_mem S.one_mem))
    (by
      have : (1 - e) * (1 - e) - (1 - e) = e * e - e := by ring
      rw [this]; exact hee)
  have : e = (1 - e - 1) * (-1) := by ring
  rw [this]; exact mS_mul S h1 (S.neg_mem S.one_mem)

theorem AlgGlue_of (hL : IdemLift) (hF : LateralTheory.E.LZProperCut.LZHensFinite) : AlgGlue := by
  intro A _ _ _ K _ _ B C t hc hint e f hef
  obtain ⟨heB, hfC, hee, hff, hd⟩ := hef
  obtain ⟨g, hgB, hgC, hge, hgf⟩ := hL A K B C t hc e f ⟨heB, hfC, hee, hff, hd⟩
  set R : Subalgebra A K := Algebra.adjoin A {g} with hR
  have hRB : R ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgB)
  have hRC : R ≤ C := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgC)
  have hgi : IsIntegral A g := hint g hgB hgC
  have : Module.Finite A R := Algebra.finite_adjoin_simple_of_isIntegral hgi
  have : IsDomain R := inferInstance
  have : ConnectedSpace ↑(Spec (CommRingCat.of R)) := by
    change ConnectedSpace (PrimeSpectrum R)
    infer_instance
  have : IsLocalRing R := hF A R this
  have hgR : g ∈ R := Algebra.self_mem_adjoin_singleton A g
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨g, hgR⟩ : R) with hu | hu
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : g * (v : K) = 1 := by
      have := congrArg Subtype.val hv; simpa using this
    right
    exact ⟨unit_case B hgB (hRB v.2) hv' heB hge hee, unit_case C hgC (hRC v.2) hv' hfC hgf hff⟩
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : (1 - g) * (v : K) = 1 := by
      have := congrArg Subtype.val hv; simpa using this
    left
    exact ⟨nonunit_case B hgB (hRB v.2) hv' heB hge hee, nonunit_case C hgC (hRC v.2) hv' hfC hgf hff⟩

end LateralTheory.E.AlgGlue₂
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocACPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut LateralTheory.E.CompCut

namespace LateralTheory.E.LocACPf

variable {W : Type} [CommRing W]

lemma idem_split {e : W} (he : IsIdempotentElem e) : e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, he.eq, sub_self]

lemma map_zero_of_mem (hW : ProdACF W) (p : Ideal W) [p.IsPrime] {a : W} (ha : a ∈ p) :
    algebraMap W (Localization.AtPrime p) a = 0 := by
  obtain ⟨e, u, he, hu, rfl⟩ := hW.2 a
  have heq : e ∈ p := by
    rcases (inferInstance : p.IsPrime).mem_or_mem ha with h | h
    · exact h
    · exact absurd (p.eq_top_of_isUnit_mem h hu) (inferInstance : p.IsPrime).ne_top
  have h1 : (1 - e) ∈ p.primeCompl := by
    intro h
    have : (1 : W) ∈ p := by simpa using p.add_mem heq h
    exact (inferInstance : p.IsPrime).ne_top ((Ideal.eq_top_iff_one _).2 this)
  rw [IsLocalization.map_eq_zero_iff p.primeCompl]
  refine ⟨⟨1 - e, h1⟩, ?_⟩
  show (1 - e) * (e * u) = 0
  rw [← mul_assoc, mul_comm (1 - e), idem_split he, zero_mul]

lemma map_idem_one (hW : ProdACF W) (p : Ideal W) [p.IsPrime] {e : W} (he : IsIdempotentElem e) (hne : e ∉ p) :
    algebraMap W (Localization.AtPrime p) e = 1 := by
  have h1 : (1 - e) ∈ p := by
    rcases (inferInstance : p.IsPrime).mem_or_mem (show e * (1 - e) ∈ p by rw [idem_split he]; exact p.zero_mem) with h | h
    · exact absurd h hne
    · exact h
  have := map_zero_of_mem hW p h1
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this.symm

lemma surj (hW : ProdACF W) (p : Ideal W) [p.IsPrime] :
    Function.Surjective (algebraMap W (Localization.AtPrime p)) := by
  intro x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  obtain ⟨e, u, he, hu, hs⟩ := hW.2 (s : W)
  have hne : e ∉ p := fun h => s.2 (hs ▸ p.mul_mem_right u h)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  refine ⟨a * e * v, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, hs]
  have : a * e * v * (e * u) = a * e * e * (v * u) := by ring
  rw [this, hv, mul_one, mul_assoc, he.eq, map_mul, map_idem_one hW p he hne, mul_one]

theorem LocAC_of : LocAC := by
  intro W _ hW q
  have := q.isPrime
  set p := q.asIdeal
  constructor
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    exact map_zero_of_mem hW p ha
  · intro P hP hdeg
    have hl : P ∈ Polynomial.lifts (algebraMap W (Localization.AtPrime p)) := by
      obtain ⟨Q, hQ⟩ := Polynomial.map_surjective _ (surj hW p) P
      exact Polynomial.mem_lifts _ |>.2 ⟨Q, hQ⟩
    obtain ⟨Q, hQ, hdQ, hmQ⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
    obtain ⟨r, hr⟩ := hW.1 Q hmQ (hdQ ▸ hdeg)
    refine ⟨algebraMap W _ r, ?_⟩
    rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]

end LateralTheory.E.LocACPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PartDirectedPf
namespace LateralTheory.E.PartDirectedPf

variable {A : Type} [CommRing A]

theorem prod_eq_zero_of_ne {a b c d : A} (P Q : PartDiagCut.Part A)
    (ha : a ∈ P.blocks) (hb : b ∈ Q.blocks) (hc : c ∈ P.blocks) (hd : d ∈ Q.blocks)
    (hne : (a, b) ≠ (c, d)) : (a * b) * (c * d) = 0 := by
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h; exact hne (by rw [hac, h])
    have := Q.orth b hb d hd hbd
    calc a * b * (c * d) = a * c * (b * d) := by ring
      _ = 0 := by rw [this, mul_zero]
  · have := P.orth a ha c hc hac
    calc a * b * (c * d) = a * c * (b * d) := by ring
      _ = 0 := by rw [this, zero_mul]

open Classical in
noncomputable def meet (P Q : PartDiagCut.Part A) : PartDiagCut.Part A where
  blocks := ((P.blocks ×ˢ Q.blocks).filter (fun x => x.1 * x.2 ≠ 0)).image (fun x => x.1 * x.2)
  idem := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hne⟩, rfl⟩ := he
    exact ⟨(P.idem a ha).1.mul (Q.idem b hb).1, hne⟩
  orth := by
    intro e he e' he' hee
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he he'
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
    obtain ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, _⟩, rfl⟩ := he'
    refine prod_eq_zero_of_ne P Q ha hb hc hd ?_
    intro h; apply hee; simp only [Prod.mk.injEq] at h; rw [h.1, h.2]
  sum_eq := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter_ne_zero, Finset.sum_product, ← Finset.sum_mul_sum,
        P.sum_eq, Q.sum_eq, mul_one]
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
      by_contra hne
      have h0 := prod_eq_zero_of_ne P Q hx.1.1 hx.1.2 hy.1.1 hy.1.2 hne
      change x.1 * x.2 = y.1 * y.2 at hxy
      rw [← hxy] at h0
      have hid : IsIdempotentElem (x.1 * x.2) := (P.idem _ hx.1.1).1.mul (Q.idem _ hx.1.2).1
      exact hx.2 (by rw [← hid.eq]; exact h0)

theorem le_meet_left (P Q : PartDiagCut.Part A) : P ≤ meet P Q := by
  intro e he
  simp only [meet, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
  refine ⟨a, ha, ?_⟩
  calc a * b * a = a * a * b := by ring
    _ = a * b := by rw [(P.idem a ha).1.eq]

theorem le_meet_right (P Q : PartDiagCut.Part A) : Q ≤ meet P Q := by
  intro e he
  simp only [meet, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
  refine ⟨b, hb, ?_⟩
  calc a * b * b = a * (b * b) := by ring
    _ = a * b := by rw [(Q.idem b hb).1.eq]

theorem part_nonempty (A : Type) [CommRing A] : Nonempty (PartDiagCut.Part A) := by
  by_cases h : Nontrivial A
  · exact ⟨{ blocks := {1}
             idem := by intro e he; rw [Finset.mem_singleton] at he; subst he; exact ⟨IsIdempotentElem.one, one_ne_zero⟩
             orth := by intro e he e' he' hne; rw [Finset.mem_singleton] at he he'; exact absurd (he.trans he'.symm) hne
             sum_eq := by simp }⟩
  · rw [not_nontrivial_iff_subsingleton] at h
    exact ⟨{ blocks := ∅
             idem := by simp
             orth := by simp
             sum_eq := Subsingleton.elim _ _ }⟩

theorem PartDirected_of : LateralTheory.E.PartDiagCut.PartDirected := by
  intro A _
  exact ⟨⟨fun P Q => ⟨meet P Q, le_meet_left P Q, le_meet_right P Q⟩⟩, part_nonempty A⟩

end LateralTheory.E.PartDirectedPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ProdPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.ProdPf

theorem iterLine_of_isPullback {S P : Scheme.{0}} {q : P ⟶ S} (hq : IterLine q) :
    ∀ {X P' : Scheme.{0}} (g : X ⟶ S) (a : P' ⟶ P) (q' : P' ⟶ X), IsPullback a q' q g → IterLine q' := by
  induction hq with
  | iso e he =>
    intro X P' g a q' h
    have : IsIso (pullback.snd e g) := inferInstance
    have hq' : q' = h.isoPullback.hom ≫ pullback.snd e g := (IsPullback.isoPullback_hom_snd h).symm
    rw [hq']
    exact IterLine.iso _ inferInstance
  | comp l k hl _ ih =>
    intro X P' g a q' h
    have w : q' ≫ g = (a ≫ l) ≫ k := by rw [Category.assoc, ← h.w]
    let m := pullback.lift q' (a ≫ l) w
    have hb : IsPullback (pullback.snd g k) (pullback.fst g k) k g := (IsPullback.of_hasPullback g k).flip
    have e1 : m ≫ pullback.fst g k = q' := pullback.lift_fst _ _ _
    have e2 : m ≫ pullback.snd g k = a ≫ l := pullback.lift_snd _ _ _
    have hs : IsPullback a (m ≫ pullback.fst g k) (l ≫ k) g := by
      rw [e1]; exact h
    have ht : IsPullback a m l (pullback.snd g k) := IsPullback.of_bot hs e2.symm hb
    have hm : IsLine m := hl.bc ht
    have e : q' = m ≫ pullback.fst g k := e1.symm
    rw [e]
    exact IterLine.comp _ _ hm (ih g (pullback.snd g k) (pullback.fst g k) hb)

theorem exists_widePullback_of_iteratedLine (hI : IterComp) {S : Scheme.{0}} : ∀ (n : ℕ) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S),
    (∀ j, IterLine (qj j)) →
    ∃ (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j), IterLine q ∧ (∀ j, π j ≫ qj j = q) ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
        ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j := by
  intro n
  induction n with
  | zero =>
    intro Pj qj _
    refine ⟨S, 𝟙 S, fun j => j.elim0, IterLine.iso _ inferInstance, fun j => j.elim0, ?_⟩
    intro T t f _
    refine ⟨t, ⟨by simp, fun j => j.elim0⟩, ?_⟩
    rintro g ⟨hg, -⟩
    simpa using hg
  | succ n ih =>
    intro Pj qj hqj
    obtain ⟨P0, q0, π0, hq0, hπ0, hU0⟩ := ih (fun j => Pj j.succ) (fun j => qj j.succ) (fun j => hqj j.succ)
    have hfst : IterLine (pullback.fst q0 (qj 0)) :=
      iterLine_of_isPullback (hqj 0) q0 (pullback.snd q0 (qj 0)) (pullback.fst q0 (qj 0))
        (IsPullback.of_hasPullback q0 (qj 0)).flip
    let π : ∀ j, pullback q0 (qj 0) ⟶ Pj j :=
      Fin.cases (motive := fun j => pullback q0 (qj 0) ⟶ Pj j) (pullback.snd q0 (qj 0))
        (fun j => pullback.fst q0 (qj 0) ≫ π0 j)
    have hπ0' : π 0 = pullback.snd q0 (qj 0) := rfl
    have hπs : ∀ j : Fin n, π j.succ = pullback.fst q0 (qj 0) ≫ π0 j := fun j => rfl
    refine ⟨pullback q0 (qj 0), pullback.fst q0 (qj 0) ≫ q0, π, hI _ _ hfst hq0, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [hπ0', ← pullback.condition]
      · rw [hπs, Category.assoc, hπ0]
    · intro T t f hf
      obtain ⟨g0, ⟨hg0q, hg0π⟩, hu⟩ := hU0 t (fun j => f j.succ) (fun j => hf j.succ)
      have w : g0 ≫ q0 = f 0 ≫ qj 0 := by rw [hg0q, hf 0]
      refine ⟨pullback.lift g0 (f 0) w, ⟨?_, ?_⟩, ?_⟩
      · rw [← Category.assoc, pullback.lift_fst, hg0q]
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · rw [hπ0', pullback.lift_snd]
        · rw [hπs, ← Category.assoc, pullback.lift_fst, hg0π]
      · rintro g' ⟨hg'q, hg'π⟩
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          apply hu
          refine ⟨by rw [Category.assoc, hg'q], fun j => ?_⟩
          rw [Category.assoc, ← hπs, hg'π]
        · rw [pullback.lift_snd, ← hπ0', hg'π]

theorem Prod_of (hI : IterComp) : LateralTheory.E.ChowGraphCut.Prod := by
  intro S n Pj qj hq
  exact exists_widePullback_of_iteratedLine hI n Pj qj hq

end LateralTheory.E.ProdPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafBaseChangeFieldPf
noncomputable section
open Polynomial IntermediateField

namespace LateralTheory.E.LeafBaseChangeFieldPf

def ratMap (F G : Type) [Field F] [Field G] [Algebra F G] : RatFunc F →+* RatFunc G :=
  RatFunc.liftRingHom ((algebraMap G[X] (RatFunc G)).comp (Polynomial.mapRingHom (algebraMap F G))) (show
      nonZeroDivisors F[X] ≤ Submonoid.comap ((algebraMap G[X] (RatFunc G)).comp
        (Polynomial.mapRingHom (algebraMap F G))) (nonZeroDivisors (RatFunc G)) from by
    intro p hp
    rw [Submonoid.mem_comap]
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom]
    intro h
    apply hp0
    have h1 := RatFunc.algebraMap_injective G (h.trans (map_zero _).symm)
    exact (Polynomial.map_eq_zero_iff (algebraMap F G).injective).1 h1)

lemma ratMap_algebraMap (F G : Type) [Field F] [Field G] [Algebra F G] (f : F) :
    ratMap F G (algebraMap F (RatFunc F) f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
  have e1 : algebraMap F (RatFunc F) f = algebraMap F[X] (RatFunc F) (C f) / algebraMap F[X] (RatFunc F) 1 := by
    rw [map_one, div_one, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [e1, ratMap, RatFunc.liftRingHom_apply_div]
  simp [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

lemma mem_adjoin_of_ratFunc {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] (x : RatFunc G) :
    algebraMap (RatFunc G) L x ∈ G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := by
  have key : ∀ p : G[X], algebraMap (RatFunc G) L (algebraMap G[X] (RatFunc G) p) =
      aeval (algebraMap (RatFunc G) L RatFunc.X) p := by
    intro p
    rw [aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]
  rw [← RatFunc.num_div_denom x, map_div₀, key, key]
  exact div_mem (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))
    (algebra_adjoin_le_adjoin G _ (aeval_mem_adjoin_singleton G _))

lemma transc_X_image {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] : Transcendental G (algebraMap (RatFunc G) L RatFunc.X) := by
  rw [transcendental_iff_injective]
  intro p q h
  rw [aeval_algebraMap_apply, aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap,
    RatFunc.aeval_X_left_eq_algebraMap] at h
  exact RatFunc.algebraMap_injective G ((algebraMap (RatFunc G) L).injective h)

lemma finite_over_adjoin {G L : Type} [Field G] [Field L] [Algebra (RatFunc G) L] [Algebra G L]
    [IsScalarTower G (RatFunc G) L] [Module.Finite (RatFunc G) L] :
    FiniteDimensional G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L := by
  let c : RatFunc G →+* G⟮algebraMap (RatFunc G) L RatFunc.X⟯ :=
    (algebraMap (RatFunc G) L).codRestrict _ mem_adjoin_of_ratFunc
  letI : Algebra (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ := c.toAlgebra
  haveI : IsScalarTower (RatFunc G) G⟮algebraMap (RatFunc G) L RatFunc.X⟯ L :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact Module.Finite.of_restrictScalars_finite (RatFunc G) _ L

end LateralTheory.E.LeafBaseChangeFieldPf

open LateralTheory.E.LeafBaseChangeFieldPf in
theorem LateralTheory.E.LeafBaseChangeFieldPf.LeafBaseChangeField_of : LateralTheory.E.LeafCurveVCut.LeafBaseChangeField := by
  intro F G K _ _ _ _ _ t ht hfin
  let e := RatFunc.algEquivOfTranscendental t ht
  let h : F⟮t⟯ →+* RatFunc G := (ratMap F G).comp e.symm.toRingHom
  letI : Algebra F⟮t⟯ (RatFunc G) := h.toAlgebra
  haveI : Nontrivial (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ h.injective
      (algebraMap F⟮t⟯ K).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct F⟮t⟯ (RatFunc G) K)
  letI : Field (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K) :=
    Module.Finite.base_change F⟮t⟯ (RatFunc G) K
  haveI : Module.Finite (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (RatFunc G) M).toLinearMap Ideal.Quotient.mk_surjective
  haveI : IsScalarTower G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M) := inferInstance
  refine ⟨TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M, inferInstance, inferInstance,
    algebraMap (RatFunc G) _ RatFunc.X,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight (R := F⟮t⟯) (A := RatFunc G) (B := K)).toRingHom,
    transc_X_image, finite_over_adjoin, ?_⟩
  ext f
  have h1 : h (algebraMap F F⟮t⟯ f) = algebraMap G (RatFunc G) (algebraMap F G f) := by
    show ratMap F G (e.symm (algebraMap F F⟮t⟯ f)) = _
    rw [AlgEquiv.commutes]
    exact ratMap_algebraMap F G f
  rw [RingHom.comp_apply, RingHom.comp_apply, IsScalarTower.algebraMap_apply F F⟮t⟯ K, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes, IsScalarTower.algebraMap_apply F⟮t⟯ (RatFunc G)]
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply G (RatFunc G) (TensorProduct F⟮t⟯ (RatFunc G) K ⧸ M), ← h1]
  rfl
end
end

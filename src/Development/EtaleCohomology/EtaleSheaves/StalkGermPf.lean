module

public import Development.EtaleCohomology.EtaleSheaves.SHTensorPf
public import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence
public import Development.EtaleCohomology.EtaleSheaves.FirstChernNaturality
public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.StalkGermPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.StalkGermPf

abbrev toO {X S : Scheme.{0}} (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback p (S.fromSpecStalk s) ⟶ overO p U :=
  pullback.map p (S.fromSpecStalk s) p U.ι (𝟙 _) (U.fromSpecStalkOfMem s hs) (𝟙 _) (by simp) (by simp)

def StalkCont : Prop := Cont → Hyp → ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
  [QuasiCompact p] [QuasiSeparated p], IsUnit (q : Γ(S, ⊤)) → ∀ (i n : ℤ) (s : S),
  (∀ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i), pull _ (sch.map (toO p s U hs)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ z : Ht q (sch.obj (pullback p (S.fromSpecStalk s))) n i, ∃ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i),
    pull _ (sch.map (toO p s U hs)) _ _ x = z)

variable {Y X S : Scheme.{0}}

theorem pull_mc {q : ℕ} {n i : ℤ} {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Ht q (sch.obj C) n i) :
    pull _ (sch.map (a ≫ b)) (tw q i) n x = pull _ (sch.map a) _ _ (pull _ (sch.map b) _ _ x) := by
  rw [Functor.map_comp, pull_comp]

theorem toO_res (p : X ⟶ S) (s : S) {V U : S.Opens} (h : V ≤ U) (hV : s ∈ V) :
    toO p s V hV ≫ resO p h = toO p s U (h hV) := by
  have e : V.fromSpecStalkOfMem s hV ≫ S.homOfLE h = U.fromSpecStalkOfMem s (h hV) := by
    rw [← cancel_mono U.ι]; simp
  simp only [toO, resO]; rw [pullback.map_comp]; congr 1 <;> simp [e]

theorem toO_f (f : Y ⟶ X) (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ toO p s U hs =
      toO (f ≫ p) s U hs ≫ fO f p U := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_f (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_res (p : X ⟶ S) {W V U : S.Opens} (h1 : W ≤ V) (h2 : V ≤ U) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem StalkGerm_of (hS : StalkCont) : StalkGerm := by
  intro hC hH q Y X S f p _ _ _ _ _ _ hq i s he n
  obtain ⟨ia, sa⟩ := hS hC hH q p hq i n s
  obtain ⟨ib, -⟩ := hS hC hH q (f ≫ p) hq i n s
  have hb := he n
  constructor
  · intro U hs x hx
    apply ia U hs x
    apply hb.1
    rw [map_zero, ← pull_mc, toO_f, pull_mc, hx, map_zero]
  · intro U hs y
    obtain ⟨w, hw⟩ := hb.2 (pull _ (sch.map (toO (f ≫ p) s U hs)) _ _ y)
    obtain ⟨U1, hs1, x1, hx1⟩ := sa w
    have hs2 : s ∈ U ⊓ U1 := ⟨hs, hs1⟩
    have hx2' : pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n
        (pull (ZMod q) (sch.map (resO p (inf_le_right : U ⊓ U1 ≤ U1))) (tw q i) n x1) = w := by
      rw [← pull_mc, toO_res]; exact hx1
    obtain ⟨x2, hx2⟩ : ∃ x2 : H (ZMod q) (sch.obj (overO p (U ⊓ U1))) (tw q i) n,
        pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n x2 = w := ⟨_, hx2'⟩
    have e1 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _ (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) =
        pull _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _)
          (by simp) (by simp))) (tw q i) n (pull _ (sch.map (toO p s (U ⊓ U1) hs2)) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, toO_f]
    have e2 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (toO (f ≫ p) s U hs)) (tw q i) n y := by
      rw [← pull_mc, toO_res]
    have h0 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2 -
          pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) = 0 := by
      rw [map_sub, e1, e2, hx2, hw, sub_self]
    obtain ⟨V, hV, hsV, hd⟩ := ib _ hs2 _ h0
    refine ⟨V, hV.trans inf_le_left, hsV, pull _ (sch.map (resO p hV)) _ _ x2, ?_⟩
    rw [map_sub, sub_eq_zero] at hd
    have g1 : pull _ (sch.map (fO f p V)) _ _ (pull _ (sch.map (resO p hV)) _ _ x2) =
        pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, res_f]
    have g2 : pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (resO (f ≫ p) (hV.trans inf_le_left))) (tw q i) n y := by
      rw [← pull_mc, res_res]
    rw [g1, hd, g2]

end LateralTheory.E.StalkGermPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AICOpenPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial

namespace LateralTheory.E.AICOpenPf
open LateralTheory.E.t_E2Cut LateralTheory.E.SteinPf

theorem roots_in {A K : Type} [CommRing A] [IsDomain A] [CommRing K] [IsDomain K] (φ : A →+* K) (hA : AIC A) :
    ∀ n (p : A[X]), p.natDegree = n → p.Monic → ∀ β : K, (p.map φ).eval β = 0 → ∃ a, φ a = β := by
  intro n
  induction n with
  | zero =>
    intro p hd hm β hβ
    have : p = 1 := hm.natDegree_eq_zero.mp hd
    subst this; simp at hβ
  | succ n ih =>
    intro p hd hm β hβ
    obtain ⟨a, ha⟩ := hA p hm (by omega)
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqm : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hm)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hfac, Polynomial.map_mul, eval_mul, mul_eq_zero] at hβ
    rcases hβ with h | h
    · refine ⟨a, ?_⟩
      simp at h; rw [sub_eq_zero] at h; exact h.symm
    · exact ih _ hqd hqm β h

theorem gtf_res {Z : Scheme.{0}} [IsIntegral Z] {U W : Z.Opens} (i : U ⟶ W) [Nonempty U] [Nonempty W] (s : Γ(Z, W)) :
    Z.germToFunctionField U (Z.presheaf.map i.op s) = Z.germToFunctionField W s := by
  simp only [Scheme.germToFunctionField]
  rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res]

theorem gtf_res_hom {Z : Scheme.{0}} [IsIntegral Z] {U W : Z.Opens} (i : U ⟶ W) [Nonempty U] [Nonempty W] :
    (Z.germToFunctionField U).hom.comp (Z.presheaf.map i.op).hom = (Z.germToFunctionField W).hom := by
  ext s; exact gtf_res i s

theorem AICOpen_of : AICOpen := by
  intro Z hZ W hW p hm hd
  have : IsIntegral Z := hZ.1
  have : Nonempty W := ⟨⟨_, hW.some_mem⟩⟩
  have hcov : ∀ x : W, ∃ U : Z.Opens, IsAffineOpen U ∧ (x : Z) ∈ U ∧ U ≤ W := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.isOpen
    exact ⟨U, hU, hxU, hUW⟩
  choose U hUa hxU hUW using hcov
  have hne : ∀ x : W, Nonempty (U x) := fun x => ⟨⟨_, hxU x⟩⟩
  let ψ := Z.germToFunctionField W

  have hroot : ∀ x : W, ∃ β : Z.functionField, (p.map ψ.hom).eval β = 0 := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hZ.2 _ (hUa x) ⟨_, hxU x⟩
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    obtain ⟨r, hr⟩ := hA (p.map ρ) (hm.map ρ) (by rw [hm.natDegree_map]; exact hd)
    refine ⟨Z.germToFunctionField (U x) r, ?_⟩
    rw [← gtf_res_hom (homOfLE (hUW x)), ← Polynomial.map_map, Polynomial.eval_map_apply, hr, map_zero]
  obtain ⟨β, hβ⟩ := hroot ⟨_, hW.some_mem⟩
  have hsec : ∀ x : W, ∃ t : Γ(Z, U x), Z.germToFunctionField (U x) t = β := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hZ.2 _ (hUa x) ⟨_, hxU x⟩
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    exact roots_in (Z.germToFunctionField (U x)).hom hA _ (p.map ρ) rfl (hm.map ρ) β
      (by rw [Polynomial.map_map, gtf_res_hom]; exact hβ)
  choose sf hsf using hsec
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have := hne i; have := hne j
    have hij : ((U i ⊓ U j : Z.Opens) : Set Z).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨_, hxU i⟩ ⟨_, hxU j⟩
    have : Nonempty (U i ⊓ U j : Z.Opens) := ⟨⟨_, hij.some_mem⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.germToFunctionField _ (Z.presheaf.map _ (sf i)) = Z.germToFunctionField _ (Z.presheaf.map _ (sf j))
    rw [gtf_res, gtf_res, hsf, hsf]
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (U := U) (V := W) (iUV := fun x => homOfLE (hUW x))
    (hcover := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU _⟩) (sf := sf) (h := hcompat)
  have hsβ : ψ s = β := by
    have h0 := hs ⟨_, hW.some_mem⟩
    have := hne ⟨_, hW.some_mem⟩
    rw [← hsf ⟨_, hW.some_mem⟩, ← gtf_res (homOfLE (hUW ⟨_, hW.some_mem⟩)) s]
    exact congrArg _ h0
  obtain ⟨t, ht⟩ : ∃ t : Γ(Z, W), ψ t = β := ⟨s, hsβ⟩
  refine ⟨t, Z.germToFunctionField_injective W ?_⟩
  rw [map_zero]
  have key : ψ.hom (p.eval t) = (p.map ψ.hom).eval (ψ.hom t) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  change ψ.hom (p.eval t) = 0
  rw [key]; change (p.map ψ.hom).eval (ψ t) = 0
  rw [ht]; exact hβ

end LateralTheory.E.AICOpenPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CechSigmaOf
section -- merged from Development.EtaleCohomology.EtaleSheaves.EqvOfCompRight
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigmaProof

abbrev cov {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    (∐ fun j => (V j).toScheme) ⟶ O.toScheme :=
  Sigma.desc fun j => X.homOfLE (hV j)

theorem pre_le {Y X : Scheme.{0}} (g : Y ⟶ X) {A B : X.Opens} (h : A ≤ B) : g ⁻¹ᵁ A ≤ g ⁻¹ᵁ B :=
  fun _ hx => h hx

theorem sq_cov {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Limits.Sigma.map (fun j => g ∣_ V j) ≫ cov O V hV = cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)) ≫ g ∣_ O := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [← cancel_mono O.ι]
  simp [cov, morphismRestrict_ι]

theorem cov_surj {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
    (hc : O ≤ ⨆ j, V j) : Surjective (cov O V hV) := by
  apply Surjective.sigmaDesc_of_union_range_eq_univ
  refine Set.eq_univ_iff_forall.2 fun x => ?_
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc x.2)
  refine Set.mem_iUnion.2 ⟨j, ⟨⟨x.1, hj⟩, ?_⟩⟩
  apply Subtype.ext
  exact congr($(X.homOfLE_ι (hV j)) ⟨x.1, hj⟩)

instance cov_smooth {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Smooth (cov O V hV) :=
  haveI : IsZariskiLocalAtSource @Smooth.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{0}) (Q := RingHom.Smooth)
  IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0}) fun _ => inferInstance

def arr {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Arrow.mk (yoneda.map (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)))) ⟶
      Arrow.mk (yoneda.map (cov O V hV)) :=
  Arrow.homMk (yoneda.map (Limits.Sigma.map fun j => g ∣_ V j)) (yoneda.map (g ∣_ O))
    (by simp only [Arrow.mk_hom]; rw [← Functor.map_comp, ← Functor.map_comp, sq_cov g O V hV])

def LevelIso : Prop := ∀ {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
  (n : ℕ), Nonempty (Arrow.mk ((Arrow.mapCechNerve (arr g O V hV)).app (op (SimplexCategory.mk n))) ≅
    Arrow.mk (yoneda.map (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k)))))

section
variable {R : Type} [CommRing R] {F : Shv R}

theorem eqv_of_arrowIso {E E' E₁ E₁' : Spc} {f : E ⟶ E'} {f' : E₁ ⟶ E₁'} (e : Arrow.mk f ≅ Arrow.mk f')
    (h : Eqv R f' F) : Eqv R f F := by
  have w : f = e.hom.left ≫ f' ≫ e.inv.right := by
    have := Arrow.w e.hom
    simp only [Arrow.mk_hom] at this
    rw [← Category.assoc, this, Category.assoc, ← Arrow.comp_right, e.hom_inv_id, Arrow.id_right]
    simp
  rw [w]
  exact ZariskiLocalCech.eqv_comp (ZariskiLocalCech.eqv_iso _) (ZariskiLocalCech.eqv_comp h (ZariskiLocalCech.eqv_iso _))

theorem eqv_of_comp_left {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) :
    Eqv R g F := fun n => by
  have h : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  have := hfg n
  rw [h] at this
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 this

end

theorem CechSigma_of (hL : LevelIso) : ZariskiLocalCech.CechSigma := by
  unfold LevelIso at hL
  intro hH R _ F Y X g O ι V hV hc hn
  obtain ⟨_, hA2, hA3, -⟩ := hH
  have hc' : g ⁻¹ᵁ O ≤ ⨆ j, g ⁻¹ᵁ V j := by
    rw [← Scheme.Hom.preimage_iSup]; exact pre_le g hc
  have := cov_surj O V hV hc
  have := cov_surj (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)) hc'
  have e1 : Eqv R (cechAug (cov O V hV)) F := hA2 R _ F
  have e2 : Eqv R (cechAug (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)))) F := hA2 R _ F
  have e3 : Eqv R (Arrow.mapCechNerve (arr g O V hV)) F := by
    refine hA3 R _ F fun m => ?_
    obtain ⟨e⟩ := hL g O V hV m.unop.len
    have e' : Arrow.mk (disc.map ((Arrow.mapCechNerve (arr g O V hV)).app m)) ≅
        Arrow.mk (sch.map (Limits.Sigma.map fun j : Fin (m.unop.len + 1) → ι => g ∣_ (⨅ k, V (j k)))) :=
      (disc.mapArrow).mapIso e
    exact eqv_of_arrowIso e' (hn _)
  have w : Arrow.mapCechNerve (arr g O V hV) ≫ cechAug (cov O V hV) =
      cechAug (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ≫ sch.map (g ∣_ O) := by
    have h := (Arrow.mapAugmentedCechNerve (arr g O V hV)).w
    exact h
  have h4 : Eqv R (cechAug (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ≫ sch.map (g ∣_ O)) F := by
    rw [← w]; exact ZariskiLocalCech.eqv_comp e3 e1
  exact eqv_of_comp_left e2 h4

end LateralTheory.E.CechSigmaProof
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Lev
open LateralTheory.E.CechSigmaProof

def sqS {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Arrow.mk (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ⟶ Arrow.mk (cov O V hV) :=
  Arrow.homMk (Limits.Sigma.map fun j => g ∣_ V j) (g ∣_ O) (sq_cov g O V hV)

def wpMap {A B C D : Scheme.{0}} {p : A ⟶ B} {q : C ⟶ D} (s : Arrow.mk p ⟶ Arrow.mk q) (n : ℕ) :
    widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p) ⟶ widePullback D (fun _ : Fin (n + 1) => C) (fun _ => q) :=
  WidePullback.lift (WidePullback.base _ ≫ s.right) (fun i => WidePullback.π _ i ≫ s.left)
    (fun i => by have := Arrow.w s; simp only [Arrow.mk_hom] at this; simp [this])

def CechYoneda : Prop := ∀ {A B C D : Scheme.{0}} {p : A ⟶ B} {q : C ⟶ D} (s : Arrow.mk p ⟶ Arrow.mk q) (n : ℕ),
  Nonempty (Arrow.mk ((Arrow.mapCechNerve (yoneda.mapArrow.map s)).app (op (SimplexCategory.mk n))) ≅
    Arrow.mk (yoneda.map (wpMap s n)))

def SchemeLevel : Prop := ∀ {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
  (n : ℕ), Nonempty (Arrow.mk (wpMap (sqS g O V hV) n) ≅
    Arrow.mk (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k))))

theorem LevelIso_of (hY : CechYoneda) (hS : SchemeLevel) : LevelIso := by
  intro Y X g O ι V hV n
  obtain ⟨e1⟩ := hY (sqS g O V hV) n
  obtain ⟨e2⟩ := hS g O V hV n
  exact ⟨e1 ≪≫ yoneda.mapArrow.mapIso e2⟩

theorem CechSigma_of (hY : CechYoneda) (hS : SchemeLevel) : ZariskiLocalCech.CechSigma :=
  LateralTheory.E.CechSigmaProof.CechSigma_of (LevelIso_of hY hS)

end LateralTheory.E.CechSigma_xy1Pf_Lev
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SHLocPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut Polynomial

namespace LateralTheory.E.SHLocPf

def EtClosed {O Ω : Type} [CommRing O] [Field Ω] (ψ : O →+* Ω) : Prop :=
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C] (χ : C →+* Ω),
    χ.comp (algebraMap O C) = ψ → ∃ s : C →ₐ[O] O, ψ.comp s.toRingHom = χ

def Build : Prop := ∀ (A : CommRingCat.{0}) [IsLocalRing A],
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (ψ : O →+* Ω),
    IE f ∧ Function.Surjective ψ ∧ (∀ a : A, a ∈ IsLocalRing.maximalIdeal A → ψ (f.hom a) = 0) ∧ EtClosed ψ

def Lift : Prop := ∀ (O Ω : Type) [CommRing O] [Field Ω] (ψ : O →+* Ω), EtClosed ψ →
  ∀ p : O[X], p.Monic → ∀ a₀ : O, ψ (p.eval a₀) = 0 → ψ (p.derivative.eval a₀) ≠ 0 →
    ∃ a : O, p.IsRoot a ∧ ψ a = ψ a₀

def Colim : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (ψ : O →+* Ω), IE f ∧ ψ.comp f.hom = ι ∧ EtClosed ψ

theorem unit_of_etClosed {O Ω : Type} [CommRing O] [Field Ω] (ψ : O →+* Ω) (h : EtClosed ψ)
    (x : O) (hx : ψ x ≠ 0) : IsUnit x := by
  have hu : IsUnit (ψ x) := isUnit_iff_ne_zero.mpr hx
  let χ : Localization.Away x →+* Ω := IsLocalization.Away.lift x hu
  have hχ : χ.comp (algebraMap O (Localization.Away x)) = ψ := IsLocalization.Away.lift_comp x hu
  obtain ⟨s, -⟩ := h (Localization.Away x) χ hχ
  refine IsUnit.of_mul_eq_one (b :=  s (IsLocalization.Away.invSelf x)) ?_
  have e := congrArg s (IsLocalization.Away.mul_invSelf (S := Localization.Away x) x)
  rw [map_mul, map_one, AlgHom.commutes] at e
  simpa using e

theorem etaleClosed_point_lifts_simple_roots_monic : Lift := by
  intro O Ω _ _ ψ hE p hp a₀ h₁ h₂
  letI : Algebra O Ω := ψ.toAlgebra
  let P : StandardEtalePair O := ⟨p, hp, p.derivative, ⟨1, 0, 1, by ring⟩⟩
  have hev : ∀ q : O[X], aeval (ψ a₀) q = ψ (q.eval a₀) := by
    intro q
    rw [Polynomial.aeval_def]; exact Polynomial.eval₂_at_apply (p := q) ψ a₀
  have hM : P.HasMap (ψ a₀) := ⟨by rw [hev]; exact h₁, by rw [hev]; exact isUnit_iff_ne_zero.mpr h₂⟩
  let χ : P.Ring →+* Ω := (P.lift (ψ a₀) hM).toRingHom
  have hχ : χ.comp (algebraMap O P.Ring) = ψ := (P.lift (ψ a₀) hM).comp_algebraMap
  obtain ⟨s, hs⟩ := hE P.Ring χ hχ
  refine ⟨s P.X, ?_, ?_⟩
  · have h0 : aeval P.X P.f = 0 := P.hasMap_X.1
    have h1 := congrArg s h0
    rw [map_zero, ← Polynomial.aeval_algHom_apply] at h1
    rw [Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval]
    exact h1
  · have := congrArg (fun g => g P.X) hs
    simp only [RingHom.comp_apply] at this
    rw [show ψ (s P.X) = χ P.X from this]
    exact P.lift_X (ψ a₀) hM

theorem build_of (hC : Colim) : Build := by
  intro A _
  let k := IsLocalRing.ResidueField A
  let ι : A →+* SeparableClosure k := (algebraMap k (SeparableClosure k)).comp (IsLocalRing.residue A)
  obtain ⟨O, f, ψ, hIE, hcomp, hE⟩ := hC A (SeparableClosure k) ι
  refine ⟨O, f, SeparableClosure k, inferInstance, inferInstance, ψ, hIE, ?_, ?_, hE⟩
  · intro ω
    have hsep : (minpoly k ω).Separable := Algebra.IsSeparable.isSeparable k ω
    have hmon : (minpoly k ω).Monic := minpoly.monic (Algebra.IsSeparable.isIntegral k ω)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      ((Polynomial.lifts_iff_coeff_lifts _).2 (fun n => IsLocalRing.residue_surjective _)) hmon
    letI : Algebra O (SeparableClosure k) := ψ.toAlgebra
    let P : StandardEtalePair O :=
      ⟨q.map f.hom, hqm.map _, (q.map f.hom).derivative, ⟨1, 0, 1, by ring⟩⟩
    have hev : ∀ r : A[X], aeval ω (r.map f.hom) = aeval ω (r.map (IsLocalRing.residue A)) := by
      intro r
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map]
      congr 1
    have hM : P.HasMap ω := by
      refine ⟨?_, ?_⟩
      · change aeval ω (q.map f.hom) = 0
        rw [hev, hq]; exact minpoly.aeval k ω
      · change IsUnit (aeval ω (q.map f.hom).derivative)
        rw [Polynomial.derivative_map, hev, ← Polynomial.derivative_map, hq]
        exact isUnit_iff_ne_zero.mpr (hsep.aeval_derivative_ne_zero (minpoly.aeval k ω))
    let χ : P.Ring →+* SeparableClosure k := (P.lift ω hM).toRingHom
    have hχ : χ.comp (algebraMap O P.Ring) = ψ := (P.lift ω hM).comp_algebraMap
    obtain ⟨s, hs⟩ := hE P.Ring χ hχ
    refine ⟨s P.X, ?_⟩
    have := congrArg (fun g => g P.X) hs
    simp only [RingHom.comp_apply] at this
    rw [show ψ (s P.X) = χ P.X from this]
    exact P.lift_X ω hM
  · intro a ha
    have e : ψ (f.hom a) = ι a := congrArg (fun g => g a) hcomp
    rw [e]
    simp [ι, (IsLocalRing.residue_eq_zero_iff a).2 ha]

theorem SHLoc_of (hB : Build) (hL : Lift) : LateralTheory.E.SHExistsPf.SHLoc := by
  intro A _
  obtain ⟨O, f, Ω, _, _, ψ, hIE, hs, hm, hE⟩ := hB A
  have hU : ∀ x : O, ψ x ≠ 0 → IsUnit x := unit_of_etClosed ψ hE
  have hZ : ∀ x : O, IsUnit x → ψ x ≠ 0 := fun x hx => (hx.map ψ).ne_zero
  have : Nontrivial O := ⟨⟨1, 0, fun h => by simpa using congrArg ψ h⟩⟩
  have : IsLocalRing O := IsLocalRing.of_nonunits_add (by
    intro a b ha hb hab
    have ha' : ψ a = 0 := by by_contra h; exact ha (hU a h)
    have hb' : ψ b = 0 := by by_contra h; exact hb (hU b h)
    exact hZ _ hab (by rw [map_add (f := _), ha', hb', add_zero]))
  have hmem : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O ↔ ψ x = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by by_contra h'; exact h (hU x h'), fun h hx => hZ x hx h⟩
  have hker : IsLocalRing.maximalIdeal O = RingHom.ker ψ := by
    ext x; rw [hmem, RingHom.mem_ker]
  let e : IsLocalRing.ResidueField O ≃+* Ω :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hs)
  have hSC : IsSepClosed (IsLocalRing.ResidueField O) := by
    refine IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)
    have hd : (p.map (e : IsLocalRing.ResidueField O →+* Ω)).degree ≠ 0 := by
      rw [Polynomial.degree_map]; exact (Polynomial.degree_pos_of_irreducible hirr).ne'
    obtain ⟨y, hy⟩ := IsSepClosed.exists_root _ hd (hsep.map)
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [map_zero, ← hy]
    have h := Polynomial.eval₂_at_apply (p := p) (e : IsLocalRing.ResidueField O →+* Ω) (e.symm y)
    rw [Polynomial.eval_map]
    simpa using h.symm
  have hH : HenselianLocalRing O := {
    is_henselian := by
      intro p hp a₀ h₁ h₂
      obtain ⟨a, ha, ha'⟩ := hL O Ω ψ hE p hp a₀ ((hmem _).1 h₁) (hZ _ h₂)
      exact ⟨a, ha, (hmem _).2 (by rw [map_sub, ha', sub_self])⟩ }
  refine ⟨O, f, hIE, ⟨hH, hSC⟩, ⟨fun a ha => ?_⟩⟩
  by_contra hna
  exact hZ _ ha (hm a ((IsLocalRing.mem_maximalIdeal _).2 hna))

end LateralTheory.E.SHLocPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTwTensExPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTwTensExPf

open Classical in
section
variable {R : Type} [CommRing R] (I J : Cx R)

theorem tres_tmul {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  simp [Tens.res]

def TP (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have := tres_tmul I J (𝟙 U.unop) w p a b
        simp only [DirectSum.lof_eq_of] at this
        simp [this, Sec.res]
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have h1 := tres_tmul I J (g.unop ≫ f.unop) w p a b
        have h2 := tres_tmul I J f.unop w p a b
        have h3 := tres_tmul I J g.unop w p (Sec.res f.unop a) (Sec.res f.unop b)
        simp only [DirectSum.lof_eq_of] at h1 h2 h3
        simp [h1, h2, Sec.res]
        exact h3.symm
end
end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

abbrev lo {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U w :=
  DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p

def dT (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    lo I J (U := U) (w := w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
    ((p.1.1.negOnePow : ℤˣ) : ℤ) • (lo I J (U := U) (w := w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

theorem dT_tmul (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      lo I J ⟨(s + 1, t), by simp only; omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b) +
      ((s.negOnePow : ℤˣ) : ℤ) • lo I J ⟨(s, t + 1), by simp only; omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b) := by
  simp [dT, lo, DirectSum.toModule_lof]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

theorem dd0 {K : Cx R} {U : Scheme.{0}} (s : ℤ) (a : Sec (K.X s) U) :
    Sec.map (K.d (s + 1) (s + 1 + 1)) (Sec.map (K.d s (s + 1)) a) = 0 := by
  rw [LateralTheory.E.LeafTwPairExistsPf.map_map, HomologicalComplex.d_comp_d]
  simp [Sec.map]

theorem dT_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  erw [tres_tmul, dT_tmul, dT_tmul, map_add, map_zsmul, tres_tmul, tres_tmul,
    LateralTheory.E.LeafTwPairExistsPf.res_map, LateralTheory.E.LeafTwPairExistsPf.res_map]

theorem dT_dT (U : Scheme.{0}) (w : ℤ) : dT I J U (w + 1) ∘ₗ dT I J U w = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [dT_tmul, map_add (f := _), map_zsmul]
  rw [dT_tmul (s := s + 1) (t := t) (w := w + 1)]
  rw [dT_tmul (s := s) (t := t + 1) (w := w + 1)]
  rw [dd0 (K := I), dd0 (K := J)]
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, smul_zero, add_zero,
    Int.negOnePow_succ, Units.val_neg, neg_smul, neg_add_cancel]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def dTP (w : ℤ) : TP I J w ⟶ TP I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (dT_nat I J g.unop w)

def PC : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (TP I J) (dTP I J) (fun w => by
    ext U : 2
    exact ModuleCat.hom_ext (dT_dT I J U.unop w))

def TC : Cx R := ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex _).obj (PC I J)

abbrev un (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((TC I J).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).app (op U)).hom

theorem un_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (un I J U w x) = un I J V w (Tens.res g w x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).naturality g.op)) x).symm

theorem un_d (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((TC I J).d w (w + 1)) (un I J U w x) = un I J U (w + 1) (dT I J U w x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (congrArg (fun f => f.app (op U)) (toSheafify_naturality Scheme.etaleTopology.{0} (dTP I J w)))) x
  simp only [TC, PC, Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d] at this ⊢
  exact this.symm

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def tau : Pair I J (TC I J) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (un I J U w ∘ₗ lo I J ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_nat]
    congr 1
    exact tres_tmul I J g w ⟨(s, t), h⟩ a b
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_d, dT_tmul, map_add (f := _), map_zsmul, Units.smul_def]

theorem tau_lift (U : Scheme.{0}) (w : ℤ) : (tau I J).lift U w = un I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp [Pair.lift, tau]

theorem tau_isTensor : (tau I J).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (U := op U) y, fun V g ⟨t, ht⟩ => ⟨t, ?_⟩⟩
    rw [tau_lift]
    exact ht
  · rw [tau_lift] at hx
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (X := op U) x 0 (by rw [map_zero]; exact hx), fun V g hg => ?_⟩
    have : Tens.res g w x = Tens.res g w 0 := hg
    rwa [map_zero] at this

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf

theorem LeafTwTensEx_of : LateralTheory.E.LeafTwPairExistsPf.LeafTwTensEx := by
  intro q _ i j
  exact ⟨_, tau _ _, tau_isTensor _ _⟩

end LateralTheory.E.LeafTwTensExPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtAffNbhdPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.EtAffNbhdPf

theorem EtAffNbhd_of : LateralTheory.E.SHSectionPf.EtAffNbhd := by
  intro A _ V g hg _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let x : Spec A := ⟨m, hm.isPrime⟩
  obtain ⟨v, hv⟩ := g.surjective x
  let 𝒰 := V.affineCover
  obtain ⟨p, hp⟩ := 𝒰.covers v
  let ι := 𝒰.f (𝒰.idx v)
  have : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (𝒰.f (𝒰.idx v)))
  have : Etale ι := inferInstance
  have : Etale (ι ≫ g) := inferInstance
  let f : A ⟶ _ := Spec.preimage (ι ≫ g)
  have hfg : Spec.map f = ι ≫ g := Spec.map_preimage _
  refine ⟨_, f, ι, ?_, hfg.symm, p.asIdeal, p.isPrime, ?_⟩
  · have : Etale (Spec.map f) := by have h := ‹Etale (ι ≫ g)›; rw [← hfg] at h; exact h
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  · have h1 : (Spec.map f).base p = x := by
      rw [hfg]
      change g.base (ι.base p) = x
      rw [hp, hv]
    have h2 : ((Spec.map f).base p).asIdeal = p.asIdeal.comap f.hom := rfl
    rw [← h2, h1]
    exact hm

end LateralTheory.E.EtAffNbhdPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FinOpenPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinOpenPf

theorem range_closed (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C)
    (he : IsIdempotentElem e) :
    IsClosed (Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) := by
  rw [PrimeSpectrum.comap_comp, Set.range_comp,
    PrimeSpectrum.localization_away_comap_range (Localization.Away e) e,
    PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (fun x => Algebra.IsIntegral.isIntegral (R := S) x) _
    (PrimeSpectrum.isClosed_zeroLocus _)

theorem FinOpen_of : LateralTheory.E.FinEtSectionPf.FinOpen := by
  intro S C _ _ _ _ e he hoi
  set φ := (algebraMap C (Localization.Away e)).comp (algebraMap S C) with hφ
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap φ)) := hoi.isOpen_range
  obtain ⟨ε, hε, hr⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ⟨range_closed S C e he, hopen⟩
  refine ⟨ε, hε, hr, ?_⟩
  let f := Spec.map (CommRingCat.ofHom φ)
  let g := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ε)))
  have H : Set.range g ⊆ Set.range f := by
    change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away ε))) ⊆
      Set.range (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away ε) ε, hr]
  let l := IsOpenImmersion.lift f g H
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have key : CommRingCat.ofHom φ ≫ Spec.preimage l =
      CommRingCat.ofHom (algebraMap S (Localization.Away ε)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac f g H
  exact congrArg CommRingCat.Hom.hom key

end LateralTheory.E.FinOpenPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafOneLocPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneLocPf

theorem freeGen_res (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  have h2 : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} (P.map g.op x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg _ h2)

theorem ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (Sx.res g x) := by
  unfold ev
  have hn := congrArg (fun f => f.hom (freeGen R _ U x))
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hn
  change _ = _ at hn
  rw [Sx.res, ← freeGen_res]
  exact hn.symm

def LeafPrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))

theorem LeafOneLoc_of (hprim : LeafPrimLoc) : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := by
  intro q _ E hE α hα U x
  obtain ⟨S, hS, hP⟩ := hprim q U (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  exact ⟨ζ, (ev_res α.1 0 0 (by simp) g x).trans (hα V (Sx.res g x) ζ)⟩

end LateralTheory.E.LeafOneLocPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FracAICPf
open Polynomial

namespace LateralTheory.E.FracAICPf

open Classical in
theorem FracAIC_of : LateralTheory.E.ULAStalkPf.FracAIC := by
  intro T K _ _ _ _ _ hT p hp hdeg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T)
    (p.support.image p.coeff)
  set s : K := algebraMap T K b with hs
  have hs0 : s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  set q := p.scaleRoots s with hq
  have hqm : q.Monic := (monic_scaleRoots_iff _).mpr hp
  have hqd : q.natDegree = p.natDegree := natDegree_scaleRoots _ _
  have hlift : q ∈ lifts (algebraMap T K) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [hq, coeff_scaleRoots]
    by_cases hi : p.coeff i = 0
    · rw [hi, zero_mul]; exact ⟨0, map_zero _⟩
    have hile : i ≤ p.natDegree := le_natDegree_of_ne_zero hi
    rcases lt_or_eq_of_le hile with hlt | heq
    · obtain ⟨c, hc⟩ := hb (p.coeff i) (Finset.mem_image_of_mem _ (mem_support_iff.mpr hi))
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      refine ⟨c * (b : T) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, hc, Algebra.smul_def, pow_succ, hs]
      ring
    · subst heq
      rw [Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree]
      exact ⟨1, map_one _⟩
  obtain ⟨q', hq'map, hq'deg, hq'm⟩ := lifts_and_natDegree_eq_and_monic hlift hqm
  obtain ⟨r, hr⟩ := hT q' hq'm (by rw [hq'deg, hqd]; exact hdeg)
  refine ⟨algebraMap T K r / s, ?_⟩
  have h1 : q.eval (algebraMap T K r) = 0 := by
    rw [← hq'map, eval_map, eval₂_at_apply, hr, map_zero]
  have h2 := scaleRoots_eval₂_mul (p := p) (RingHom.id K) (algebraMap T K r / s) s
  simp only [RingHom.id_apply, eval₂_id] at h2
  rw [mul_div_cancel₀ _ hs0, ← hq, h1] at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hs0)

end LateralTheory.E.FracAICPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SHAlgSecPf
noncomputable section
open CategoryTheory Limits IsLocalRing

namespace LateralTheory.E.SHAlgSecPf

theorem retract_alg {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] [Algebra.Etale A R] (Q : Ideal R) [Q.IsPrime]
    (hQ : (Q.comap (algebraMap A R)).IsMaximal) : Nonempty (R →ₐ[A] A) := by
  have hQm : Q.comap (algebraMap A R) = maximalIdeal A := IsLocalRing.eq_maximalIdeal hQ
  have hEt : Algebra.IsEtaleAt A Q := by
    have h := (Algebra.etaleLocus_eq_univ_iff_etale (R := A) (A := R)).mpr inferInstance
    have : (⟨Q, inferInstance⟩ : PrimeSpectrum R) ∈ Algebra.etaleLocus A R := by rw [h]; trivial
    exact this
  obtain ⟨g, hgQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let Rg := Localization.Away g
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid R) : Set R) (Q : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hgQ
  let Q' : Ideal Rg := Q.map (algebraMap R Rg)
  have hQ'p : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Rg Q ‹_› hdisj
  have hQ'c : Q'.comap (algebraMap R Rg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Rg ‹_› hdisj
  have hcomap : Q'.comap (algebraMap A Rg) = RingHom.ker (algebraMap A (ResidueField A)) := by
    rw [IsScalarTower.algebraMap_eq A R Rg, ← Ideal.comap_comap, hQ'c, hQm,
      ResidueField.algebraMap_eq, ker_residue]
  obtain ⟨φ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := A) (K := ResidueField A) Q' hcomap
  obtain ⟨ψ, -⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale (R := A) (A := Rg) (B := A)
    (C := ResidueField A) (maximalIdeal A) (Algebra.ofId A (ResidueField A))
    (residue_surjective) (fun b => by
      simp [Algebra.ofId_apply, ResidueField.algebraMap_eq, residue_eq_zero_iff]) φ
  exact ⟨ψ.comp (IsScalarTower.toAlgHom A R Rg)⟩

theorem SHAlgSec_of : LateralTheory.E.SHSectionPf.SHAlgSec := by
  intro A R f hA hf hQ
  obtain ⟨hH, hS⟩ := hA
  let := f.hom.toAlgebra
  have : Algebra.Etale A R := (RingHom.etale_algebraMap).mp hf
  obtain ⟨Q, hQp, hQm⟩ := hQ
  obtain ⟨σ⟩ := retract_alg (A := A) (R := R) Q hQm
  refine ⟨CommRingCat.ofHom σ.toRingHom, ?_⟩
  ext a
  exact σ.commutes a

end LateralTheory.E.SHAlgSecPf
end
end

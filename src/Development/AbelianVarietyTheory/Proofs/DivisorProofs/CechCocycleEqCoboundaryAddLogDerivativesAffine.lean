module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1FiniteGenerationAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleOfFiniteAffineSubcover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleOfFiniteAffineSubcover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

variable {Z : Scheme.{0}}

theorem sf_resG_resG {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x :=
  (congrArg (fun q => q.hom x) (Z.presheaf.map_comp (homOfLE h).op (homOfLE h').op)).symm

theorem sf_resG_id {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) : resG Z h x = x :=
  congrArg (fun q => q.hom x) (Z.presheaf.map_id (Opposite.op U))

theorem sf_resG_inj {U V : Z.Opens} (h : V ≤ U) (h' : U ≤ V) {x y : Γ(Z, U)}
    (e : resG Z h x = resG Z h y) : x = y := by
  have := congrArg (resG Z h') e
  rwa [sf_resG_resG, sf_resG_resG, sf_resG_id, sf_resG_id] at this

variable {J : Type} (W : J → Z.Opens) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))

def sfCr (U : Z.Opens) (i i' : J) (h : U ≤ W i ⊓ W i') : Γ(Z, U) := resG Z h (c i i')

theorem sfCr_res {U V : Z.Opens} (i i' : J) (h : U ≤ W i ⊓ W i') (h' : V ≤ U) :
    resG Z h' (sfCr W c U i i' h) = sfCr W c V i i' (h'.trans h) :=
  sf_resG_resG _ _ _

theorem sfCr_add (hc : IsCoc W c) (U : Z.Opens) (i i' i'' : J) (h : U ≤ W i ⊓ W i' ⊓ W i'') :
    sfCr W c U i i' (h.trans inf_le_left) +
      sfCr W c U i' i'' (h.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) =
      sfCr W c U i i'' (h.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) := by
  have e := congrArg (resG Z h) (hc i i' i'')
  rw [map_add (f := _), sf_resG_resG, sf_resG_resG, sf_resG_resG] at e
  exact e

theorem sfCr_self (hc : IsCoc W c) (U : Z.Opens) (i : J) (h : U ≤ W i ⊓ W i) :
    sfCr W c U i i h = 0 := by
  have e := sfCr_add W c hc U i i i (le_inf h (h.trans inf_le_left))
  have e2 : sfCr W c U i i h + sfCr W c U i i h = sfCr W c U i i h := e
  linear_combination e2

theorem sfCr_congr2 (U : Z.Opens) {i i' j' : J} (e : i' = j') (h : U ≤ W i ⊓ W i') (h' : U ≤ W i ⊓ W j') :
    sfCr W c U i i' h = sfCr W c U i j' h' := by subst e; rfl

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

theorem cechAffineCochainValue_congr_source (f : C1 (OAff s)) {A A' B : Z.affineOpens} (e : A = A') (h : B.1 ≤ A.1) (h' : B.1 ≤ A'.1) :
    fv s f h = fv s f h' := by subst e; rfl

end GlobalTheory.CechFin


open GlobalTheory.CechPoset in
theorem GlobalTheory.CechFin.cocycle_of_finite_affine_subcover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i')), (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) → ∀ S : Finset J, ⨆ i ∈ S, W i = ⊤ → ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i ∈ S, ∀ i' ∈ S, c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
  intro R _ Z s J W hW hW2 hI S hS c hc
  let κ := {j // j ∈ S}
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  let D : κ → Z.Opens := fun k => W k.1
  have hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ k ∈ I, D k) := by
    classical
    intro I hIn
    have := hI (I.image Subtype.val) (hIn.image _)
    rwa [Finset.iInf_finset_image] at this
  have hcov : ⨆ k, D k = ⊤ := by
    rw [← hS, iSup_subtype']
  have hinf : ∀ a b : NE κ, (cov D hD (a ⊓ b)).1 = (cov D hD a).1 ⊓ (cov D hD b).1 :=
    fun a b => Finset.iInf_union
  have hsup : ⨆ a, (cov D hD a).1 = ⊤ := by
    refine eq_top_iff.2 (hcov.symm.le.trans (iSup_le fun k => ?_))
    refine le_trans (le_of_eq ?_) (le_iSup (fun a => (cov D hD a).1)
      (OrderDual.toDual ⟨{k}, Finset.singleton_nonempty k⟩))
    simp [cov]
  have hmem : ∀ (a : (NE κ)ᵒᵖ) (k : κ), k ∈ sub a → (cov D hD a.unop).1 ≤ W k.1 :=
    fun a k hk => biInf_le (fun k => D k) hk
  let Fv : C1 (covF s D hD) := fun a b φ =>
    sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1
      (le_inf (hmem b _ (mn_mem b)) (hmem b _ (sub_subset φ (mn_mem a))))
  have hF : Fv ∈ Z1 (covF s D hD) := by
    intro a b d φ ψ
    have e := sfCr_add W c hc (cov D hD d.unop).1 (mn d).1 (mn b).1 (mn a).1
      (le_inf (le_inf (hmem d _ (mn_mem d)) (hmem d _ (sub_subset ψ (mn_mem b))))
        (hmem d _ (sub_subset ψ (sub_subset φ (mn_mem a)))))
    show sfCr W c (cov D hD d.unop).1 (mn d).1 (mn a).1 _ =
      resG Z (cov_mono D hD (leOfHom ψ.unop)) (sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1 _) +
        sfCr W c (cov D hD d.unop).1 (mn d).1 (mn b).1 _
    rw [sfCr_res]
    rw [add_comm]
    exact e.symm
  obtain ⟨y, hy⟩ := (GlobalTheory.T.cech_pull_one_bijective_lattice_cover R Z s (NE κ) (cov D hD) (cov_mono D hD) hinf hsup).2
    (H1.mk _ ⟨Fv, hF⟩)
  obtain ⟨f0, rfl⟩ := H1.mk_surjective _ y
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hy
  obtain ⟨g, hg⟩ := hy

  let hfun : ∀ i, Γ(Z, W i) := fun i => @dite _ (i ∈ S) (Classical.propDecidable _) (fun hi =>
      -resG Z (le_of_eq (Finset.iInf_singleton (⟨i, hi⟩ : κ) D).symm :
        W i ≤ (cov D hD (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)).unop).1)
        (g (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)))) (fun _ => 0)
  refine ⟨-f0, hfun, fun i hi i' hi' => ?_⟩
  let k : κ := ⟨i, hi⟩
  let k' : κ := ⟨i', hi'⟩
  let a := ne {k} (Finset.singleton_nonempty k)
  let a' := ne {k'} (Finset.singleton_nonempty k')
  let b := ne {k, k'} (Finset.insert_nonempty k {k'})
  have ca : (cov D hD a.unop).1 = W i := Finset.iInf_singleton k D
  have ca' : (cov D hD a'.unop).1 = W i' := Finset.iInf_singleton k' D
  have cb : (cov D hD b.unop).1 = W i ⊓ W i' := by
    show (⨅ j ∈ ({k, k'} : Finset κ), D j) = _
    rw [Finset.iInf_insert, Finset.iInf_singleton]
  let φ : a ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_self k {k'}))
  let φ' : a' ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self k')))
  have hab : (cov D hD b.unop).1 ≤ (cov D hD a.unop).1 := cov_mono D hD (leOfHom φ.unop)
  have ha'b : (cov D hD b.unop).1 ≤ (cov D hD a'.unop).1 := cov_mono D hD (leOfHom φ'.unop)
  have hBP : (cov D hD b.unop).1 ≤ W i ⊓ W i' := cb.le
  have hPB : W i ⊓ W i' ≤ (cov D hD b.unop).1 := cb.ge
  have mna : mn a = k := Finset.min'_singleton k
  have mna' : mn a' = k' := Finset.min'_singleton k'
  have hxB : (cov D hD b.unop).1 ≤ W (mn b).1 := hmem b _ (mn_mem b)
  have h4 := congrFun (congrFun (congrFun hg a) b) φ
  have h5 := congrFun (congrFun (congrFun hg a') b) φ'
  have h4' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z hab (g a) = fv s f0.1 (A := cov D hD a.unop) (B := cov D hD b.unop) hab -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i (le_inf hxB (hBP.trans inf_le_left)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna) (le_inf hxB (hab.trans (hmem a _ (mn_mem a))))]
    exact h4
  have h5' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z ha'b (g a') = fv s f0.1 (A := cov D hD a'.unop) (B := cov D hD b.unop) ha'b -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i' (le_inf hxB (hBP.trans inf_le_right)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna') (le_inf hxB (ha'b.trans (hmem a' _ (mn_mem a'))))]
    exact h5
  have c1 := sfCr_add W c hc (cov D hD b.unop).1 i (mn b).1 i'
    (le_inf (le_inf (hBP.trans inf_le_left) hxB) (hBP.trans inf_le_right))
  have c2 := sfCr_add W c hc (cov D hD b.unop).1 (mn b).1 i (mn b).1
    (le_inf (le_inf hxB (hBP.trans inf_le_left)) hxB)
  rw [sfCr_self W c hc] at c2
  have r1 := res_val s f0 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_left hBP
  have r2 := res_val s f0 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_right hBP
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca.symm) _ hab] at r1
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca'.symm) _ ha'b] at r2
  have erho : resG Z hBP (rho W s hW hW2 (-f0).1 i i') =
      -resG Z hBP (fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left) +
        resG Z hBP (fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) := by
    show resG Z hBP (-fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
      -fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) = _
    rw [map_sub, map_neg, map_neg]; ring
  have e0 : resG Z hBP (c i i') = sfCr W c (cov D hD b.unop).1 i i' hBP := rfl
  have t1 : resG Z hBP (resG Z inf_le_left (hfun i)) = -resG Z hab (g a) := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi]
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  have t2 : resG Z hBP (resG Z inf_le_right (hfun i')) = -resG Z ha'b (g a') := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi']
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  rw [r1, r2] at erho
  apply sf_resG_inj hBP hPB
  rw [map_add (f := _), map_sub, t1, t2]
  linear_combination e0 - erho - h4' + h5' - c1 + c2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleOfFiniteAffineSubcoverStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_of_finite_affine_subcover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i')), (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) → ∀ S : Finset J, ⨆ i ∈ S, W i = ⊤ → ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i ∈ S, ∀ i' ∈ S, c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
  first | exact @GlobalTheory.CechFin.cocycle_of_finite_affine_subcover | exact GlobalTheory.CechFin.cocycle_of_finite_affine_subcover | (intros; apply GlobalTheory.CechFin.cocycle_of_finite_affine_subcover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChange
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_transfer {Z Z' : Scheme.{0}} {J : Type} (W : J → Z.Opens) (W' : J → Z'.Opens)
    (R : Type) [CommRing R]
    (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) (act' : ∀ i i' : J, R →+* Γ(Z', W' i ⊓ W' i'))
    (φ1 : ∀ i, Γ(Z, W i) →+* Γ(Z', W' i))
    (φ2 : ∀ i i', Γ(Z, W i ⊓ W i') →+* Γ(Z', W' i ⊓ W' i'))
    (φ3 : ∀ i i' i'', Γ(Z, W i ⊓ W i' ⊓ W i'') →+* Γ(Z', W' i ⊓ W' i' ⊓ W' i''))
    (h1 : ∀ i, Function.Surjective (φ1 i))
    (h2 : ∀ i i', Function.Bijective (φ2 i i'))
    (h3 : ∀ i i' i'', Function.Injective (φ3 i i' i''))
    (hl : ∀ i i' x, φ2 i i' (resG Z inf_le_left x) = resG Z' inf_le_left (φ1 i x))
    (hr : ∀ i i' x, φ2 i i' (resG Z inf_le_right x) = resG Z' inf_le_right (φ1 i' x))
    (ha : ∀ i i' i'' x, φ3 i i' i'' (resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') x) =
      resG Z' (inf_le_left : W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i') (φ2 i i' x))
    (hb : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i' ⊓ W' i'') (φ2 i' i'' x))
    (hc : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i'') (φ2 i i'' x))
    (hact : ∀ i i' r, φ2 i i' (act i i' r) = act' i i' r) :
    CechFG W' R act' → CechFG W R act := by
  rintro ⟨N, e', he', hc'⟩
  choose g hg using fun (k : Fin N) (i i' : J) => (h2 i i').2 (e' k i i')
  refine ⟨N, g, ?_, ?_⟩
  · intro k i i' i''
    apply h3 i i' i''
    have := he' k i i' i''
    rw [map_add (f := _), ha, hb, hc, hg, hg, hg]
    exact this
  · intro c hcoc
    obtain ⟨r, h', hh⟩ := hc' (fun i i' => φ2 i i' (c i i')) (by
      intro i i' i''
      have := congrArg (φ3 i i' i'') (hcoc i i' i'')
      rw [map_add (f := _), ha, hb, hc] at this
      exact this)
    choose h hh1 using fun i => h1 i (h' i)
    refine ⟨r, h, fun i i' => (h2 i i').1 ?_⟩
    have e1 := hh i i'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sub, map_sum, hl, hr, hh1, hh1]
    simp only [map_mul, hact, hg]
    exact e1

theorem appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {O₁ O₂ : Y.Opens} {V₁ V₂ : X.Opens} (hO : O₂ ≤ O₁)
    (hV : V₂ ≤ V₁) (e₁ : V₁ ≤ f ⁻¹ᵁ O₁) (e₂ : V₂ ≤ f ⁻¹ᵁ O₂) (x : Γ(Y, O₁)) :
    (f.appLE O₂ V₂ e₂).hom (resG Y hO x) = resG X hV ((f.appLE O₁ V₁ e₁).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] {O : Y.Opens}
    (hO : O ≤ f.opensRange) {V : X.Opens} (hV : V = f ⁻¹ᵁ O) (e : V ≤ f ⁻¹ᵁ O) :
    Function.Bijective (f.appLE O V e).hom := by
  subst hV
  rw [Scheme.Hom.appLE_eq_app]
  haveI := f.isIso_app O hO
  exact (asIso (f.app O)).commRingCatIsoToRingEquiv.bijective

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem preimage_inf' {X Y : Scheme.{0}} (f : X ⟶ Y) (A B : Y.Opens) :
    f ⁻¹ᵁ (A ⊓ B) = f ⁻¹ᵁ A ⊓ f ⁻¹ᵁ B := by
  ext x; simp

theorem appLE_act {G X : Scheme.{0}} (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (O : G.Opens)
    (V : (pullback p hU.fromSpec).Opens) (hO : O ≤ p ⁻¹ᵁ U)
    (e : V ≤ pullback.fst p hU.fromSpec ⁻¹ᵁ O) (r : Γ(X, U)) :
    ((pullback.fst p hU.fromSpec).appLE O V e).hom ((p.appLE U O hO).hom r) =
      (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) V).hom r := by
  have e' : V ≤ (pullback.snd p hU.fromSpec ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [← pullback.condition]; exact e.trans (Scheme.Hom.preimage_mono _ hO)
  have key : (pullback.snd p hU.fromSpec ≫ hU.fromSpec).appLE U V e' =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (pullback.snd p hU.fromSpec).appLE ⊤ V le_top := by
    rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self, Category.assoc]
    exact congrArg ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ ·) (Scheme.Hom.map_appLE _ _ _)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq pullback.condition _ _ _ e', key]
  rfl

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_baseChange_affineOpen (G X : Scheme.{0}) (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) :
    CechFG (fun i => pullback.fst p hU.fromSpec ⁻¹ᵁ W i) Γ(X, U)
        (fun i i' => (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) _).hom) →
      CechFG W Γ(X, U) (fun i i' => (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  have hR : ∀ O : G.Opens, O ≤ p ⁻¹ᵁ U → O ≤ (pullback.fst p hU.fromSpec).opensRange := by
    intro O hO
    rw [Scheme.Hom.opensRange_pullbackFst, IsAffineOpen.opensRange_fromSpec]
    exact hO
  have h2e : ∀ A B : G.Opens, pullback.fst p hU.fromSpec ⁻¹ᵁ A ⊓ pullback.fst p hU.fromSpec ⁻¹ᵁ B =
      pullback.fst p hU.fromSpec ⁻¹ᵁ (A ⊓ B) := fun A B => (preimage_inf' _ A B).symm
  refine cechFG_of_transfer W _ _ _ _
    (fun i => ((pullback.fst p hU.fromSpec).appLE (W i) _ le_rfl).hom)
    (fun i i' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i') _ (h2e _ _).le).hom)
    (fun i i' i'' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i' ⊓ W i'') _
      (by rw [h2e, h2e])).hom)
    (fun i => (appLE_bijective _ (hR _ (hWU i)) rfl _).2)
    (fun i i' => appLE_bijective _ (hR _ (inf_le_left.trans (hWU i))) (h2e _ _) _)
    (fun i i' i'' => (appLE_bijective _ (hR _ (inf_le_left.trans (inf_le_left.trans (hWU i))))
      (by rw [h2e, h2e]) _).1)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' r => appLE_act p U hU _ _ _ _ r)

theorem cechFG_of_baseChange_affine (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type)
    (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1) :
    CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1)
        (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) →
      CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) :=
  cechFG_of_baseChange_affineOpen G X p U.1 U.2 J W hWU

end GlobalTheory.CechTr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_finite_generation_of_affine_base_change : ∀ (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1) (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) → CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  first | exact @GlobalTheory.CechTr.cechFG_of_baseChange_affine | exact GlobalTheory.CechTr.cechFG_of_baseChange_affine | (intros; apply GlobalTheory.CechTr.cechFG_of_baseChange_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1FiniteAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1FiniteAffineOpen
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFinGen

theorem finite_piece (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (f : R) (hf : IsIdempotentElem f) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - f}))))) :
    Module.Finite (R ⧸ Ideal.span {1 - f}) ((R ⧸ Ideal.span {1 - f}) ⊗[R] HO1 A.hom) := by
  haveI : IsLocalization.Away f (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem hf
  haveI : Module.Flat R (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.flat (R ⧸ Ideal.span {1 - f}) (Submonoid.powers f)
  let B : Over (Sp (R ⧸ Ideal.span {1 - f})) :=
    (Over.pullback (spMap (algebraMap R (R ⧸ Ideal.span {1 - f})))).obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj _ A hA
  have hBg : SmoothOfRelativeDimension g B.hom := hg
  obtain ⟨hfp, -, -, -⟩ := hO _ B g hB hBg
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (R ⧸ Ideal.span {1 - f}) A.left B.left A.hom B.hom
    (pullback.fst _ _) (IsPullback.of_hasPullback _ _) inferInstance inferInstance
  haveI := hfp.1
  exact Module.Finite.equiv e.symm

theorem finite_HO1 (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) : Module.Finite R (HO1 A.hom) := by
  obtain ⟨n, e, he, hsm⟩ := GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension R A hA
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff, ← he.complete]
    exact Ideal.sum_mem _ (fun k _ ↦ Ideal.subset_span ⟨k, rfl⟩)
  have hidem : ∀ g : Set.range e, IsIdempotentElem g.val := by
    rintro ⟨_, k, rfl⟩; exact he.idem k
  haveI : ∀ g : Set.range e, IsLocalization.Away g.val (R ⧸ Ideal.span {1 - g.val}) := fun g ↦
    IsLocalization.Away.quotient_of_isIdempotentElem (hidem g)
  haveI : ∀ g : Set.range e, IsLocalizedModule.Away g.val
      (TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) := fun g ↦
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.val) (R ⧸ Ideal.span {1 - g.val}) _).2
      (TensorProduct.isBaseChange R (HO1 A.hom) (R ⧸ Ideal.span {1 - g.val}))
  refine Module.Finite.of_localizationSpan' (Set.range e) hspan
    (Rₚ := fun g ↦ R ⧸ Ideal.span {1 - g.val})
    (Mₚ := fun g ↦ (R ⧸ Ideal.span {1 - g.val}) ⊗[R] HO1 A.hom)
    (fun g ↦ TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) (fun g ↦ ?_)
  obtain ⟨_, k, rfl⟩ := g
  obtain ⟨d, hd⟩ := hsm k
  exact finite_piece hO A hA (e k) (he.idem k) d hd

end GlobalTheory.CechFinGen

theorem GlobalTheory.CechFinGen.finite_HO1_onAff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ U : X.affineOpens,
    Module.Finite Γ(X, U.1) (HO1 (GlobalTheory.DeRhamSheaf.onAff t.G U.2).hom) := by
  intro E _ _ _ H X t hp U
  letI : GrpObj (GlobalTheory.DeRhamSheaf.onAff t.G U.2) := Functor.grpObjObj
  have hA : IsAbelianScheme t.G := GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hp
  exact GlobalTheory.CechFinGen.finite_HO1 GlobalTheory.AbCoh.oStr (GlobalTheory.DeRhamSheaf.onAff t.G U.2) (GlobalTheory.DeRhamSheaf.isAbelianScheme_onAff hA U.2)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1FiniteAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_h1_finite_affine_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) (HO1 (GlobalTheory.DeRhamSheaf.onAff t.G U.2).hom) := by
  first | exact @GlobalTheory.CechFinGen.finite_HO1_onAff | exact GlobalTheory.CechFinGen.finite_HO1_onAff | (intros; apply GlobalTheory.CechFinGen.finite_HO1_onAff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSemiAbelianAffineOpenBaseChangeCompactCove
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSemiAbelianAffineOpenBaseChangeCompactCove
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

namespace GlobalTheory

theorem pullback_fromSpec_compact_affineCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → CompactSpace ↑(pullback t.G.hom U.2.fromSpec : Scheme.{0}) ∧ (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i)) ∧ ⨆ i, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i = ⊤ := by
  intro E _ _ _ H X t hP U J W hW hcov
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hU : IsAffineOpen U.1 := U.2
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : IsOpenImmersion (pullback.fst t.G.hom hU.fromSpec) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd t.G.hom hU.fromSpec)
  · intro I hI
    have := GlobalTheory.isAffineHom_diagonal_of_isSeparated (pullback.snd t.G.hom hU.fromSpec)
    refine GlobalTheory.isAffineOpen_finset_biInf (fun i => ?_) I hI
    have hle : W i ≤ (pullback.fst t.G.hom hU.fromSpec).opensRange := by
      intro x hx
      have hx' : x ∈ t.G.hom ⁻¹ᵁ U.1 := hcov ▸ (le_iSup W i) hx
      have hy : t.G.hom x ∈ Set.range hU.fromSpec := by
        rw [hU.range_fromSpec]; exact hx'
      obtain ⟨y, hy⟩ := hy
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      exact ⟨z, hz⟩
    rw [← (pullback.fst t.G.hom hU.fromSpec).isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hle]
    exact hW i
  · rw [← Scheme.Hom.preimage_iSup, hcov, ← Scheme.Hom.comp_preimage, pullback.condition,
      Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self, Scheme.Hom.preimage_top]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSemiAbelianAffineOpenBaseChangeCompactCoveStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properSemiAbelian_affineOpen_baseChange_compact_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → CompactSpace ↑(pullback t.G.hom U.2.fromSpec : Scheme.{0}) ∧ (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i)) ∧ ⨆ i, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i = ⊤ := by
  first | exact @GlobalTheory.pullback_fromSpec_compact_affineCover | exact GlobalTheory.pullback_fromSpec_compact_affineCover | (intros; apply GlobalTheory.pullback_fromSpec_compact_affineCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1FiniteGenerationAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin
open GlobalTheory.CatCoh GlobalTheory.CechDR

theorem isCoc_sub {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens) {c c' : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCoc W c) (hc' : IsCoc W c') : IsCoc W (fun i i' => c i i' - c' i i') := by
  intro i i' i''
  simp only [map_sub]
  linear_combination hc i i' i'' - hc' i i' i''

theorem cechFG_of_finite (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) [CompactSpace Z]
    (hfin : Module.Finite R (HO1 s)) (J : Type) (W : J → Z.Opens)
    (hD : ∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) (hc : ⨆ i, W i = ⊤) :
    CechFG W R (fun i i' => (secMap s (W i ⊓ W i')).hom) := by
  classical
  have hW : ∀ i, IsAffineOpen (W i) := fun i => by simpa using hD {i} (Finset.singleton_nonempty i)
  have hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i') := fun i i' => by
    have h := hD {i, i'} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_singleton] at h
  have hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'') := fun i i' i'' => by
    have h := hD {i, i', i''} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_insert, Finset.iInf_singleton, ← inf_assoc] at h
  obtain ⟨S, hS⟩ : ∃ S : Finset J, ⨆ i ∈ S, W i = ⊤ := by
    have hcov : (Set.univ : Set Z) ⊆ ⋃ i, (W i : Set Z) := by
      intro x _
      have hx : x ∈ ⨆ i, W i := hc ▸ trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx
    obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set Z)) (fun i => (W i).isOpen) hcov
    refine ⟨S, eq_top_iff.2 fun x _ => ?_⟩
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨hi, hx⟩⟩
  have hsur : ∀ c, IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i i',
      c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
    intro c hcoc
    obtain ⟨f, h₀, hf⟩ := GlobalTheory.T.cechCocycle_of_finite_affine_subcover R Z s J W hW hW2 hD S hS c hcoc
    obtain ⟨h, hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover Z J W (↑S) (fun i => by
        rw [show (⨆ a ∈ (↑S : Set J), W a) = ⨆ a ∈ S, W a from by simp, hS]; exact le_top)
      (fun i i' => c i i' - rho W s hW hW2 f.1 i i') (isCoc_sub W hcoc (rho_isCoc W s hW hW2 hW3 f)) h₀
      (fun a ha b hb => by rw [hf a ha b hb]; ring)
    exact ⟨f, h, fun i i' => by rw [← hh]; ring⟩
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := HO1 s)
  choose fk hfk using fun k => H1.mk_surjective (OAff s) (v k)
  refine ⟨n, fun k => rho W s hW hW2 (fk k).1, fun k => rho_isCoc W s hW hW2 hW3 (fk k), fun c hcoc => ?_⟩
  obtain ⟨f, h, hfh⟩ := hsur c hcoc
  have hmem : H1.mk (OAff s) f ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  have hcl : H1.mk (OAff s) f = H1.mk (OAff s) (∑ k, r k • fk k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hr]
    simp only [map_smul, hfk]
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hcl
  have e1 : f.1 = (∑ k, r k • (fk k).1) + d0 (OAff s) g := by
    rw [hg, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    abel
  refine ⟨r, fun i => h i + (-gv s g ⟨W i, hW i⟩), fun i i' => ?_⟩
  rw [hfh, e1, rho_add, rho_sum, rho_d0, map_add (f := _), map_add (f := _)]
  ring

end GlobalTheory.CechFin

open GlobalTheory.CechFin in
theorem GlobalTheory.CechFin.cech_h1_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP hA U J W hWaff hcov hWU
  obtain ⟨hcomp, hD, htop⟩ := GlobalTheory.T.properSemiAbelian_affineOpen_baseChange_compact_cover E H X t hP U J W hWaff hcov
  have hfin := GlobalTheory.T.structure_h1_finite_affine_open E H X t hP U
  exact GlobalTheory.T.cech_finite_generation_of_affine_base_change t.G.left X t.G.hom U J W hWU
    (cechFG_of_finite Γ(X, U.1) (pullback t.G.hom U.2.fromSpec) (pullback.snd t.G.hom U.2.fromSpec) hfin J _ hD htop)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1FiniteGenerationAffineStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h1_finite_generation_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  first | exact @GlobalTheory.CechFin.cech_h1_finite | exact GlobalTheory.CechFin.cech_h1_finite | (intros; apply GlobalTheory.CechFin.cech_h1_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleEqTopOfSupMaximalSmulEqTop
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

theorem submodule_eq_top_of_sup_maximal_smul_eq_top :
    ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
      (M : Submodule R N), (∀ m : Ideal R, m.IsMaximal → M ⊔ m • ⊤ = ⊤) → M = ⊤ := by
  intro R _ N _ _ _ M h

  have hQ : ∀ m : Ideal R, m.IsMaximal → (⊤ : Submodule R (N ⧸ M)) ≤ m • ⊤ := by
    intro m hm
    have h1 := congrArg (Submodule.map M.mkQ) (h m hm)
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
    have h2 : Submodule.map M.mkQ M = ⊥ := Submodule.mkQ_map_self M
    rw [h2, bot_sup_eq] at h1
    rw [h1]
  have hfg : (⊤ : Submodule R (N ⧸ M)).FG := Module.Finite.fg_top
  have hann : Module.annihilator R (N ⧸ M) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ hfg (hQ m hm)
    have hrm : r ∈ m := hle (Module.mem_annihilator.mpr fun q => hr q Submodule.mem_top)
    have : (1 : R) ∈ m := by
      have := m.sub_mem hrm hr1
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr this)
  rw [eq_top_iff]
  intro n _
  have h1 : (1 : R) ∈ Module.annihilator R (N ⧸ M) := hann ▸ Submodule.mem_top
  have h0 : (Submodule.Quotient.mk n : N ⧸ M) = 0 := by
    simpa using Module.mem_annihilator.mp h1 (Submodule.Quotient.mk n)
  exact (Submodule.Quotient.mk_eq_zero M).mp h0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.CechH1Span

theorem resG_appLE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {O O' : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (h : O' ≤ O)
    (r : Γ(X, U.1)) :
    resG t.G.left h ((t.G.hom.appLE U.1 O hO).hom r) = (t.G.hom.appLE U.1 O' (h.trans hO)).hom r := by
  show ((t.G.hom.appLE U.1 O hO) ≫ t.G.left.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]


set_option maxHeartbeats 1000000 in
theorem exists_dlog_add_coboundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (θ : Fin n → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) := by
  classical
  intro E _ _ _ H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj c hc
  let ρ : ∀ p : J × J, Γ(X, U.1) →+* Γ(t.G.left, W p.1 ⊓ W p.2) := fun p =>
    (t.G.hom.appLE U.1 (W p.1 ⊓ W p.2) (inf_le_left.trans (hWU p.1))).hom
  letI inst : ∀ p : J × J, Module Γ(X, U.1) Γ(t.G.left, W p.1 ⊓ W p.2) := fun p => Module.compHom _ (ρ p)
  have smul_apply : ∀ (r : Γ(X, U.1)) (x : ∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) (p : J × J),
      (r • x) p = ρ p r * x p := fun _ _ _ => rfl
  let Z : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    { carrier := {x | ∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (x (i, i')) +
          resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
            (x (i', i'')) =
          resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
            (x (i, i''))}
      add_mem' := by
        intro a b ha hb i i' i''
        simp only [Pi.add_apply, map_add (f := _)]
        rw [← ha i i' i'', ← hb i i' i'']
        abel
      zero_mem' := by
        intro i i' i''
        simp
      smul_mem' := by
        intro r x hx i i' i''
        simp only [smul_apply, map_mul]
        rw [← hx i i' i'']
        simp only [ρ, resG_appLE]
        ring }
  let Bd : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    { carrier := {x | ∃ h : ∀ i : J, Γ(t.G.left, W i), ∀ i i',
          x (i, i') = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i')}
      add_mem' := by
        rintro a b ⟨h1, e1⟩ ⟨h2, e2⟩
        refine ⟨h1 + h2, fun i i' => ?_⟩
        simp only [Pi.add_apply, map_add (f := _), e1, e2]
        ring
      zero_mem' := ⟨0, fun i i' => by simp⟩
      smul_mem' := by
        rintro r x ⟨h1, e1⟩
        refine ⟨fun i => (t.G.hom.appLE U.1 (W i) (hWU i)).hom r * h1 i, fun i i' => ?_⟩
        simp only [smul_apply, e1, map_mul, resG_appLE, ρ]
        ring }
  let κ : Fin n → (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) := fun b p =>
    δ b (W p.1 ⊓ W p.2) (resG t.G.left (inf_le_inf (hj p.1) (hj p.2)) (t.PP.L.g (j p.1) (j p.2)).val) *
      resG t.G.left (inf_le_inf (hj p.1) (hj p.2)) (t.PP.L.g (j p.1) (j p.2))⁻¹.val
  let S : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    Bd ⊔ Submodule.span Γ(X, U.1) (Set.range κ)
  let S' : Submodule Γ(X, U.1) Z := S.comap Z.subtype
  obtain ⟨N, e, he, hAe⟩ := GlobalTheory.T.cech_h1_finite_generation_affine E H X t hP hA U J W hWa hcov hWU
  let ek : Fin N → Z := fun k => ⟨fun p => e k p.1 p.2, he k⟩
  have hspan : Submodule.span Γ(X, U.1) (Set.range fun k => S'.mkQ (ek k)) = ⊤ := by
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := S'.mkQ_surjective q
    obtain ⟨r, h, hz⟩ := hAe (fun i i' => z.1 (i, i')) (z.2)
    have hmem : z - ∑ k, r k • ek k ∈ S' := by
      refine Submodule.mem_sup_left ⟨h, fun i i' => ?_⟩
      change z.1 (i, i') - (∑ k, r k • ek k).1 (i, i') = _
      rw [Submodule.coe_sum, Finset.sum_apply, hz i i']
      simp only [Submodule.coe_smul, smul_apply, ρ]
      exact add_sub_cancel_right _ _
    have : S'.mkQ z = ∑ k, r k • S'.mkQ (ek k) := by
      have h0 : S'.mkQ (z - ∑ k, r k • ek k) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum] at h0
      simp only [map_smul] at h0
      exact sub_eq_zero.1 h0
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI : Module.Finite Γ(X, U.1) (Z ⧸ S') := ⟨⟨Finset.univ.image fun k => S'.mkQ (ek k), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hspan⟩⟩
  have hbot := GlobalTheory.submodule_eq_top_of_sup_maximal_smul_eq_top Γ(X, U.1) (Z ⧸ S') ⊥ (fun m hm => by
    rw [bot_sup_eq]
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := S'.mkQ_surjective q
    obtain ⟨θ, h, N', r, e', hr, he', hz⟩ :=
      GlobalTheory.T.cechCocycle_eq_coboundary_add_logDerivatives_mod E H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj m hm
        (fun i i' => z.1 (i, i')) z.2
    let ek' : Fin N' → Z := fun k => ⟨fun p => e' k p.1 p.2, he' k⟩
    have hmem : z - ∑ k, r k • ek' k ∈ S' := by
      have hw : ∑ b, θ b • κ b ∈ Submodule.span Γ(X, U.1) (Set.range κ) :=
        Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
      have hy : (fun p : J × J => resG t.G.left (inf_le_left : W p.1 ⊓ W p.2 ≤ W p.1) (h p.1) -
          resG t.G.left (inf_le_right : W p.1 ⊓ W p.2 ≤ W p.2) (h p.2)) ∈ Bd := ⟨h, fun i i' => rfl⟩
      change (z - ∑ k, r k • ek' k : Z).1 ∈ S
      refine Submodule.mem_sup.2 ⟨_, hy, _, hw, ?_⟩
      funext p
      obtain ⟨i, i'⟩ := p
      change _ = z.1 (i, i') - (∑ k, r k • ek' k).1 (i, i')
      rw [Submodule.coe_sum, Finset.sum_apply, Pi.add_apply, Finset.sum_apply, hz i i']
      simp only [Submodule.coe_smul, smul_apply, ρ, κ]
      exact (add_sub_cancel_right _ _).symm
    have hq : S'.mkQ z = ∑ k, r k • S'.mkQ (ek' k) := by
      have h0 : S'.mkQ (z - ∑ k, r k • ek' k) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum] at h0
      simp only [map_smul] at h0
      exact sub_eq_zero.1 h0
    rw [hq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (hr k) Submodule.mem_top)
  let cz : Z := ⟨fun p => c p.1 p.2, hc⟩
  have hcz : S'.mkQ cz = 0 := by
    have : S'.mkQ cz ∈ (⊥ : Submodule Γ(X, U.1) (Z ⧸ S')) := hbot ▸ Submodule.mem_top
    exact (Submodule.mem_bot _).1 this
  have hcS0 : cz ∈ S' := (Submodule.Quotient.mk_eq_zero S').1 hcz
  have hcS : cz.1 ∈ S := hcS0
  obtain ⟨y, ⟨h, hy⟩, w, hw, hyw⟩ := Submodule.mem_sup.1 hcS
  obtain ⟨θ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hw
  refine ⟨θ, h, fun i i' => ?_⟩
  have k := congrFun hyw (i, i')
  change _ = c i i' at k
  rw [← k, Pi.add_apply, hy i i', Finset.sum_apply]
  simp only [smul_apply, ρ, κ]

end GlobalTheory.CechH1Span
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesAffineStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_eq_coboundary_add_logDerivatives_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (θ : Fin n → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) := by
  first | exact @GlobalTheory.CechH1Span.exists_dlog_add_coboundary | exact GlobalTheory.CechH1Span.exists_dlog_add_coboundary | (intros; apply GlobalTheory.CechH1Span.exists_dlog_add_coboundary <;> assumption)
end

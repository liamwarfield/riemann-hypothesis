module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherBis

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsHomogeneousGeneratorsIdealSheafClosedImmer
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace UpperTheory.HomogeneousExtension

private lemma exists_pow_mul_mem {Z : Scheme.{0}} (I : Z.IdealSheafData) (U : Z.affineOpens)
    (t g : Γ(Z, U))
    (hg : Z.presheaf.map (homOfLE (Z.basicOpen_le t)).op g ∈ I.ideal (Z.affineBasicOpen t)) :
    ∃ e : ℕ, t ^ e * g ∈ I.ideal U := by
  have inst := U.2.isLocalization_basicOpen t
  rw [← I.map_ideal_basicOpen U t] at hg
  have h1 : (Z.presheaf.map (homOfLE (Z.basicOpen_le t)).op).hom = algebraMap _ _ := rfl
  rw [h1] at hg
  change algebraMap _ _ g ∈ _ at hg
  obtain ⟨_, ⟨e, rfl⟩, he⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers t) _ _ _).1 hg
  exact ⟨e, he⟩

variable {R : Type} [CommRing R] {N : ℕ} {Z : Scheme.{0}} (i : Z ⟶ PSpace R N)

private noncomputable def phi (a : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) R →+* Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) :=
  (i.appLE _ _ le_rfl).hom.comp (chartHom a)

private lemma phi_X_self (a : Fin (N + 1)) : phi i a (X a) = 1 := by
  simp [phi, chartHom_X_self]

private lemma isAffineOpen_U [IsClosedImmersion i] (a : Fin (N + 1)) :
    IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) := by
  have h : IsAffineOpen (Proj.basicOpen (grading R N) (X a)) :=
    Proj.isAffineOpen_basicOpen (grading R N) (X a) (X_mem a) one_pos
  exact h.preimage i

private lemma exists_homog_chartHom (a : Fin (N + 1))
    (s : Γ(PSpace R N, Proj.basicOpen (grading R N) (X a))) :
    ∃ (d : ℕ) (G : MvPolynomial (Fin (N + 1)) R), G ∈ grading R N d ∧ chartHom a G = s := by
  let e := Proj.basicOpenIsoAway (grading R N) (X a) (X_mem a) one_pos
  obtain ⟨d, G, hG, hx⟩ := HomogeneousLocalization.Away.mk_surjective (grading R N) (X_mem a) (e.inv s)
  have hG' : G ∈ grading R N d := by simpa using hG
  refine ⟨d, G, hG', ?_⟩
  rw [chartHom_of_mem a hG']
  have h1 : (Proj.awayToSection (grading R N) (X a)).hom (e.inv s) = s := by
    have := e.inv_hom_id_apply s
    exact this
  rw [← h1, ← hx]

private lemma exists_homog_phi [IsClosedImmersion i] (a : Fin (N + 1))
    (h : Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))) :
    ∃ (d : ℕ) (G : MvPolynomial (Fin (N + 1)) R), G ∈ grading R N d ∧ phi i a G = h := by
  obtain ⟨s, hs⟩ := i.app_surjective _
    (Proj.isAffineOpen_basicOpen (grading R N) (X a) (X_mem a) one_pos) h
  obtain ⟨d, G, hG, hGs⟩ := exists_homog_chartHom a s
  refine ⟨d, G, hG, ?_⟩
  simp only [phi, RingHom.comp_apply, hGs, ← Scheme.Hom.app_eq_appLE]
  exact hs

private lemma phi_surjective [IsClosedImmersion i] (a : Fin (N + 1)) :
    Function.Surjective (phi i a) := fun h => by
  obtain ⟨_, G, _, hG⟩ := exists_homog_phi i a h
  exact ⟨G, hG⟩

private lemma basicOpen_phi_X (a b : Fin (N + 1)) :
    Z.basicOpen (phi i b (X a)) = i ⁻¹ᵁ Proj.basicOpen (grading R N) (X b) ⊓
      i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) := by
  simp only [phi, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp, Scheme.basicOpen_res,
    ← Scheme.preimage_basicOpen]
  have e := basicOpen_chartHom_X (A := R) (n := N) b a
  erw [e]
  ext x
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, Scheme.Hom.mem_preimage,
    SetLike.mem_coe, TopologicalSpace.Opens.mem_inf]
  tauto

private lemma phi_res (a b : Fin (N + 1)) {d : ℕ} {G : MvPolynomial (Fin (N + 1)) R}
    (hG : G ∈ grading R N d) (ha : Z.basicOpen (phi i b (X a)) ≤
      i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) :
    Z.presheaf.map (homOfLE (Z.basicOpen_le (phi i b (X a)))).op (phi i b G) =
      Z.presheaf.map (homOfLE ha).op (phi i a G) *
        Z.presheaf.map (homOfLE (Z.basicOpen_le (phi i b (X a)))).op (phi i b (X a)) ^ d := by
  set V := Z.basicOpen (phi i b (X a)) with hV
  have hWV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grading R N) (X b * X a) := by
    rw [hV, basicOpen_phi_X, Proj.basicOpen_mul]
    intro x hx
    simpa using hx
  have nat : ∀ (k : Fin (N + 1)) (s : Γ(PSpace R N, Proj.basicOpen (grading R N) (X k)))
      (hk : V ≤ i ⁻¹ᵁ Proj.basicOpen (grading R N) (X k))
      (hW : Proj.basicOpen (grading R N) (X b * X a) ≤ Proj.basicOpen (grading R N) (X k)),
      Z.presheaf.map (homOfLE hk).op ((i.appLE _ _ le_rfl).hom s) =
        (i.appLE _ V hWV).hom ((PSpace R N).presheaf.map (homOfLE hW).op s) := by
    intro k s hk hW
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have ci := chart_identity (A := R) (n := N) a b (t := d) (a := G) (by simpa using hG)
  rw [← chartHom_of_mem a hG] at ci
  have e1 := nat b (chartHom b G) (Z.basicOpen_le _) (basicOpen_mul_le_left a b)
  have e2 := nat a (chartHom a G) ha (basicOpen_mul_le_right a b)
  have e3 := nat b (chartHom b (X a)) (Z.basicOpen_le _) (basicOpen_mul_le_left a b)
  change Z.presheaf.map _ ((i.appLE _ _ le_rfl).hom (chartHom b G)) =
    Z.presheaf.map _ ((i.appLE _ _ le_rfl).hom (chartHom a G)) *
      Z.presheaf.map _ ((i.appLE _ _ le_rfl).hom (chartHom b (X a))) ^ d
  rw [e1, e2, e3, ← map_pow, ← map_mul]
  exact congrArg (i.appLE _ V hWV).hom ci.symm

private lemma exists_pow_mul_phi_mem [IsClosedImmersion i] (I : Z.IdealSheafData)
    (a b : Fin (N + 1)) {d : ℕ} {G : MvPolynomial (Fin (N + 1)) R} (hG : G ∈ grading R N d)
    (hI : phi i a G ∈ I.ideal ⟨_, isAffineOpen_U i a⟩) :
    ∃ e : ℕ, phi i b (X a) ^ e * phi i b G ∈ I.ideal ⟨_, isAffineOpen_U i b⟩ := by
  have ha : Z.basicOpen (phi i b (X a)) ≤ i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) := by
    rw [basicOpen_phi_X]
    exact inf_le_right
  refine exists_pow_mul_mem I ⟨_, isAffineOpen_U i b⟩ (phi i b (X a)) (phi i b G) ?_
  have hle : Z.affineBasicOpen (U := ⟨_, isAffineOpen_U i b⟩) (phi i b (X a)) ≤ ⟨_, isAffineOpen_U i a⟩ := ha
  have hmem := I.ideal_le_comap_ideal hle hI
  rw [Ideal.mem_comap] at hmem
  rw [phi_res i a b hG ha, mul_comm]
  exact Ideal.mul_mem_left _ _ hmem

private lemma exists_extension [IsClosedImmersion i] (I : Z.IdealSheafData) (a : Fin (N + 1))
    (h : Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)))
    (hI : h ∈ I.ideal ⟨_, isAffineOpen_U i a⟩) :
    ∃ d₀ : ℕ, ∀ n, d₀ ≤ n → ∃ G : MvPolynomial (Fin (N + 1)) R, G.IsHomogeneous n ∧
      phi i a G = h ∧ ∀ b, phi i b G ∈ I.ideal ⟨_, isAffineOpen_U i b⟩ := by
  obtain ⟨d, G, hG, rfl⟩ := exists_homog_phi i a h
  have key : ∀ b, ∃ e : ℕ, phi i b (X a) ^ e * phi i b G ∈ I.ideal ⟨_, isAffineOpen_U i b⟩ :=
    fun b => exists_pow_mul_phi_mem i I a b hG hI
  choose e he using key
  refine ⟨d + Finset.univ.sup e, fun n hn => ⟨X a ^ (n - d) * G, ?_, ?_, ?_⟩⟩
  · have hGd : G.IsHomogeneous d := (mem_homogeneousSubmodule d G).mp hG
    have hmul := (isHomogeneous_X_pow a (n - d) : (X a ^ (n - d) : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (n - d)).mul hGd
    rwa [Nat.sub_add_cancel (by omega)] at hmul
  · simp [phi_X_self]
  · intro b
    have hle : e b ≤ n - d := by
      have : e b ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ b)
      omega
    rw [map_mul, map_pow, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact Ideal.mul_mem_left _ _ (he b)

end UpperTheory.HomogeneousExtension

open UpperTheory.HomogeneousExtension in
theorem UpperTheory.exists_homogeneous_generators_idealSheaf_closedImmersion :
    ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {N : ℕ} {Z : Scheme.{0}} (i : Z ⟶ PSpace R N) [IsClosedImmersion i] (I : Z.IdealSheafData),
      ∃ (n M : ℕ) (F : Fin (M + 1) → MvPolynomial (Fin (N + 1)) R), (∀ m, (F m).IsHomogeneous n) ∧
        ∀ (a : Fin (N + 1)) (hU : IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))),
          Ideal.span (Set.range fun m => i.appLE _ _ le_rfl (chartHom a (F m))) = I.ideal ⟨_, hU⟩ := by
  intro R _ _ N Z i _ I
  have hfg : ∀ a : Fin (N + 1), (I.ideal ⟨_, isAffineOpen_U i a⟩).FG := by
    intro a
    haveI : IsNoetherianRing Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) :=
      isNoetherianRing_of_surjective _ _ (phi i a) (phi_surjective i a)
    exact IsNoetherian.noetherian _
  choose gens hgens using hfg
  have hext : ∀ p : (Σ a : Fin (N + 1), (gens a : Set Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)))),
      ∃ d₀ : ℕ, ∀ n, d₀ ≤ n → ∃ G : MvPolynomial (Fin (N + 1)) R, G.IsHomogeneous n ∧
        phi i p.1 G = p.2.1 ∧ ∀ b, phi i b G ∈ I.ideal ⟨_, isAffineOpen_U i b⟩ := by
    rintro ⟨a, h, hh⟩
    exact exists_extension i I a h (hgens a ▸ Ideal.subset_span hh)
  choose d₀ hd₀ using hext
  let n := Finset.univ.sup d₀
  have hG := fun p => hd₀ p n (Finset.le_sup (Finset.mem_univ p))
  choose G hGh hGa hGb using hG
  let M := Fintype.card (Σ a : Fin (N + 1), (gens a : Set Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))))
  let e := Fintype.equivFin (Σ a : Fin (N + 1), (gens a : Set Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))))
  let F : Fin (M + 1) → MvPolynomial (Fin (N + 1)) R := fun m =>
    if hm : (m : ℕ) < M then G (e.symm ⟨m, hm⟩) else 0
  refine ⟨n, M, F, ?_, ?_⟩
  · intro m
    by_cases hm : (m : ℕ) < M
    · simp only [F, dif_pos hm]
      exact hGh _
    · simp only [F, dif_neg hm]
      exact MvPolynomial.isHomogeneous_zero _ _ _
  · intro a hU
    change Ideal.span (Set.range fun m => phi i a (F m)) = I.ideal ⟨_, isAffineOpen_U i a⟩
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨m, rfl⟩
      by_cases hm : (m : ℕ) < M
      · simp only [F, dif_pos hm]
        exact hGb _ a
      · simp only [F, dif_neg hm, map_zero]
        exact Ideal.zero_mem _
    · rw [← hgens a, Ideal.span_le]
      intro h hh
      let p : (Σ a : Fin (N + 1), (gens a : Set Γ(Z, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)))) :=
        ⟨a, h, hh⟩
      refine Ideal.subset_span ⟨⟨e p, by omega⟩, ?_⟩
      have hlt : ((⟨e p, by omega⟩ : Fin (M + 1)) : ℕ) < M := (e p).2
      simp only [F, dif_pos hlt]
      simp only [Fin.eta, Equiv.symm_apply_apply]
      exact hGa p
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.CechCocycleLineBundle
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma eval₂_scale {A S : Type*} [CommRing A] [CommRing S] {n : ℕ} (g : A →+* S)
    (x : Fin n → S) (w : S) {m : ℕ} {a : MvPolynomial (Fin n) A} (ha : a.IsHomogeneous m) :
    eval₂ g (fun l => w * x l) a = w ^ m * eval₂ g x a :=
  _root_.UpperTheory.Reformulated.B.Qk57.eval₂_scale g x w ha

set_option backward.isDefEq.respectTransparency false in
private lemma homOfLE_appTop_topIso {W : Scheme.{0}} {U U' : W.Opens} (e : U' ≤ U) (x : Γ(W, U)) :
    (W.homOfLE e).appTop (U.topIso.inv x) = U'.topIso.inv (W.presheaf.map (homOfLE e).op x) := by
  rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun t => (W.presheaf.map t) x) (Subsingleton.elim _ _)

private noncomputable def rho {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) :
    R →+* Γ(W, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ s.appTop).hom

private lemma toSpecΓ_rho {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) :
    W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (rho s)) = s := by
  refine ext_to_Spec ?_
  change (Scheme.ΓSpecIso _).inv ≫ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (rho s))).appTop =
    (Scheme.ΓSpecIso _).inv ≫ s.appTop
  rw [ProjHom.specCorr_comp, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

section
variable {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) {M : ℕ}

private noncomputable def phi (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) :
    MvPolynomial (Fin (M + 1)) R →+* Γ(U, ⊤) :=
  eval₂Hom (U.ι.appTop.hom.comp (rho s)) fun l => U.topIso.inv (x l)

private lemma phi_X (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (l : Fin (M + 1)) :
    phi s U x (X l) = U.topIso.inv (x l) := by
  simp [phi]

private lemma phi_C (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (r : R) :
    phi s U x (C r) = U.ι.appTop (rho s r) := by
  simp [phi]

private lemma phi_irr (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1)) (hx : x m = 1) :
    (HomogeneousIdeal.irrelevant (grading R M)).toIdeal.map (phi s U x) = ⊤ :=
  map_irrelevant_eq_top _ m (by rw [phi_X, hx, map_one]; exact isUnit_one)

private noncomputable def loc (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1))
    (hx : x m = 1) : U.toScheme ⟶ PSpace R M :=
  Proj.fromOfGlobalSections (grading R M) (phi s U x) (phi_irr s U x m hx)

private lemma loc_agree {U U' : W.Opens} (x : Fin (M + 1) → Γ(W, U)) (x' : Fin (M + 1) → Γ(W, U'))
    (m m' : Fin (M + 1)) (hx : x m = 1) (hx' : x' m' = 1)
    (hrel : ∀ l k, W.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (x l) *
        W.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op (x' k) =
      W.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op (x k) *
        W.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op (x' l)) :
    W.homOfLE (inf_le_left : U ⊓ U' ≤ U) ≫ loc s U x m hx =
      W.homOfLE (inf_le_right : U ⊓ U' ≤ U') ≫ loc s U' x' m' hx' := by
  unfold loc
  rw [ProjHom.comp_fromOfGlobalSections _ _ (fun l => (X l : MvPolynomial (Fin (M + 1)) R))
      (fun _ => 1) (fun _ => one_pos) (fun l => X_mem l) iSup_basicOpen_X,
    ProjHom.comp_fromOfGlobalSections _ _ (fun l => (X l : MvPolynomial (Fin (M + 1)) R))
      (fun _ => 1) (fun _ => one_pos) (fun l => X_mem l) iSup_basicOpen_X]
  set ψ := (W.homOfLE (inf_le_left : U ⊓ U' ≤ U)).appTop.hom.comp (phi s U x) with hψ
  set ψ' := (W.homOfLE (inf_le_right : U ⊓ U' ≤ U')).appTop.hom.comp (phi s U' x') with hψ'
  have hX : ∀ l, ψ (X l) = (U ⊓ U').topIso.inv (W.presheaf.map (homOfLE inf_le_left).op (x l)) :=
    fun l => by
      rw [hψ, RingHom.comp_apply, phi_X]
      exact homOfLE_appTop_topIso _ _
  have hX' : ∀ l, ψ' (X l) = (U ⊓ U').topIso.inv (W.presheaf.map (homOfLE inf_le_right).op (x' l)) :=
    fun l => by
      rw [hψ', RingHom.comp_apply, phi_X]
      exact homOfLE_appTop_topIso _ _
  have hC : ∀ r, ψ (C r) = ψ' (C r) := fun r => by
    rw [hψ, hψ', RingHom.comp_apply, RingHom.comp_apply, phi_C, phi_C]
    change ((U.ι.appTop ≫ (W.homOfLE (inf_le_left : U ⊓ U' ≤ U)).appTop) _) =
      ((U'.ι.appTop ≫ (W.homOfLE (inf_le_right : U ⊓ U' ≤ U')).appTop) _)
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have hm : ψ (X m) = 1 := by rw [hX, hx, map_one, map_one]
  have hm' : ψ' (X m') = 1 := by rw [hX', hx', map_one, map_one]
  have hrel' : ∀ l k, ψ (X l) * ψ' (X k) = ψ (X k) * ψ' (X l) := fun l k => by
    rw [hX, hX, hX', hX', ← map_mul, ← map_mul, hrel]
  have hw : IsUnit (ψ (X m')) :=
    IsUnit.of_mul_eq_one (ψ' (X m)) (by rw [← hrel' m m', hm, hm', one_mul])
  have hsc : ∀ l, ψ (X l) = ψ (X m') * ψ' (X l) := fun l => by
    rw [← hrel' l m', hm', mul_one]
  refine ProjHom.fromOfGlobalSections_eq_of_twist _ _ (fun l => X l) (fun _ => 1) (fun _ => one_pos)
    (fun l => X_mem l) iSup_basicOpen_X _ _ (ψ (X m')) hw fun d a ha => ?_
  have e1 : ψ = eval₂Hom (ψ'.comp C) fun l => ψ (X m') * ψ' (X l) :=
    MvPolynomial.ringHom_ext (fun r => by simp [hC]) (fun l => by simp [hsc l])
  have e2 : ψ' = eval₂Hom (ψ'.comp C) fun l => ψ' (X l) :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun l => by simp)
  calc ψ a = eval₂ (ψ'.comp C) (fun l => ψ (X m') * ψ' (X l)) a := by
        conv_lhs => rw [e1]
        rfl
    _ = ψ (X m') ^ d * eval₂ (ψ'.comp C) (fun l => ψ' (X l)) a := eval₂_scale _ _ _ ha
    _ = ψ (X m') ^ d * ψ' a := by
        congr 1
        conv_rhs => rw [e2]
        rfl
end

section
variable {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) {M : ℕ}

private lemma rho_comp {Y : Scheme.{0}} (h : Y ⟶ W) (r : R) : rho (h ≫ s) r = h.appTop (rho s r) := by
  rw [rho, Scheme.Hom.comp_appTop]
  rfl

private lemma loc_str (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1)) (hx : x m = 1) :
    loc s U x m hx ≫ PSpace.str R M = U.ι ≫ s := by
  unfold loc
  rw [PSpace.str, Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp]
  conv_rhs => rw [← toSpecΓ_rho (U.ι ≫ s)]
  congr 2
  ext r
  refine Eq.trans ?_ (rho_comp s U.ι r).symm
  refine Eq.trans ?_ (phi_C s U x r)
  rfl

private lemma loc_preimage (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m : Fin (M + 1))
    (hx : x m = 1) : loc s U x m hx ⁻¹ᵁ Proj.basicOpen (grading R M) (X m) = ⊤ := by
  unfold loc
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (grading R M) _ _ one_pos (X_mem m), phi_X, hx,
    map_one]
  exact Scheme.basicOpen_of_isUnit _ isUnit_one

set_option backward.isDefEq.respectTransparency false in
private lemma loc_coord (U : W.Opens) (x : Fin (M + 1) → Γ(W, U)) (m l : Fin (M + 1))
    (hx : x m = 1) (g : U.toScheme ⟶ PSpace R M) (hg : g = loc s U x m hx)
    (e : ⊤ ≤ g ⁻¹ᵁ Proj.basicOpen (grading R M) (X m)) :
    g.appLE _ ⊤ e (chartHom m (X l)) = U.topIso.inv (x l) := by
  subst hg
  have hb : U.toScheme.basicOpen (phi s U x (X m)) = ⊤ := by
    rw [phi_X, hx, map_one]
    exact Scheme.basicOpen_of_isUnit _ isUnit_one
  have hmem : (X l : MvPolynomial (Fin (M + 1)) R) ∈ grading R M (1 • 1) := by
    simpa using X_mem l
  have key := ProjHom.corr_fromOfGlobalSections' (grading R M) (phi s U x) (phi_irr s U x m hx)
    one_pos (X_mem m) ⊤ hb e 1 (X l) hmem
  rw [ProjHom.corr_apply, phi_X, phi_X, hx, map_one, map_one, one_pow, mul_one,
    ProjHom.ι_appTop_eq] at key
  have key2 := congrArg (Scheme.Opens.topIso (⊤ : U.toScheme.Opens)).hom key
  simp only [Iso.inv_hom_id_apply] at key2
  rw [chartHom_of_mem m (X_mem l)]
  refine Eq.trans key2 ?_
  have : (homOfLE le_top : (⊤ : U.toScheme.Opens) ⟶ ⊤).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma appLE_ι {Y : Scheme.{0}} (f : W ⟶ Y) (O : Y.Opens) (U : W.Opens)
    (h : U ≤ f ⁻¹ᵁ O) (e : ⊤ ≤ (U.ι ≫ f) ⁻¹ᵁ O) (y : Γ(Y, O)) :
    (U.ι ≫ f).appLE O ⊤ e y = U.topIso.inv (f.appLE O U h y) := by
  rw [← Scheme.Hom.appLE_comp_appLE U.ι f O U ⊤ h (by simp), CommRingCat.comp_apply,
    Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg (fun t => (W.presheaf.map t) (f.appLE O U h y)) (Subsingleton.elim _ _)
end

theorem UpperTheory.cech_cocycle_line_bundle :
    ∀ {R : Type} [CommRing R] {W : Scheme.{0}} (s : W ⟶ Sp R) (M : ℕ) {ι : Type}
        (V : ι → W.Opens), iSup V = ⊤ → ∀ (μ : ι → Fin (M + 1)) (c : ∀ i, Fin (M + 1) → Γ(W, V i)),
        (∀ i, c i (μ i) = 1) →
        (∀ i j l k, W.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i l) *
            W.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j k) =
          W.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i k) *
            W.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j l)) →
        ∃ f : W ⟶ PSpace R M, f ≫ PSpace.str R M = s ∧ ∀ i,
          ∃ h : V i ≤ f ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)), ∀ l,
            f.appLE _ (V i) h (chartHom (μ i) (X l)) = c i l := by
  intro R _ W s M ι V hV μ c h1 h2
  let cov := W.openCoverOfIsOpenCover V hV
  let fi : ∀ i, (V i).toScheme ⟶ PSpace R M := fun i => loc s (V i) (c i) (μ i) (h1 i)
  have hag : ∀ i j : ι, pullback.fst (cov.f i) (cov.f j) ≫ fi i =
      pullback.snd (cov.f i) (cov.f j) ≫ fi j := fun i j => by
    have H := isPullback_opens_inf (V i) (V j)
    change pullback.fst (V i).ι (V j).ι ≫ fi i = pullback.snd (V i).ι (V j).ι ≫ fi j
    rw [← H.isoPullback_inv_fst, ← H.isoPullback_inv_snd, Category.assoc, Category.assoc,
      loc_agree s (c i) (c j) (μ i) (μ j) (h1 i) (h1 j) (h2 i j)]
  let f : W ⟶ PSpace R M := cov.glueMorphisms fi hag
  have hι : ∀ i, (V i).ι ≫ f = fi i := fun i => cov.ι_glueMorphisms fi hag i
  refine ⟨f, ?_, fun i => ?_⟩
  · refine cov.hom_ext _ _ fun i => ?_
    have hi : (V i).ι ≫ f ≫ PSpace.str R M = (V i).ι ≫ s := by
      rw [← Category.assoc, hι i]
      exact loc_str s (V i) (c i) (μ i) (h1 i)
    exact hi
  · have hpre : ((V i).ι ≫ f) ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)) = ⊤ := by
      rw [hι i]
      exact loc_preimage s (V i) (c i) (μ i) (h1 i)
    have hle : V i ≤ f ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)) := fun x hx => by
      have hx' : (⟨x, hx⟩ : (V i).toScheme) ∈
          ((V i).ι ≫ f) ⁻¹ᵁ Proj.basicOpen (grading R M) (X (μ i)) := by
        rw [hpre]
        trivial
      exact hx'
    refine ⟨hle, fun l => ?_⟩
    have h3 := appLE_ι f _ (V i) hle hpre.ge (chartHom (μ i) (X l))
    rw [loc_coord s (V i) (c i) (μ i) l (h1 i) _ (hι i) hpre.ge] at h3
    have h4 := congrArg (V i).topIso.hom h3
    simpa only [Iso.inv_hom_id_apply] using h4.symm
end

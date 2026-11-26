module

public import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf
public import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2
public import Development.EtaleCohomology.EtaleSheaves.LeafDegCut
public import Development.EtaleCohomology.EtaleSheaves.KummerInduction.StepKOf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.PointwisePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.PointwisePf

def PushColim : Prop := ∀ {D Y' O : CommRingCat.{0}} (φ' : D ⟶ Y') (o : D ⟶ O) {J : Type} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{0}) (t : (Functor.const J).obj D ⟶ F) (s : F ⟶ (Functor.const J).obj O),
  IsColimit (Cocone.mk O s) → (∀ j, t.app j ≫ s.app j = o) →
  ∃ (G : J ⥤ CommRingCat.{0}) (c : Cocone G) (_ : IsColimit c) (u : ∀ j, Y' ⟶ G.obj j) (ψ : ∀ j, F.obj j ⟶ G.obj j)
    (u'' : Y' ⟶ c.pt) (φ'' : O ⟶ c.pt),
    (∀ j, IsPushout φ' (t.app j) (u j) (ψ j)) ∧ (∀ {j k : J} (f : j ⟶ k), u j ≫ G.map f = u k) ∧
    (∀ {j k : J} (f : j ⟶ k), ψ j ≫ G.map f = F.map f ≫ ψ k) ∧ (∀ j, u j ≫ c.ι.app j = u'') ∧
    (∀ j, ψ j ≫ c.ι.app j = s.app j ≫ φ'') ∧ IsPushout φ' o u'' φ''

theorem pc (q : ℕ) (i m : ℤ) {X Y Z : CommRingCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (v : H (ZMod q) (sch.obj (Spec X)) (tw q i) m) :
    pull _ (sch.map (Spec.map g)) (tw q i) m (pull _ (sch.map (Spec.map f)) (tw q i) m v) =
      pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) m v := by
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

theorem unit_of {A B : CommRingCat.{0}} (h : A ⟶ B) (q : ℕ) (hq : IsUnit (q : A)) : IsUnit (q : B) := by
  have := hq.map h.hom; simpa using this

theorem Pointwise_of_pushColim (hPC : PushColim) : LateralTheory.E.KillCokPf.Pointwise := by
  intro hB1 q _ i A Y φ hq D d O o hIE hBC Y' w φ' hpo m y Q hQ
  obtain ⟨J, _, _, F, t, s, hs, ht⟩ := hIE
  have ho : ∀ j, t.app j ≫ s.app j = o := fun j => (ht j).2
  obtain ⟨G, c, hc, u, ψ, u'', φ'', hpj, hu, hψ, hcu, hcψ, hpo''⟩ := hPC φ' o F t s hs ho
  have hRE : RE q i φ'' := hBC _ (w ≫ u'') φ'' (hpo.paste_vert hpo'')
  obtain ⟨z, hz⟩ := (hRE m).2 (pull _ (sch.map (Spec.map u'')) (tw q i) m y)
  obtain ⟨j, zj, hzj⟩ := (hB1 q F (Cocone.mk O s) hs m i).1 z (unit_of (d ≫ o) q hq)
  change pull _ (sch.map (Spec.map (s.app j))) (tw q i) m zj = z at hzj
  let x : H (ZMod q) (sch.obj (Spec (G.obj j))) (tw q i) m :=
    pull _ (sch.map (Spec.map (u j))) (tw q i) m y - pull _ (sch.map (Spec.map (ψ j))) (tw q i) m zj
  have hx0 : pull _ (sch.map (Spec.map (c.ι.app j))) (tw q i) m x = 0 := by
    simp only [x, map_sub, pc, hcu, hcψ, ← hz, ← hzj]
    exact sub_self _
  obtain ⟨k, f, hk⟩ := (hB1 q G c hc m i).2 j x (unit_of (d ≫ t.app j ≫ ψ j) q hq) hx0
  change pull _ (sch.map (Spec.map (G.map f))) (tw q i) m x = 0 at hk
  refine ⟨F.obj k, t.app k, Q.comap (s.app k).hom, (ht k).1, Ideal.comap_isPrime _ _, ?_, G.obj k, u k, ψ k, hpj k,
    pull _ (sch.map (Spec.map (F.map f))) (tw q i) m zj, ?_⟩
  · rw [Ideal.comap_comap, ← ho k]; rfl
  · simp only [x, map_sub, pc, hu, hψ, sub_eq_zero] at hk
    rw [pc, hk]

@[simps]
def dgm {D : CommRingCat.{0}} {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat.{0}) (t : (Functor.const J).obj D ⟶ F) :
    J ⥤ Under D where
  obj j := Under.mk (t.app j)
  map {j k} f := Under.homMk (F.map f) (by simpa using (t.naturality f).symm)
  map_id j := by ext; simp
  map_comp f g := by ext; simp

@[simps]
def cone {D O : CommRingCat.{0}} (o : D ⟶ O) {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj D ⟶ F) (s : F ⟶ (Functor.const J).obj O) (ho : ∀ j, t.app j ≫ s.app j = o) :
    Cocone (dgm F t) where
  pt := Under.mk o
  ι := { app j := Under.homMk (s.app j) (by exact ho j)
         naturality j k f := by ext1; exact (s.naturality f).trans (Category.comp_id _) }

theorem pushColim : PushColim := by
  intro D Y' O φ' o J _ _ F t s hs ho
  have : ReflectsColimitsOfShape J (Under.forget D) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : (Under.pushout φ').IsLeftAdjoint := ⟨_, ⟨Under.mapPushoutAdj φ'⟩⟩
  have h1 : IsColimit ((Under.forget D).mapCocone (cone o F t s ho)) :=
    IsColimit.ofIsoColimit hs (Cocone.ext (Iso.refl _) (by intro j; exact Category.comp_id _))
  have hK : IsColimit (cone o F t s ho) := isColimitOfReflects (Under.forget D) h1
  have hP := isColimitOfPreserves (Under.pushout φ') hK
  have hc := isColimitOfPreserves (Under.forget Y') hP
  refine ⟨_, _, hc, fun j => pushout.inr (t.app j) φ', fun j => pushout.inl (t.app j) φ', pushout.inr o φ', pushout.inl o φ',
    fun j => (IsPushout.of_hasPushout (t.app j) φ').flip, ?_, ?_, ?_, ?_, (IsPushout.of_hasPushout o φ').flip⟩
  · intro j k f; simp [Under.pushout]; exact pushout.inr_desc _ _ _
  · intro j k f; simp [Under.pushout]; exact pushout.inl_desc _ _ _
  · intro j; simp [Under.pushout]; exact pushout.inr_desc _ _ _
  · intro j; simp [Under.pushout]; exact pushout.inl_desc _ _ _

end LateralTheory.E.PointwisePf

namespace LateralTheory.E.PointwisePf

end LateralTheory.E.PointwisePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PushGluePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.KillCokPf.Asm
open scoped TensorProduct

namespace LateralTheory.E.PushGluePf

abbrev pS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    H R (sch.obj (Spec A)) F n →+ H R (sch.obj (Spec B)) F n :=
  pull R (sch.map (Spec.map f)) F n

theorem pS_comp (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : H R (sch.obj (Spec A)) F n) : pS R F n (f ≫ g) x = pS R F n g (pS R F n f x) := by
  simp only [pS]; rw [Spec.map_comp, Functor.map_comp, pull_comp]

abbrev ev {ι : Type} (Y : ι → CommRingCat.{0}) (j : ι) : CommRingCat.of (∀ k, Y k) ⟶ Y j :=
  CommRingCat.ofHom (Pi.evalRingHom (fun k => Y k) j)

theorem pull_iso_bij (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {E E' : Spc} (g : E ⟶ E') [IsIso g] :
    Function.Bijective (pull R g F n) := by
  have h1 : ∀ x, pull R (inv g) F n (pull R g F n x) = x := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R g F n (pull R (inv g) F n x) = x := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem pi_bij (hC : Coprod) (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {ι : Type} [Finite ι]
    (Y : ι → CommRingCat.{0}) :
    Function.Bijective fun (x : H R (sch.obj (Spec (CommRingCat.of (∀ k, Y k)))) F n) (j : ι) => pS R F n (ev Y j) x := by
  have h : (fun (x : H R (sch.obj (Spec (CommRingCat.of (∀ k, Y k)))) F n) (j : ι) => pS R F n (ev Y j) x) =
      (fun (x : H R (sch.obj (∐ fun k => Spec (Y k))) F n) (j : ι) =>
        pull R (sch.map (Sigma.ι (fun k => Spec (Y k)) j)) F n x) ∘ pull R (sch.map (sigmaSpec Y)) F n := by
    funext x j
    simp only [Function.comp_apply, pS, ev]
    rw [← pull_comp, ← Functor.map_comp, ι_sigmaSpec]
  rw [h]
  exact (hC R F (fun k => Spec (Y k)) n).comp (pull_iso_bij R F n _)

theorem pushout_pi {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') {ι : Type} [Fintype ι] (D₁ : ι → CommRingCat.{0})
    (e : ∀ k, D ⟶ D₁ k) (Y₁ : ι → CommRingCat.{0}) (u : ∀ k, Y' ⟶ Y₁ k) (φ₁ : ∀ k, D₁ k ⟶ Y₁ k)
    (hpo : ∀ k, IsPushout φ' (e k) (u k) (φ₁ k)) :
    IsPushout φ' (piMap D₁ e) (CommRingCat.ofHom (Pi.ringHom fun k => (u k).hom))
      (CommRingCat.ofHom (Pi.ringHom fun k => (φ₁ k).hom.comp (Pi.evalRingHom (fun k => D₁ k) k))) := by
  classical
  letI : Algebra D Y' := φ'.hom.toAlgebra
  letI : ∀ k, Algebra D (D₁ k) := fun k => (e k).hom.toAlgebra
  have hT : IsPushout φ' (piMap D₁ e) _ _ := CommRingCat.isPushout_tensorProduct D Y' (∀ k, D₁ k)
  have hTk : ∀ k, IsPushout φ' (e k) _ _ := fun k => CommRingCat.isPushout_tensorProduct D Y' (D₁ k)
  let isk : ∀ k, CommRingCat.of (Y' ⊗[D] D₁ k) ≅ Y₁ k := fun k => IsPushout.isoIsPushout _ _ (hTk k) (hpo k)
  have hl : ∀ k (y : Y'), (isk k).hom (y ⊗ₜ 1) = u k y := fun k y => by
    have := IsPushout.inl_isoIsPushout_hom _ _ (hTk k) (hpo k)
    exact congrArg (fun f => f.hom y) this
  have hr : ∀ k (d : D₁ k), (isk k).hom (1 ⊗ₜ d) = φ₁ k d := fun k d => by
    have := IsPushout.inr_isoIsPushout_hom _ _ (hTk k) (hpo k)
    exact congrArg (fun f => f.hom d) this
  let e₄ : CommRingCat.of (Y' ⊗[D] (∀ k, D₁ k)) ≅ CommRingCat.of (∀ k, Y₁ k) :=
    ((Algebra.TensorProduct.piRight D D Y' (fun k => D₁ k)).toRingEquiv.trans
      (RingEquiv.piCongrRight fun k => (isk k).commRingCatIsoToRingEquiv)).toCommRingCatIso
  refine hT.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e₄ (by simp) (by simp) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun y => funext fun k => ?_)
    have h4 : e₄.hom (y ⊗ₜ (1 : ∀ k, D₁ k)) k = (isk k).hom (y ⊗ₜ 1) := by
      simp [e₄, Algebra.TensorProduct.piRight_tmul]; rfl
    exact h4.trans (hl k y)
  · refine CommRingCat.hom_ext (RingHom.ext fun d => funext fun k => ?_)
    have h4 : e₄.hom ((1 : Y') ⊗ₜ d) k = (isk k).hom (1 ⊗ₜ d k) := by
      simp [e₄, Algebra.TensorProduct.piRight_tmul]; rfl
    exact h4.trans (hr k (d k))

theorem PushGlue_of (hC : Coprod) : LateralTheory.E.KillCokPf.Glue.PushGlue := by
  intro _ q _ i D Y' φ' m y ι _ D₁ e _ hk
  classical
  choose Y₁ u φ₁ hpo hz using hk
  choose z hz using hz
  obtain ⟨z₀, hz₀⟩ := (pi_bij hC (ZMod q) (tw q i) m D₁).2 z
  have hz₀' : ∀ j, pS _ (tw q i) m (ev D₁ j) z₀ = z j := fun j => congrFun hz₀ j
  let u'' : Y' ⟶ CommRingCat.of (∀ k, Y₁ k) := CommRingCat.ofHom (Pi.ringHom fun k => (u k).hom)
  let φ'' : CommRingCat.of (∀ k, D₁ k) ⟶ CommRingCat.of (∀ k, Y₁ k) :=
    CommRingCat.ofHom (Pi.ringHom fun k => (φ₁ k).hom.comp (Pi.evalRingHom (fun k => D₁ k) k))
  refine ⟨CommRingCat.of (∀ k, Y₁ k), u'', φ'', ?_, z₀, ?_⟩
  · exact pushout_pi φ' D₁ e Y₁ u φ₁ hpo
  · apply (pi_bij hC (ZMod q) (tw q i) m Y₁).1
    funext j
    have e1 : φ'' ≫ ev Y₁ j = ev D₁ j ≫ φ₁ j := rfl
    have e2 : u'' ≫ ev Y₁ j = u j := rfl
    show pS _ (tw q i) m (ev Y₁ j) (pS _ (tw q i) m φ'' z₀) = pS _ (tw q i) m (ev Y₁ j) (pS _ (tw q i) m u'' y)
    rw [← pS_comp, ← pS_comp, e1, e2, pS_comp, hz₀']
    exact hz j

end LateralTheory.E.PushGluePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LiftPf
noncomputable section
open Polynomial LateralTheory.E.PartDiagCut

namespace LateralTheory.E.LiftPf

theorem orthF {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfo : ∀ l m, l ≠ m → ε l * ε m = 0) {e e' : A} (he : e ∈ P.1) (he' : e' ∈ P.1) {l m : Fin n}
    (hne : (e, l) ≠ (e', m)) : e * ε l * (e' * ε m) = 0 := by
  by_cases hee : e = e'
  · subst hee
    have hlm : l ≠ m := fun h => hne (by rw [h])
    calc e * ε l * (e * ε m) = e * e * (ε l * ε m) := by ring
      _ = 0 := by rw [hfo l m hlm, mul_zero]
  · calc e * ε l * (e' * ε m) = (e * e') * (ε l * ε m) := by ring
      _ = 0 := by rw [P.orth e he e' he' hee, zero_mul]

theorem refine_exists {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfi : ∀ l, IsIdempotentElem (ε l)) (hfo : ∀ l m, l ≠ m → ε l * ε m = 0)
    (hfs : ∑ l, ε l = 1) : ∃ Q : PartDiagCut.Part A, P ≤ Q ∧ ∀ g ∈ Q.1, ∃ l, g * ε l = g := by
  classical
  let F : A × Fin n → A := fun x => x.1 * ε x.2
  let T := (P.1 ×ˢ (Finset.univ : Finset (Fin n))).filter (fun x => F x ≠ 0)
  have memT : ∀ x ∈ T, x.1 ∈ P.1 ∧ F x ≠ 0 := by
    intro x hx
    simp only [T, Finset.mem_filter, Finset.mem_product] at hx
    exact ⟨hx.1.1, hx.2⟩
  have idF : ∀ x ∈ T, IsIdempotentElem (F x) := fun x hx => (P.idem x.1 (memT x hx).1).1.mul (hfi x.2)
  have oF : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → F x * F y = 0 := fun x hx y hy hxy =>
    orthF P ε hfo (memT x hx).1 (memT y hy).1 (by simpa using hxy)
  have inj : Set.InjOn F T := by
    intro x hx y hy hxy
    by_contra hne
    apply (memT x hx).2
    rw [← (idF x hx).eq]
    nth_rewrite 2 [hxy]
    exact oF x hx y hy hne
  refine ⟨⟨T.image F, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨idF x hx, (memT x hx).2⟩
  · intro g hg g' hg' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg'
    exact oF x hx y hy (fun h => hne (by rw [h]))
  · rw [Finset.sum_image inj, Finset.sum_filter_ne_zero, Finset.sum_product]
    simp only [F]
    simp_rw [← Finset.mul_sum, hfs, mul_one]
    exact P.sum_eq
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨x.1, (memT x hx).1, ?_⟩
    show x.1 * ε x.2 * x.1 = x.1 * ε x.2
    rw [mul_right_comm, (P.idem x.1 (memT x hx).1).1.eq]
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨x.2, by show x.1 * ε x.2 * ε x.2 = x.1 * ε x.2; rw [mul_assoc, (hfi x.2).eq]⟩

variable {B : Type} [CommRing B]

theorem natHom (I : Ideal B) {P Q : PartDiagCut.Part (B ⧸ I)} (h : P ≤ Q) :
    (stageMap I h).comp (βP I P) = βP I Q := by
  refine RingHom.ext fun x => funext fun g => ?_
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact IsLocalization.map_eq _ _

theorem isUnit_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (g : Q.1) (x : B) (hx : x ∈ S I g.1) :
    IsUnit (βP I Q x g) := by
  simpa [βP] using IsLocalization.map_units (Localization (S I g.1)) (⟨x, hx⟩ : S I g.1)

theorem mem_of_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I Q)
    (hz : ∀ g : Q.1, ∃ w ∈ I.map (βP I Q), ∃ c : Localization (S I g.1), z g = c * w g) :
    z ∈ I.map (βP I Q) := by
  classical
  rw [← Finset.univ_sum_single z]
  refine Ideal.sum_mem _ fun g _ => ?_
  obtain ⟨w, hw, c, hc⟩ := hz g
  have : (Pi.single g (z g) : PiLocalization₂ I Q) = (Pi.single g c : PiLocalization₂ I Q) * w := by
    funext g'
    by_cases hg : g' = g
    · subst hg; simp [hc]
    · simp [hg]
  rw [this]; exact Ideal.mul_mem_left _ _ hw

theorem Lift_of : LateralTheory.E.PartCPf.Lift := by
  classical
  intro B _ I P p a₀ n r f hp hfi hfo hfs hy
  obtain ⟨Q, h, hL⟩ := refine_exists P (fun l => Ideal.Quotient.mk I (f l)) hfi hfo hfs
  choose L hLg using fun g : Q.1 => hL g.1 g.2
  refine ⟨Q, h, fun g => stageMap I h (r (L g)) g, ?_, ?_⟩
  · rw [hp, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, IsRoot.def, eval_prod, eval_sub, eval_X, eval_C]
    funext g
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ (L g)) (by simp)
  · apply mem_of_comp
    intro g
    have hw : βP I Q (f (L g)) * stageMap I h (a₀ - r (L g)) ∈ I.map (βP I Q) := by
      have := Ideal.mem_map_of_mem (stageMap I h) (hy (L g))
      rw [Ideal.map_map, natHom, map_mul, ← RingHom.comp_apply, natHom] at this
      exact this
    have hmem : f (L g) ∈ S I g.1 := ⟨1, by rw [mul_one, mul_comm]; exact hLg g⟩
    obtain ⟨u, hu⟩ := isUnit_comp I Q g (f (L g)) hmem
    refine ⟨_, hw, -(↑u⁻¹ : Localization (S I g.1)), ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply, map_sub]
    rw [← hu]
    linear_combination (stageMap I h a₀ g - stageMap I h (r (L g)) g) * u.inv_mul

end LateralTheory.E.LiftPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AicOfIsLocalization
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial Opposite

namespace LateralTheory.E.LocPf

theorem root_mem_range {A K : Type} [CommRing A] [CommRing K] [IsDomain K] (hA : GlobalTheory.EtC.AIC A) (φ : A →+* K) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → ∀ a : K, p.eval₂ φ a = 0 → ∃ b, φ b = a := by
  intro n
  induction n with
  | zero =>
    intro p hn hp a ha
    rw [eq_one_of_monic_natDegree_zero hp hn, eval₂_one] at ha
    exact absurd ha one_ne_zero
  | succ n ih =>
    intro p hn hp a ha
    have : Nontrivial A := by
      by_contra hnt; rw [not_nontrivial_iff_subsingleton] at hnt
      rw [Subsingleton.elim p 0] at hn; simp at hn
    obtain ⟨b, hb⟩ := hA p hp (by omega)
    have e := (mul_divByMonic_eq_iff_isRoot (p := p) (a := b)).mpr hb
    have hq : (p /ₘ (X - C b)).Monic := Monic.of_mul_monic_left (monic_X_sub_C b) (by rw [e]; exact hp)
    have hdeg : (p /ₘ (X - C b)).natDegree = n := by
      have := (monic_X_sub_C b).natDegree_mul hq
      rw [e, natDegree_X_sub_C] at this; omega
    rw [← e, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact ⟨b, (sub_eq_zero.mp h).symm⟩
    · exact ih _ hdeg hq a h

theorem aic_of_isLocalization {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (hA : GlobalTheory.EtC.AIC A) : GlobalTheory.EtC.AIC B := by
  intro p hp hd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M (fun i : Fin (p.natDegree + 1) => p.coeff i)
  set t := algebraMap A B b with ht
  have hlift : p.scaleRoots t ∈ lifts (algebraMap A B) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with h | h | h
    · obtain ⟨c, hc⟩ := hb ⟨i, by omega⟩
      refine ⟨c * (b : A) ^ (p.natDegree - i - 1), ?_⟩
      rw [map_mul, map_pow, hc, Algebra.smul_def, ← ht]
      rw [show t ^ (p.natDegree - i) = t * t ^ (p.natDegree - i - 1) by rw [← pow_succ']; congr 1; omega]
      ring
    · subst h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩
  obtain ⟨q, hqm, hqd, hq⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).mpr hp)
  obtain ⟨c, hc⟩ := hA q hq (by rw [hqd, natDegree_scaleRoots]; exact hd)
  obtain ⟨u, hu⟩ := (IsLocalization.map_units B b).exists_right_inv
  refine ⟨u * algebraMap A B c, ?_⟩
  have h1 : p = (p.scaleRoots t).scaleRoots u := by
    rw [← scaleRoots_mul, ht, hu, scaleRoots_one]
  have h2 : (p.scaleRoots t).eval (algebraMap A B c) = 0 := by
    rw [← hqm, Polynomial.eval_map, eval₂_at_apply, hc, map_zero]
  conv_lhs => rw [h1]
  rw [scaleRoots_eval_mul, h2, mul_zero]

theorem germ_comp (Z : Scheme.{0}) {W U : Z.Opens} (i : W ≤ U) (x : Z) (hx : x ∈ W) :
    (Z.presheaf.germ W x hx).hom.comp (Z.presheaf.map (homOfLE i).op).hom = (Z.presheaf.germ U x (i hx)).hom := by
  ext s; simp

theorem exists_small (Z : Scheme.{0}) (h : ∀ z : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U ∧ GlobalTheory.EtC.AIC Γ(Z, U))
    (U : Z.Opens) (z : Z) (hz : z ∈ U) : ∃ W : Z.Opens, W ≤ U ∧ z ∈ W ∧ GlobalTheory.EtC.AIC Γ(Z, W) := by
  obtain ⟨V, hV, hzV, hA⟩ := h z
  obtain ⟨f, hle, hzf⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hz⟩ hzV
  have := hV.isLocalization_basicOpen f
  exact ⟨Z.basicOpen f, hle, hzf, aic_of_isLocalization (Submonoid.powers f) hA⟩

theorem loc : LateralTheory.E.NormACPf.Loc := by
  intro Z hZ h U hU ⟨z0, hz0⟩ p hp hd
  set η := genericPoint Z
  have hη : ∀ W : Z.Opens, (W : Set Z).Nonempty → η ∈ W := fun W hW =>
    ((genericPoint_spec Z).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  have hηU : η ∈ U := hη U ⟨z0, hz0⟩
  choose W hWU hzW hWA using fun z : U => exists_small Z h U z.1 z.2
  have hηW : ∀ z : U, η ∈ W z := fun z => hη _ ⟨z.1, hzW z⟩
  let gU := (Z.presheaf.germ U η hηU).hom
  let res := fun z : U => (Z.presheaf.map (homOfLE (hWU z)).op).hom
  have hdom : ∀ z : U, Nontrivial Γ(Z, W z) := fun z => by
    have : Nonempty (W z) := ⟨⟨z.1, hzW z⟩⟩; infer_instance
  let z0' : U := ⟨z0, hz0⟩
  obtain ⟨b0, hb0⟩ := hWA z0' (p.map (res z0')) (hp.map _) (by rw [hp.natDegree_map]; exact hd)
  set a := Z.presheaf.germ (W z0') η (hηW z0') b0 with ha_def
  have hroot : p.eval₂ gU a = 0 := by
    have := congrArg (Z.presheaf.germ (W z0') η (hηW z0')).hom hb0
    rw [Polynomial.eval_map, hom_eval₂, germ_comp, map_zero] at this
    exact this
  have hc : ∀ z : U, ∃ c, Z.presheaf.germ (W z) η (hηW z) c = a := by
    intro z
    refine root_mem_range (hWA z) (Z.presheaf.germ (W z) η (hηW z)).hom _ (p.map (res z)) rfl (hp.map _) a ?_
    rw [eval₂_map, germ_comp]; exact hroot
  choose c hcz using hc
  obtain ⟨s1, hs1, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf W U (fun z => homOfLE (hWU z))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hzW _⟩) c (by
      intro i j
      apply germ_injective_of_isIntegral Z (U := W i ⊓ W j) η (show η ∈ W i ⊓ W j from ⟨hηW i, hηW j⟩)
      change (Z.presheaf.germ _ η _) (Z.presheaf.map _ (c i)) = (Z.presheaf.germ _ η _) (Z.presheaf.map _ (c j))
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hcz, hcz])
  obtain ⟨s, hs⟩ : ∃ s : Γ(Z, U), ∀ i, Z.presheaf.map (homOfLE (hWU i)).op s = c i := ⟨s1, hs1⟩
  have hsa : gU s = a := by
    have := hs z0'
    rw [← hcz z0', ← this]
    change _ = (Z.presheaf.germ _ η _) (Z.presheaf.map _ s)
    rw [TopCat.Presheaf.germ_res_apply]
  refine ⟨s, germ_injective_of_isIntegral Z η hηU ?_⟩
  change gU (p.eval s) = gU 0
  rw [map_zero, ← eval₂_at_apply, hsa, hroot]

end LateralTheory.E.LocPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SpecAICPf
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.SpecAICPf

theorem aic_equiv {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A') (h : AIC A) : AIC A' := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _) (by rwa [natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have := congrArg e ha
  rw [eval_map, ← coe_eval₂RingHom, map_zero] at this
  rw [← this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [eval₂_eq_sum_range, eval_eq_sum_range, map_sum]

theorem card_roots_of_aic {A : Type} [CommRing A] [IsDomain A] (h : AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.Monic → p.natDegree = n → Multiset.card p.roots = n := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    rw [eq_one_of_monic_natDegree_zero hp hn]; simp
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    have e := mul_divByMonic_eq_iff_isRoot.2 ha
    have hq : (p /ₘ (X - C a)).Monic := Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [e]; exact hp)
    rw [← e, roots_mul (by rw [e]; exact hp.ne_zero), roots_X_sub_C, Multiset.card_add, ih _ hq hdeg]
    simp; omega

theorem aic_localization {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
    [IsLocalization M S] (h : AIC B) : AIC S := by
  classical
  intro p hp hd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M (Finset.image p.coeff (Finset.range (p.natDegree + 1)))
  set r : S := algebraMap B S b
  have hl : p.scaleRoots r ∈ lifts (algebraMap B S) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · obtain ⟨t, ht⟩ := hb (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      refine ⟨t * b ^ (p.natDegree - (i + 1)), ?_⟩
      rw [map_mul, ht, map_pow, Algebra.smul_def]
      simp only [r]
      have : p.natDegree - i = (p.natDegree - (i + 1)) + 1 := by omega
      rw [this, pow_succ]; ring
    · subst hi; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt hi]; exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff r).2 hp)
  obtain ⟨β, hβ⟩ := h q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  have hru : IsUnit r := IsLocalization.map_units S b
  refine ⟨algebraMap B S β * hru.unit⁻¹, ?_⟩
  have h1 := scaleRoots_eval₂_mul (p := p) (RingHom.id S) (algebraMap B S β * hru.unit⁻¹) r
  simp only [eval₂_id, RingHom.id_apply] at h1
  have h2 : r * (algebraMap B S β * hru.unit⁻¹) = algebraMap B S β := by
    rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]
  rw [h2, ← hq, eval_map, eval₂_hom, hβ, map_zero] at h1
  exact (hru.pow _).mul_right_eq_zero.1 h1.symm

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

theorem roots_eq {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] (hK : Function.Injective (algebraMap R K)) (L : Subalgebra R K) (hL : AIC L)
    (p : R[X]) (hp : p.Monic) : (p.map (algebraMap R L)).roots.map L.val.toRingHom = (p.map (algebraMap R K)).roots ∧
      Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
  have hinj : Function.Injective (algebraMap R L) := by
    intro a b hab
    exact hK (congrArg Subtype.val hab)
  have hc : Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
    rw [card_roots_of_aic hL _ _ (hp.map _) rfl, natDegree_map_eq_of_injective hinj]
  refine ⟨?_, hc⟩
  rw [roots_map_of_injective_of_card_eq_natDegree (f := L.val.toRingHom) Subtype.val_injective
    (by rw [hc, natDegree_map_eq_of_injective hinj]), map_map]
  rfl

theorem aic_of_local {R : Type} [CommRing R] [IsDomain R]
    (h : ∀ v : MaximalSpectrum R, AIC (Localization.AtPrime v.asIdeal)) : AIC R := by
  classical
  intro p hp hd
  let K := FractionRing R
  let L : MaximalSpectrum R → Subalgebra R K := fun v =>
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  have hL : ∀ v, AIC (L v) := fun v =>
    aic_equiv (IsLocalization.algEquiv v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal) (L v)).toRingEquiv (h v)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨e0, c0⟩ := roots_eq (IsFractionRing.injective R K) (L ⟨m, hm⟩) (hL _) p hp
  obtain ⟨x, hx⟩ : ∃ x, x ∈ (p.map (algebraMap R K)).roots := by
    rw [← e0]
    apply Multiset.exists_mem_of_ne_zero
    intro h0
    rw [Multiset.map_eq_zero] at h0
    rw [h0] at c0; simp at c0; omega
  have hmem : x ∈ (⊥ : Subalgebra R K) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot R K, Algebra.mem_iInf]
    intro v
    rw [← (roots_eq (IsFractionRing.injective R K) (L v) (hL v) p hp).1] at hx
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
    exact y.2
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.1 hmem
  refine ⟨a, ?_⟩
  have hr := (mem_roots (hp.map _).ne_zero).1 hx
  rw [IsRoot, eval_map, eval₂_hom] at hr
  exact (IsFractionRing.injective R K) (by rw [hr, map_zero])

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

open CategoryTheory AlgebraicGeometry

theorem stalk_aic (B : CommRingCat.{0}) (hA : AIC B) (x : Spec B) : AIC ((Spec B).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra B ((Spec B).presheaf.stalk x) := StructureSheaf.stalkAlgebra B x
  have : IsLocalization.AtPrime ((Spec B).presheaf.stalk x) x.asIdeal := StructureSheaf.IsLocalization.to_stalk B x
  exact aic_localization x.asIdeal.primeCompl hA

theorem SpecAIC_of : LateralTheory.E.FibreEqvPf.SpecAIC := by
  intro B hB hA
  refine ⟨inferInstance, ?_⟩
  intro U hU hne
  haveI : Nonempty U := hne.to_subtype
  apply aic_of_local
  intro v
  let y : PrimeSpectrum Γ(Spec B, U) := ⟨v.asIdeal, v.isMaximal.isPrime⟩
  have hy : hU.fromSpec y ∈ U := by
    show hU.fromSpec y ∈ (U : Set (Spec B))
    rw [← hU.range_fromSpec]; exact ⟨y, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk (Spec B).presheaf ⟨hU.fromSpec y, hy⟩
  have hloc : IsLocalization.AtPrime ((Spec B).presheaf.stalk (hU.fromSpec y)) y.asIdeal := hU.isLocalization_stalk' y hy
  have hst := stalk_aic B hA (hU.fromSpec y)
  exact aic_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl ((Spec B).presheaf.stalk (hU.fromSpec y))
    (Localization.AtPrime v.asIdeal)).toRingEquiv hst

end LateralTheory.E.SpecAICPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChaseBPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf LateralTheory.E.StepKPf
  LateralTheory.E.StepKPf.ChasePf

namespace LateralTheory.E.ChaseBPf

attribute [reassoc] rL_ι rD_ι

theorem pc {R : Type} [CommRing R] {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (F : Shv R) (n : ℤ)
    (x : H R (sch.obj C) F n) :
    pull R (sch.map (a ≫ b)) F n x = pull R (sch.map a) F n (pull R (sch.map b) F n x) := by
  rw [Functor.map_comp, pull_comp]

theorem pbInf {Y : Scheme.{0}} (A B C : Y.Opens) (hA : C ≤ A) (hB : C ≤ B) (hC : C = A ⊓ B) :
    IsPullback (Y.homOfLE hA) (Y.homOfLE hB) A.ι B.ι := by
  subst hC; exact isPullback_opens_inf A B

theorem cover {Y : Scheme.{0}} (A B : Y.Opens) (h : A ⊔ B = ⊤) :
    Set.range A.ι ∪ Set.range B.ι = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, ← TopologicalSpace.Opens.coe_sup, h,
    TopologicalSpace.Opens.coe_top]

variable {J : Type} [SmallCategory J]

theorem lv_inf (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J}
    (f : k ⟶ j0) : lv D e (U ⊓ V) f = lv D e U f ⊓ lv D e V f := Scheme.Hom.preimage_inf _

theorem lm_inf {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) :
    lm c e (U ⊓ V) = lm c e U ⊓ lm c e V := Scheme.Hom.preimage_inf _

theorem lv_sup (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) (h : U ⊔ V = ⊤)
    {k : J} (f : k ⟶ j0) : lv D e U f ⊔ lv D e V f = ⊤ := by
  rw [lv, lv, ← Scheme.Hom.preimage_sup, h, Scheme.Hom.preimage_top]

theorem lm_sup {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens)
    (h : U ⊔ V = ⊤) : lm c e U ⊔ lm c e V = ⊤ := by
  rw [lm, lm, ← Scheme.Hom.preimage_sup, h, Scheme.Hom.preimage_top]

def kv (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J} (f : k ⟶ j0) :
    (lv D e (U ⊓ V) f).toScheme ≅ pullback (lv D e U f).ι (lv D e V f).ι :=
  (pbInf _ _ _ ((lv_inf D e U V f).le.trans inf_le_left) ((lv_inf D e U V f).le.trans inf_le_right)
    (lv_inf D e U V f)).isoPullback

def km {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) :
    (lm c e (U ⊓ V)).toScheme ≅ pullback (lm c e U).ι (lm c e V).ι :=
  (pbInf _ _ _ ((lm_inf c e U V).le.trans inf_le_left) ((lm_inf c e U V).le.trans inf_le_right)
    (lm_inf c e U V)).isoPullback

def pm (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k l : J} (f : k ⟶ j0)
    (g : l ⟶ k) : pullback (lv D e U (g ≫ f)).ι (lv D e V (g ≫ f)).ι ⟶ pullback (lv D e U f).ι (lv D e V f).ι :=
  pullback.map _ _ _ _ (rD D e U f g) (rD D e V f g) (D.map g) (rD_ι D e U f g).symm (rD_ι D e V f g).symm

def pL {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J}
    (f : k ⟶ j0) : pullback (lm c e U).ι (lm c e V).ι ⟶ pullback (lv D e U f).ι (lv D e V f).ι :=
  pullback.map _ _ _ _ (rL c e U f) (rL c e V f) (c.π.app k) (rL_ι c e U f).symm (rL_ι c e V f).symm

@[reassoc]
theorem rL_rD {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : rL c e U (g ≫ f) ≫ rD D e U f g = rL c e U f := by
  rw [← cancel_mono (lv D e U f).ι, Category.assoc, rD_ι, rL_ι_assoc, c.w, rL_ι]

theorem pL_pm {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens)
    {k l : J} (f : k ⟶ j0) (g : l ⟶ k) : pL c e U V (g ≫ f) ≫ pm D e U V f g = pL c e U V f := by
  apply pullback.hom_ext <;> simp only [pL, pm, pullback.map] <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]

theorem km_pL {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens)
    {k : J} (f : k ⟶ j0) : (km c e U V).hom ≫ pL c e U V f = rL c e (U ⊓ V) f ≫ (kv D e U V f).hom := by
  apply pullback.hom_ext
  · rw [← cancel_mono (lv D e U f).ι]
    simp only [pL, km, kv, pullback.map, Category.assoc]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]
  · rw [← cancel_mono (lv D e V f).ι]
    simp only [pL, km, kv, pullback.map, Category.assoc]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]

theorem kv_pm (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : (kv D e U V (g ≫ f)).hom ≫ pm D e U V f g = rD D e (U ⊓ V) f g ≫ (kv D e U V f).hom := by
  apply pullback.hom_ext
  · rw [← cancel_mono (lv D e U f).ι]
    simp only [pm, kv, pullback.map, Category.assoc]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]
  · rw [← cancel_mono (lv D e V f).ι]
    simp only [pm, kv, pullback.map, Category.assoc]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd_assoc, rL_ι, rL_ι_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, rD_ι, rD_ι_assoc, rL_rD, rL_rD_assoc]

theorem pL_fst {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J}
    (f : k ⟶ j0) : pL c e U V f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ rL c e U f := pullback.lift_fst _ _ _

theorem pL_snd {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U V : X.Opens) {k : J}
    (f : k ⟶ j0) : pL c e U V f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ rL c e V f := pullback.lift_snd _ _ _

theorem liftR {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {q : ℕ}
    {n i : ℤ} {k1 l : J} (f1 : k1 ⟶ j0) (a1 : Ht q (sch.obj (lv D e U f1).toScheme) n i) (g1 : l ⟶ k1) (φ : l ⟶ j0)
    (h : g1 ≫ f1 = φ) : ∃ a' : Ht q (sch.obj (lv D e U φ).toScheme) n i,
      pull _ (sch.map (rL c e U φ)) _ _ a' = pull _ (sch.map (rL c e U f1)) _ _ a1 := by
  subst h
  exact ⟨pull _ (sch.map (rD D e U f1 g1)) _ _ a1, by rw [← pc, rL_rD]⟩

theorem cone3 [IsCofiltered J] {j0 k k1 k2 : J} (f : k ⟶ j0) (f1 : k1 ⟶ j0) (f2 : k2 ⟶ j0) :
    ∃ (l : J) (g : l ⟶ k) (g1 : l ⟶ k1) (g2 : l ⟶ k2), g1 ≫ f1 = g ≫ f ∧ g2 ≫ f2 = g ≫ f := by
  obtain ⟨l1, g, g1, h1⟩ := IsCofiltered.cospan f f1
  obtain ⟨l, h, g2, h2⟩ := IsCofiltered.cospan (g ≫ f) f2
  exact ⟨l, h ≫ g, h ≫ g1, g2, by rw [Category.assoc, Category.assoc, h1], by rw [Category.assoc, h2]⟩

theorem ChaseB_of : ChaseB := by
  intro h hmv q J _ _ D c hc j0 X e U V hUV rU rV rW n i k f y hy hyU hyV
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  obtain ⟨δ, hex, hnat⟩ := hmv h (ZMod q) (tw q i)
  have cv : ∀ {l : J} (φ : l ⟶ j0), Set.range (lv D e U φ).ι ∪ Set.range (lv D e V φ).ι = Set.univ :=
    fun φ => cover _ _ (lv_sup D e U V hUV φ)
  have cL : Set.range (lm c e U).ι ∪ Set.range (lm c e V).ι = Set.univ := cover _ _ (lm_sup c e U V hUV)
  have hpm : ∀ {k l : J} (f : k ⟶ j0) (g : l ⟶ k) w, δ _ _ m (pull _ (sch.map (pm D e U V f g)) _ _ w) =
      pull _ (sch.map (D.map g)) _ _ (δ _ _ m w) := fun f g w =>
    hnat _ _ _ _ (cv _) (cv f) _ _ _ (rD_ι D e U f g).symm (rD_ι D e V f g).symm m w
  obtain ⟨w, hw⟩ := ((hex _ _ (cv f) m).2.2 y).1 ⟨hyU, hyV⟩
  have hinf : δ (lm c e U).ι (lm c e V).ι m (pull _ (sch.map (pL c e U V f)) _ _ w) = 0 :=
    (hnat _ _ _ _ cL (cv f) _ _ _ (rL_ι c e U f).symm (rL_ι c e V f).symm m w).trans (by rw [hw]; exact hy)
  obtain ⟨a, b, hab⟩ := ((hex _ _ cL m).2.1 _).1 hinf
  obtain ⟨k1, f1, a1, ha1⟩ := (rU m i).1 a
  obtain ⟨k2, f2, b1, hb1⟩ := (rV m i).1 b
  obtain ⟨l, g, g1, g2, h1, h2⟩ := cone3 f f1 f2
  obtain ⟨a', ha'⟩ := liftR c e U f1 a1 g1 (g ≫ f) h1
  obtain ⟨b', hb'⟩ := liftR c e V f2 b1 g2 (g ≫ f) h2
  set z := pull _ (sch.map (pm D e U V f g)) _ _ w - (pull _ (sch.map (pullback.fst _ _)) _ _ a' -
    pull _ (sch.map (pullback.snd _ _)) _ _ b') with hz_def
  have hz : pull _ (sch.map (pL c e U V (g ≫ f))) _ _ z = 0 := by
    rw [hz_def, map_sub, map_sub, ← pc, pL_pm, ← pc, ← pc, pL_fst, pL_snd, pc, pc, ha', hb', ha1, hb1, hab, sub_self]
  have hδz : δ _ _ m z = pull _ (sch.map (D.map g)) _ _ y := by
    rw [hz_def, map_sub, ((hex _ _ (cv (g ≫ f)) m).2.1 _).2 ⟨a', b', rfl⟩, sub_zero, hpm, hw]
  have hz' : pull _ (sch.map (rL c e (U ⊓ V) (g ≫ f))) _ _ (pull _ (sch.map (kv D e U V (g ≫ f)).hom) _ _ z) = 0 := by
    rw [← pc, ← km_pL, pc, hz, map_zero]
  obtain ⟨l2, g', hg'⟩ := (rW m i).2 l (g ≫ f) _ hz'
  have hzz : pull _ (sch.map (pm D e U V (g ≫ f) g')) _ _ z = 0 := by
    have e0 : pm D e U V (g ≫ f) g' =
        (kv D e U V (g' ≫ g ≫ f)).inv ≫ rD D e (U ⊓ V) (g ≫ f) g' ≫ (kv D e U V (g ≫ f)).hom := by
      rw [← kv_pm, Iso.inv_hom_id_assoc]
    rw [e0, pc, pc, hg', map_zero]
  refine ⟨l2, g' ≫ g, ?_⟩
  have e1 := hpm (g ≫ f) g' z
  rw [hzz, map_zero, hδz, ← pc] at e1
  rw [D.map_comp]
  exact e1.symm

end LateralTheory.E.ChaseBPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.RelEqvInjPf
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.RelEqvInjPf

set_option linter.unusedSectionVars false
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

abbrev pl {K L : CochainComplex C ℤ} (f : K ⟶ L) (M : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass L M n →+ CohomologyClass K M n := cpre (Cocycle.ofHom f) M n n (zero_add n)

lemma inr_map {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) : mappingCone.inr φ' ≫ mappingCone.map φ' φ α β comm = β ≫ mappingCone.inr φ := by
  simp [mappingCone.map]

lemma map_fst {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) :
    (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp (mappingCone.fst φ).1 (zero_add 1) =
      (mappingCone.fst φ').1.comp (Cochain.ofHom α) (add_zero 1) := by
  rw [mappingCone.ext_cochain_from_iff _ 0 1 (zero_add 1)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_zero 1) (by omega)]
    simp [mappingCone.map]
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain]
    simp

lemma laurent_adjoin_eq_of_image_eq {A' A I : CochainComplex C ℤ} (α : A' ⟶ A) {j k : ℤ} (hjk : j + 1 = k)
    (hα : Function.Injective (pl α I k)) (z : Cocycle A I k) (ξ : Cochain A' I j)
    (h : δ j k ξ = (Cochain.ofHom α).comp z.1 (zero_add k)) : ∃ t : Cochain A I j, δ j k t = z.1 := by
  have h0 : pl α I k (CohomologyClass.mk z) = 0 := by
    change CohomologyClass.mk (zcomp (Cocycle.ofHom α) z (zero_add k)) = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨j, hjk, ξ, h⟩
  have h1 : CohomologyClass.mk z = 0 := hα (h0.trans (map_zero _).symm)
  rw [CohomologyClass.mk_eq_zero_iff] at h1
  obtain ⟨j', hj', t, ht⟩ := h1
  obtain rfl : j' = j := by omega
  exact ⟨t, ht⟩

lemma exists_finset_adjoin_laurent_preimage {B' B I : CochainComplex C ℤ} (β : B' ⟶ B) {j k : ℤ} (hjk : j + 1 = k)
    (hβ : Function.Surjective (pl β I k)) (z : Cocycle B' I k) :
    ∃ (w : Cocycle B I k) (r : Cochain B' I j), δ j k r = z.1 - (Cochain.ofHom β).comp w.1 (zero_add k) := by
  obtain ⟨W, hW⟩ := hβ (CohomologyClass.mk z)
  obtain ⟨w, rfl⟩ := W.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom β) w (zero_add k)) = _ at hW
  have h2 := hW.symm
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at h2
  obtain ⟨j', hj', r, hr⟩ := h2
  obtain rfl : j' = j := by omega
  exact ⟨w, r, by rw [hr]; rfl⟩

theorem main {A B A' B' I : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) (l m n : ℤ) (hl : l + 1 = m) (hm : m + 1 = n)
    (hαi : Function.Injective (pl α I m)) (hβi : Function.Injective (pl β I n))
    (hβs : Function.Surjective (pl β I m)) :
    Function.Injective (pl (mappingCone.map φ' φ α β comm) I n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp _ c _) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m', hm', ξ0, hξ0⟩ := hy
  have em : m' = m := by omega
  subst m'
  change δ m n ξ0 = (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp c.1 (zero_add n) at hξ0
  set a := (mappingCone.inl φ).comp c.1 (show -1 + n = m by omega) with ha
  set b := (Cochain.ofHom (mappingCone.inr φ)).comp c.1 (zero_add n) with hb
  have hdec : c.1 = mappingCone.descCochain φ a b hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm]; simp [ha, hb]
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hδa : δ m n a = n.negOnePow • (Cochain.ofHom φ).comp b (zero_add n) := by
    have h := congrArg (fun z => (mappingCone.inl φ).comp z (show -1 + (n + 1) = n by omega)) hc
    simp only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero,
      add_zero] at h
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg, sub_eq_zero] at h
    exact h
  have hδb : δ n (n + 1) b = 0 := by
    have h := congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add (n + 1))) hc
    simpa using h

  have h1 : δ m n ((Cochain.ofHom (mappingCone.inr φ')).comp ξ0 (zero_add m)) =
      (Cochain.ofHom β).comp (Cocycle.mk b (n + 1) rfl hδb).1 (zero_add n) := by
    rw [δ_ofHom_comp, hξ0, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map,
      Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    rfl
  obtain ⟨η, hη⟩ := laurent_adjoin_eq_of_image_eq β hm hβi _ _ h1
  change δ m n η = b at hη

  set s := n.negOnePow with hs
  set γ := a - s • (Cochain.ofHom φ).comp η (zero_add m) with hγ
  have hδγ : δ m n γ = 0 := by
    rw [hγ, δ_sub, δ_units_smul, δ_ofHom_comp, hη, hδa, sub_self]
  set D0 := mappingCone.descCochain φ (0 : Cochain A I l) η hl with hD0
  have hcγ : c.1 = δ m n D0 + (mappingCone.fst φ).1.comp γ (by omega) := by
    rw [hdec, hD0, mappingCone.δ_descCochain _ _ _ _ _ hm, hη, hγ]
    simp only [mappingCone.descCochain, δ_zero, zero_add, Cochain.comp_sub]
    abel

  set ξ := ξ0 - (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp D0 (zero_add m) with hξ
  have h3 : δ m n ξ = (mappingCone.fst φ').1.comp ((Cochain.ofHom α).comp γ (zero_add m)) (by omega) := by
    rw [hξ, δ_sub, δ_ofHom_comp, hξ0, hcγ, Cochain.comp_add, add_sub_cancel_left,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, map_fst, Cochain.comp_assoc_of_second_is_zero_cochain]
  set p := (mappingCone.inl φ').comp ξ (show -1 + m = l by omega) with hp
  set q := (Cochain.ofHom (mappingCone.inr φ')).comp ξ (zero_add m) with hq
  have hdecξ : ξ = mappingCone.descCochain φ' p q hl := by
    rw [mappingCone.ext_cochain_from_iff _ l m hl]; simp [hp, hq]
  rw [hdecξ, mappingCone.δ_descCochain _ _ _ _ _ hm] at h3
  have h3a : δ l m p + s • (Cochain.ofHom φ').comp q (zero_add m) = (Cochain.ofHom α).comp γ (zero_add m) := by
    have h := congrArg (fun z => (mappingCone.inl φ').comp z (show -1 + n = m by omega)) h3
    simpa only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero,
      add_zero] using h
  have h3b : δ m n q = 0 := by
    have h := congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ')).comp z (zero_add n)) h3
    simpa using h

  obtain ⟨w, r, hr⟩ := exists_finset_adjoin_laurent_preimage β hl hβs (Cocycle.mk q n hm h3b)
  change δ l m r = q - (Cochain.ofHom β).comp w.1 (zero_add m) at hr
  have hw : δ m n w.1 = 0 := Cocycle.δ_eq_zero w n
  have h4 : δ l m (p + s • (Cochain.ofHom φ').comp r (zero_add l)) =
      (Cochain.ofHom α).comp (Cocycle.mk (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) n hm
        (by rw [δ_sub, δ_units_smul, δ_ofHom_comp, hδγ, hw]; simp)).1 (zero_add m) := by
    change _ = (Cochain.ofHom α).comp (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) (zero_add m)
    rw [δ_add, δ_units_smul, δ_ofHom_comp, hr, Cochain.comp_sub, Cochain.comp_sub, ← h3a,
      Cochain.comp_units_smul]
    simp only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
    rw [comm, smul_sub]
    abel
  obtain ⟨t, ht⟩ := laurent_adjoin_eq_of_image_eq α hl hαi _ _ h4
  change δ l m t = γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m) at ht

  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, D0 + mappingCone.descCochain φ t w.1 hl, ?_⟩
  rw [δ_add, mappingCone.δ_descCochain φ t w.1 hl n hm, ht, hw, hcγ]
  simp
  rw [← hs, sub_add_cancel]

theorem RelEqvInj_of : LateralTheory.E.RelDescPf.RelEqvInj := by
  intro R _ F U E U' E' f f' u e comm hu he n
  exact main ((chains R).map f) ((chains R).map f') ((chains R).map u) ((chains R).map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) (n - 1 - 1) (n - 1) n (by omega) (by omega)
    (hu (n - 1)).1 (he n).1 (he (n - 1)).2

end LateralTheory.E.RelEqvInjPf
end
end

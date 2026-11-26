module

public import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.CokernelKilling
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf

namespace LateralTheory.E.KillCokPf

def Pointwise : Prop := B1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D) (O : CommRingCat.{0}) (o : D ⟶ O), IE o → BC q i φ (d ≫ o) →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (m : ℤ) (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) (Q : Ideal O), Q.IsPrime →
  ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = Q.comap o.hom ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)

def Assemble : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m),
  (∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = r ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e ∧ SpS e ∧ IsPushout φ' e u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem KillCok_of (hC : Coprod) (hP : Pointwise) (hA : Assemble) : LateralTheory.E.DescLocPf.Fine.KillCok := by
  intro hH q _ i n A Y φ hq P _ het _ D d hD hpts Y' w φ' hpo m _ y
  have hB1 : B1 := hH.2.2.2.2.2.2.1
  have hloc : ∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧
      Q₁.comap e.hom = r ∧ ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m) := by
    intro r hr
    obtain ⟨O, o, Q, hIE, hQ, hQr, hBC⟩ := hpts r hr
    obtain ⟨D₁, e, Q₁, he, hQ₁, hc, rest⟩ := hP hB1 q i φ hq D d O o hIE hBC Y' w φ' hpo m y Q hQ
    exact ⟨D₁, e, Q₁, he, hQ₁, hc.trans hQr, rest⟩
  obtain ⟨E, e, Y'', u, φ'', he, hs, hpo', hy⟩ := hA hC q i φ' m y hloc
  exact ⟨E, e, Y'', u, φ'', he, hs, het d e hD he, hpo', hy⟩

end LateralTheory.E.KillCokPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CokernelKilling.AssembleOf
section -- merged from Development.EtaleCohomology.EtaleSheaves.CokernelKilling.FiniteSubcover
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.KillCokPf.Lem

theorem et_isOpenMap {D D₁ : CommRingCat.{0}} (e : D ⟶ D₁) (he : Et e) : IsOpenMap (PrimeSpectrum.comap e.hom) := by
  letI := e.hom.toAlgebra
  haveI : Algebra.Etale D D₁ := he
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := D) (S := D₁)

theorem finite_subcover {D : CommRingCat.{0}} (D₁ : PrimeSpectrum D → CommRingCat.{0}) (e : ∀ r, D ⟶ D₁ r)
    (he : ∀ r, Et (e r)) (hr : ∀ r, r ∈ Set.range (PrimeSpectrum.comap (e r).hom)) :
    ∃ s : Finset (PrimeSpectrum D), ∀ x : PrimeSpectrum D, ∃ r ∈ s, x ∈ Set.range (PrimeSpectrum.comap (e r).hom) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun r => Set.range (PrimeSpectrum.comap (e r).hom))
    (fun r => (et_isOpenMap (e r) (he r)).isOpen_range) (fun x _ => Set.mem_iUnion.2 ⟨x, hr x⟩)
  refine ⟨s, fun x => ?_⟩
  have := hs (Set.mem_univ x)
  simp only [Set.mem_iUnion] at this
  obtain ⟨r, hrs, hx⟩ := this
  exact ⟨r, hrs, hx⟩

end LateralTheory.E.KillCokPf.Lem
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.KillCokPf.Asm

abbrev piMap {D : CommRingCat.{0}} {ι : Type} (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k) :
    D ⟶ CommRingCat.of (∀ k, D₁ k) :=
  CommRingCat.ofHom (Pi.ringHom fun k => (e k).hom)

def ProdGlue : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) {ι : Type} [Fintype ι] (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k),
  (∀ k, Et (e k)) →
  (∀ k, ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ k ⟶ Y₁), IsPushout φ' (e k) u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  Et (piMap D₁ e) ∧ ∃ (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : CommRingCat.of (∀ k, D₁ k) ⟶ Y''),
    IsPushout φ' (piMap D₁ e) u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem sps_pi {D : CommRingCat.{0}} {ι : Type} (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k)
    (hc : ∀ x : PrimeSpectrum D, ∃ k, x ∈ Set.range (PrimeSpectrum.comap (e k).hom)) : SpS (piMap D₁ e) := by
  intro r hr
  obtain ⟨k, P, hP⟩ := hc ⟨r, hr⟩
  refine ⟨P.asIdeal.comap (Pi.evalRingHom (fun k => D₁ k) k), Ideal.comap_isPrime _ _, ?_⟩
  have h := congrArg PrimeSpectrum.asIdeal hP
  simp only [PrimeSpectrum.comap_asIdeal] at h
  rw [← h, Ideal.comap_comap]
  rfl

theorem Assemble_of (hG : ProdGlue) : LateralTheory.E.KillCokPf.Assemble := by
  intro hC q _ i D Y' φ' m y hloc
  have h' : ∀ x : PrimeSpectrum D, ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁), Et e ∧
      x ∈ Set.range (PrimeSpectrum.comap e.hom) ∧
      ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m) := by
    intro x
    obtain ⟨D₁, e, Q₁, he, hQ₁, hc, rest⟩ := hloc x.asIdeal x.isPrime
    exact ⟨D₁, e, he, ⟨⟨Q₁, hQ₁⟩, PrimeSpectrum.ext hc⟩, rest⟩
  choose D₁ e he hx hY using h'
  obtain ⟨s, hs⟩ := LateralTheory.E.KillCokPf.Lem.finite_subcover D₁ e he hx
  obtain ⟨het, Y'', u, φ'', hpo, hy⟩ := hG hC q i φ' m y (ι := s) (fun k => D₁ k.1) (fun k => e k.1)
    (fun k => he k.1) (fun k => hY k.1)
  refine ⟨_, _, Y'', u, φ'', het, sps_pi _ _ ?_, hpo, hy⟩
  intro x
  obtain ⟨r, hr, hxr⟩ := hs x
  exact ⟨⟨r, hr⟩, hxr⟩

end LateralTheory.E.KillCokPf.Asm
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.KillCokPf.Asm

namespace LateralTheory.E.KillCokPf.Glue

theorem et_pi {D : CommRingCat.{0}} {ι : Type} [Finite ι] (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k)
    (he : ∀ k, Et (e k)) : Et (piMap D₁ e) := by
  letI : ∀ k, Algebra D (D₁ k) := fun k => (e k).hom.toAlgebra
  haveI : ∀ k, Algebra.Etale D (D₁ k) := he
  have h : Algebra.Etale D (∀ k, D₁ k) := inferInstance
  exact h

def PushGlue : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) {ι : Type} [Fintype ι] (D₁ : ι → CommRingCat.{0}) (e : ∀ k, D ⟶ D₁ k),
  (∀ k, Et (e k)) →
  (∀ k, ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ k ⟶ Y₁), IsPushout φ' (e k) u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  ∃ (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : CommRingCat.of (∀ k, D₁ k) ⟶ Y''),
    IsPushout φ' (piMap D₁ e) u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem ProdGlue_of (hP : PushGlue) : ProdGlue := by
  intro hC q _ i D Y' φ' m y ι _ D₁ e he hk
  exact ⟨et_pi D₁ e he, hP hC q i φ' m y D₁ e he hk⟩

theorem KillCok_of' (hC : Coprod) (hP : LateralTheory.E.KillCokPf.Pointwise) (hG : PushGlue) : LateralTheory.E.DescLocPf.Fine.KillCok :=
  LateralTheory.E.KillCokPf.KillCok_of hC hP (Assemble_of (ProdGlue_of hG))

end LateralTheory.E.KillCokPf.Glue

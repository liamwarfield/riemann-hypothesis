module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameGenericFibreChainRescaledDeeperRealisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameGenericFibreChainRescaledDeeperRealisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SameChain

theorem spec_endo_eq_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (g : Sp Ω ⟶ Sp Ω)
    (h : g ≫ spMap R.val.toRingHom = spMap R.val.toRingHom) : g = 𝟙 _ := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have h2 : CommRingCat.ofHom R.val.toRingHom ≫ ψ = CommRingCat.ofHom R.val.toRingHom :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h)
  have e : ∀ c ∈ R, ψ.hom c = c := fun c hc => congrArg (fun f => f.hom (⟨c, hc⟩ : R)) h2
  have hψ : ψ = 𝟙 _ := by
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    simp [map_div₀, e a ha, e b hb]
  rw [hψ, Spec.map_id]

theorem sec_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) {G : Over (Sp Ω)}
    (a : G.left ⟶ ρ.P.A.left) (h : IsPullback a G.hom ρ.P.A.hom (spMap S.R.val.toRingHom)) (w : Sp Ω ⟶ G.left)
    (x : S.Gam) (hw : w ≫ a = spMap S.R.val.toRingHom ≫ (ρ.pt x).left) : w ≫ G.hom = 𝟙 _ := by
  refine spec_endo_eq_id S.R S.frac _ ?_
  rw [Category.assoc, ← h.w, ← Category.assoc, hw, Category.assoc, Over.w (ρ.pt x)]
  simp

end GlobalTheory.Poinc.SameChain


open GlobalTheory.Poinc.SameChain in
theorem GlobalTheory.Poinc.same_chain_deep : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (D : Deep X₁ ε₁)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A))
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)),
  Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) →
  Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) := by
  intro g n F W Z i X₁ ε₁ D c₀ hc R' fg frac hth hev ρ' ε' c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ h1 h3
  obtain ⟨P₁, a₁, a₁', e₁, pa₁, pa₁', L₁, L₁', E₁, T₁⟩ := h1
  obtain ⟨P₀, b, b', e₀, pb, pb', L₀, L₀', E₀, T₀⟩ := D.same
  obtain ⟨P₃, c, c', e₃, pc, pc', L₃, L₃', E₃, T₃⟩ := h3
  have pa₁c : IsGrpPullback P₁.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a₁ := pa₁.congr (by rw [RingHom.id_comp]) rfl
  have pcc : IsGrpPullback P₃.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) c := pc.congr (by rw [RingHom.id_comp]) rfl
  have hspc := Geo.Tor.spMap_comp X₁.S.R.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)
  have pbc : IsGrpPullback P₀.A X₁.ρ.P.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom) b :=
    pb.congr hspc rfl
  have wm : b ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [pbc.1.w, Category.assoc]
  set m := pa₁c.1.lift b (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) wm with hmdef
  have hm1 : m ≫ a₁ = b := pa₁c.1.lift_fst _ _ wm
  have hm2 : m ≫ P₁.A.hom = P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁) := pa₁c.1.lift_snd _ _ wm
  have pm : IsGrpPullback P₀.A P₁.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m := pa₁c.cancel (pbc.congr rfl hm1.symm) hm2
  obtain ⟨e, he_mon, he⟩ := grpPullback_iso pb' pcc
  haveI := he_mon
  have pe := isGrpPullback_of_iso e
  refine ⟨P₀, m ≫ a₁', e.hom.left ≫ c', e₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pm.comp pa₁').congr (Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)).symm rfl
  · exact (pe.comp pc').congr (Category.id_comp _) rfl
  · have A : LBIso (X₁.ρ.P.L.pull b) (P₁.L.pull m) :=
      LBIso.chartPull (chartPullSame X₁.ρ.P.L (K := PUnit) (fun _ => b) (fun _ => a₁) (fun _ => 1) m
        (fun _ => hm1.symm)) (chartPullPull P₁.L m) L₁.symm
    have B : LBIso (P₁.L.pull m) (ρ'.P.L.pull (m ≫ a₁')) :=
      LBIso.chartPull (chartPullPull P₁.L m) (chartPullSame ρ'.P.L (K := PUnit) (fun _ => m ≫ a₁') (fun _ => a₁')
        (fun _ => 1) m (fun _ => rfl)) L₁'
    exact LBIso.trans P₀.isLB (pull_isLB P₁.isLB m) (pull_isLB ρ'.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB b) (pull_isLB P₁.isLB m) L₀ A) B
  · have A : LBIso (D.X.ρ.P.L.pull b') (P₃.L.pull e.hom.left) :=
      LBIso.chartPull (chartPullSame D.X.ρ.P.L (K := PUnit) (fun _ => b') (fun _ => c) (fun _ => 1) e.hom.left
        (fun _ => he.symm)) (chartPullPull P₃.L e.hom.left) L₃.symm
    have B : LBIso (P₃.L.pull e.hom.left) (ρ₂.P.L.pull (e.hom.left ≫ c')) :=
      LBIso.chartPull (chartPullPull P₃.L e.hom.left) (chartPullSame ρ₂.P.L (K := PUnit)
        (fun _ => e.hom.left ≫ c') (fun _ => c') (fun _ => 1) e.hom.left (fun _ => rfl)) L₃'
    exact LBIso.trans P₀.isLB (pull_isLB P₃.isLB _) (pull_isLB ρ₂.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB D.X.ρ.P.isLB b') (pull_isLB P₃.isLB _) L₀' A) B
  · intro E
    have k1 : (e₀ E).left ≫ m = m ≫ (e₁ E).left := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, (E₀ E).1, Category.assoc, (E₁ E).1, ← Category.assoc, hm1]
      · rw [Category.assoc, hm2, ← Category.assoc, Over.w (e₀ E), Category.assoc, Over.w (e₁ E), hm2]
    have k3 : (e₀ E).left ≫ e.hom.left = e.hom.left ≫ (e₃ E).left := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, (E₀ E).2, Category.assoc, (E₃ E).1, ← Category.assoc, he]
      · rw [Category.assoc, Over.w e.hom, Over.w (e₀ E), Category.assoc, Over.w (e₃ E), Over.w e.hom]
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, k1, Category.assoc, (E₁ E).2, Category.assoc]
    · rw [← Category.assoc, k3, Category.assoc, (E₃ E).2, Category.assoc]
  · intro x
    obtain ⟨w, hw, hw'⟩ := T₀ x
    obtain ⟨w₁, hw₁, hw₁'⟩ := T₁ x
    obtain ⟨w₃, hw₃, hw₃'⟩ := T₃ (D.lab x)
    have s0 : w ≫ P₀.A.hom = 𝟙 _ := sec_of_pt D.X.ρ b' pb'.1 w _ hw'
    have s1 : w₁ ≫ P₁.A.hom = 𝟙 _ := sec_of_pt ρ' a₁' pa₁'.1 w₁ _ hw₁'
    have s3 : w₃ ≫ P₃.A.hom = 𝟙 _ := sec_of_pt ρ₂ c' pc'.1 w₃ _ hw₃'
    have hwm : w ≫ m = spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ w₁ := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, hw, Category.assoc, hw₁, hspc, Category.assoc, RingHom.id_comp]
      · rw [Category.assoc, hm2, ← Category.assoc, s0, Category.id_comp, Category.assoc, s1, Category.comp_id]
    have hwe : w ≫ e.hom.left = w₃ := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, hw', hw₃, RingHom.id_comp]
      · rw [Category.assoc, Over.w e.hom, s0, s3]
    refine ⟨w, ?_, ?_⟩
    · rw [← Category.assoc, hwm, Category.assoc, hw₁', Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁),
        Category.assoc]
    · rw [← Category.assoc, hwe, hw₃']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameGenericFibreChainRescaledDeeperRealisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameGenericFibre_chain_rescaled_deeper_realisation : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (D : Deep X₁ ε₁)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A))
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)),
  Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) →
  Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) := by
  first | exact @GlobalTheory.Poinc.same_chain_deep | exact GlobalTheory.Poinc.same_chain_deep | (intros; apply GlobalTheory.Poinc.same_chain_deep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentsAbelianSchemeConstantDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentsAbelianSchemeConstantDimension
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DimSplit

theorem idem_eq_of {S : Type} [CommRing S] {a b : S} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : ∀ q : PrimeSpectrum S, a ∉ q.asIdeal ↔ b ∉ q.asIdeal) : a = b := by
  have := (PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).injective
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (by
      ext q
      show q ∈ PrimeSpectrum.basicOpen a ↔ q ∈ PrimeSpectrum.basicOpen b
      simp only [PrimeSpectrum.mem_basicOpen]
      exact hab q)
  exact congrArg Subtype.val this

theorem exists_idempotents_of_isLocallyConstant {R α : Type} [CommRing R] (d : PrimeSpectrum R → α)
    (hd : IsLocallyConstant d) :
    ∃ (n : ℕ) (e : Fin n → R), CompleteOrthogonalIdempotents e ∧
      ∀ k, ∃ a : α, ∀ p : PrimeSpectrum R, 1 - e k ∈ p.asIdeal → d p = a := by
  classical
  have hfin : (Set.range d).Finite := hd.range_finite
  let s := hfin.toFinset
  let g : Fin s.card → α := fun k => (s.equivFin.symm k).1
  have hg : Function.Injective g := fun i j h => s.equivFin.symm.injective (Subtype.val_injective h)
  let C : Fin s.card → TopologicalSpace.Clopens (PrimeSpectrum R) := fun k =>
    ⟨d ⁻¹' {g k}, hd.isClopen_fiber _⟩
  let e : Fin s.card → R := fun k => ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).1
  have he : ∀ k, IsIdempotentElem (e k) := fun k =>
    ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).2
  have hmem : ∀ k (p : PrimeSpectrum R), e k ∉ p.asIdeal ↔ d p = g k := by
    intro k p
    have h := PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm (R := R) (C k)
    rw [← PrimeSpectrum.mem_basicOpen]
    show p ∈ PrimeSpectrum.basicOpen (e k) ↔ _
    rw [h]
    rfl
  have horth : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij => idem_eq_of ((he i).mul (he j)) IsIdempotentElem.zero fun q => ?_⟩
    refine ⟨fun h => ?_, fun h => absurd q.asIdeal.zero_mem h⟩
    have hi : e i ∉ q.asIdeal := fun hi => h (q.asIdeal.mul_mem_right _ hi)
    have hj : e j ∉ q.asIdeal := fun hj => h (q.asIdeal.mul_mem_left _ hj)
    exact absurd (hg (((hmem i q).1 hi).symm.trans ((hmem j q).1 hj))) hij
  refine ⟨s.card, e, ⟨horth, ?_⟩, fun k => ⟨g k, fun p hp => (hmem k p).1 fun hk => ?_⟩⟩
  · refine idem_eq_of horth.isIdempotentElem_sum IsIdempotentElem.one fun q => ?_
    refine ⟨fun _ => q.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2, fun _ hsum => ?_⟩
    have hq : d q ∈ s := hfin.mem_toFinset.2 ⟨q, rfl⟩
    let k := s.equivFin ⟨d q, hq⟩
    have hk : g k = d q := by simp [g, k]
    have hrest : ∑ j ∈ Finset.univ.erase k, e j ∈ q.asIdeal := by
      refine Ideal.sum_mem _ fun j hj => ?_
      by_contra hj'
      exact (Finset.ne_of_mem_erase hj) (hg (((hmem j q).1 hj').symm.trans hk.symm))
    have : e k ∈ q.asIdeal := by
      have h2 := q.asIdeal.sub_mem hsum hrest
      rwa [← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_right] at h2
    exact (hmem k q).2 hk.symm this
  · exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using p.asIdeal.add_mem hp hk))

end GlobalTheory.DimSplit

namespace GlobalTheory.DimSplit

theorem exists_idempotents_smoothOfRelativeDimension : ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A],
    IsAbelianScheme A → ∃ (n : ℕ) (e : Fin n → R₀), CompleteOrthogonalIdempotents e ∧ ∀ k, ∃ g : ℕ,
      SmoothOfRelativeDimension g (Limits.pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k})))) := by
  intro R₀ _ A _ hA
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have fib : ∀ x y, A.hom x = A.hom y → n x = n y := fun x y h =>
    hc.apply_eq_of_isPreconnected (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected
      rfl h.symm
  have hsurj : Function.Surjective A.hom := (inferInstance : Surjective A.hom).surj
  let d : PrimeSpectrum R₀ → ℕ := fun p => n (Classical.choose (hsurj p))
  have hdn : ∀ x, d (A.hom x) = n x := fun x => fib _ _ (Classical.choose_spec (hsurj (A.hom x)))
  have hdl : IsLocallyConstant d := by
    refine (IsLocallyConstant.iff_isOpen_fiber).2 fun g => ?_
    have hcl : IsClosed (A.hom '' (n ⁻¹' {g})ᶜ) :=
      A.hom.isClosedMap _ (hc.isOpen_fiber g).isClosed_compl
    have heq : (d ⁻¹' {g})ᶜ = A.hom '' (n ⁻¹' {g})ᶜ := by
      ext p
      refine ⟨fun hp => ⟨_, hp, Classical.choose_spec (hsurj p)⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact fun h => hx (show n x = g from (hdn x).symm.trans h)
    rw [← isClosed_compl_iff, heq]
    exact hcl
  obtain ⟨m, e, he, hk⟩ := exists_idempotents_of_isLocallyConstant d hdl
  refine ⟨m, e, he, fun k => ?_⟩
  obtain ⟨g, hg⟩ := hk k
  refine ⟨g, GlobalTheory.SmoothNearFibre.smoothOfRelativeDimension_pullback_snd A.hom _ g fun z w hzw => ⟨W z, hW z, ?_⟩⟩
  have hn : n z = g := by
    rw [← hdn z, hzw]
    apply hg
    show Ideal.Quotient.mk _ (1 - e k) ∈ w.asIdeal
    have h0 : Ideal.Quotient.mk (Ideal.span {1 - e k}) (1 - e k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))
    rw [h0]
    exact w.asIdeal.zero_mem
  rw [← hn]
  exact hd z

end GlobalTheory.DimSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentsAbelianSchemeConstantDimensionStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotents_abelianScheme_constant_dimension : ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A], IsAbelianScheme A → ∃ (n : ℕ) (e : Fin n → R₀), CompleteOrthogonalIdempotents e ∧ ∀ k, ∃ g : ℕ, SmoothOfRelativeDimension g (Limits.pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k})))) := by
  first | exact @GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension | exact GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension | (intros; apply GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphism
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

section Chart

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

theorem chart_spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem chart_spMap_inj {A B : Type} [CommRing A] [CommRing B] {a b : A →+* B} (e : spMap a = spMap b) : a = b := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

variable (hI : I ^ 2 = 0) {X₀ Z₀ X Z : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {t₀ : Z₀ ⟶ Sp R₀} {s : X ⟶ Sp R}
  {t : Z ⟶ Sp R} {i : X₀ ⟶ X} {k : Z₀ ⟶ Z} {S : Sys I π s₀} {S' : Sys I π t₀} (P : S.Presents s i)
  (P' : S'.Presents t k) {f₀ : Z₀ ⟶ X₀} {f : Z ⟶ X} (hkf : k ≫ f = f₀ ≫ i)


include hkf in
theorem chart_red (p : Pair f₀) :
    spMap (S'.p (Opposite.op p.1.1)) ≫ P'.y (Opposite.op p.1.1) ≫ f =
      spMap (GlobalTheory.CechDR.secPull s₀ t₀ p) ≫ spMap (S.p (Opposite.op p.1.2)) ≫ P.y (Opposite.op p.1.2) := by
  rw [← Category.assoc, P'.red, P.red, Category.assoc, hkf, ← Category.assoc, ← Category.assoc,
    ← GlobalTheory.CechDR.secPull_affPt s₀ t₀ p, Category.assoc]


include hI hkf in
theorem chart_range (p : Pair f₀) :
    Set.range ⇑(P'.y (Opposite.op p.1.1) ≫ f) ⊆ Set.range ⇑(P.y (Opposite.op p.1.2)) := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨q₀, rfl⟩ := (S'.surjective_spMap_p hI (Opposite.op p.1.1)).surj q
  have e := congrArg (fun g ↦ g q₀) (chart_red P P' hkf p)
  simp only [Scheme.Hom.comp_apply] at e
  rw [Scheme.Hom.comp_apply, e]
  exact ⟨_, rfl⟩

def chartMor (p : Pair f₀) : Sp (S'.F.obj (Opposite.op p.1.1)) ⟶ Sp (S.F.obj (Opposite.op p.1.2)) :=
  haveI := P.isOpen (Opposite.op p.1.2)
  IsOpenImmersion.lift _ _ (chart_range hI P P' hkf p)

theorem chartMor_fac (p : Pair f₀) :
    chartMor hI P P' hkf p ≫ P.y (Opposite.op p.1.2) = P'.y (Opposite.op p.1.1) ≫ f :=
  haveI := P.isOpen (Opposite.op p.1.2)
  IsOpenImmersion.lift_fac _ _ _

def chartRing (p : Pair f₀) : S.F.obj (Opposite.op p.1.2) →+* S'.F.obj (Opposite.op p.1.1) :=
  (Spec.preimage (chartMor hI P P' hkf p)).hom

theorem spMap_chartRing (p : Pair f₀) : spMap (chartRing hI P P' hkf p) = chartMor hI P P' hkf p := by
  simp only [spMap, chartRing, CommRingCat.ofHom_hom]
  exact Spec.map_preimage _

theorem chart_ext {A : Type} [CommRing A] (U : AffOp X₀) {a b : S.F.obj U →+* A}
    (e : spMap a ≫ P.y U = spMap b ≫ P.y U) : a = b :=
  haveI := P.isOpen U
  chart_spMap_inj ((cancel_mono (P.y U)).1 e)

include hkf in
theorem chartRing_fac (p : Pair f₀) :
    spMap (chartRing hI P P' hkf p) ≫ P.y (Opposite.op p.1.2) = P'.y (Opposite.op p.1.1) ≫ f := by
  rw [spMap_chartRing, chartMor_fac]


include hkf in
theorem chartRing_comp_algebraMap (hf : f ≫ s = t) (p : Pair f₀) :
    (chartRing hI P P' hkf p).comp (algebraMap R (S.F.obj (Opposite.op p.1.2))) =
      algebraMap R (S'.F.obj (Opposite.op p.1.1)) := by
  refine chart_spMap_inj ?_
  rw [chart_spMap_comp, ← P.base, ← Category.assoc, chartRing_fac, Category.assoc, hf, P'.base]

def chartAlg (hf : f ≫ s = t) (p : Pair f₀) : S.F.obj (Opposite.op p.1.2) →ₐ[R] S'.F.obj (Opposite.op p.1.1) :=
  { chartRing hI P P' hkf p with
    commutes' := fun r ↦ congrArg (fun g ↦ g r) (chartRing_comp_algebraMap hI P P' hkf hf p) }


include hkf in
theorem chartRing_red (p : Pair f₀) :
    (S'.p (Opposite.op p.1.1)).comp (chartRing hI P P' hkf p) =
      (GlobalTheory.CechDR.secPull s₀ t₀ p).comp (S.p (Opposite.op p.1.2)) := by
  refine chart_ext P _ ?_
  rw [chart_spMap_comp, chart_spMap_comp, Category.assoc, Category.assoc, chartRing_fac, chart_red P P' hkf p]


include hkf in
theorem chartRing_nat {p q : Pair f₀} (a : q ≤ p) (b : S.F.obj (Opposite.op p.1.2)) :
    mp S'.F (homOfLE (Pair.le_fst a)).op (chartRing hI P P' hkf p b) =
      chartRing hI P P' hkf q (mp S.F (homOfLE (Pair.le_snd a)).op b) := by
  have e : ((mp S'.F (homOfLE (Pair.le_fst a)).op : _ →+* _)).comp (chartRing hI P P' hkf p) =
      (chartRing hI P P' hkf q).comp (mp S.F (homOfLE (Pair.le_snd a)).op : _ →+* _) := by
    refine chart_ext P _ ?_
    rw [chart_spMap_comp, chart_spMap_comp, Category.assoc, Category.assoc, chartRing_fac, P.nat,
      chartRing_fac, ← Category.assoc, P'.nat]
  exact congrArg (fun g ↦ g b) e

end Chart

end GlobalTheory.Obs

namespace GlobalTheory.Obs

theorem exists_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (f : Z ⟶ X), f ≫ s = t → k ≫ f = f₀ ≫ i → ∃ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l ∧ (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l := by
  intro R R₀ _ _ I hI π _ _ X₀ Z₀ X Z s₀ t₀ s t i k _ _ S S' P P' f₀ h f hf hkf
  refine ⟨fun T ↦ chartAlg hI P P' hkf hf T.unop, fun T b ↦ ?_, fun T T' a b ↦ ?_⟩
  · exact congrArg (fun g ↦ g b) (chartRing_red hI P P' hkf T.unop)
  · exact chartRing_nat hI P P' hkf (leOfHom a.unop) b

end GlobalTheory.Obs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphismStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_natural_chart_lifts_of_morphism : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (f : Z ⟶ X), f ≫ s = t → k ≫ f = f₀ ≫ i → ∃ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l ∧ (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l := by
  first | exact @GlobalTheory.Obs.exists_chart_lifts | exact GlobalTheory.Obs.exists_chart_lifts | (intros; apply GlobalTheory.Obs.exists_chart_lifts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.ModelFrameCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isCombAtG_push {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f : S₁ ⟶ S₀} (mm : SABMap t' t f)
    {R : Type} [CommRing R] (x : Sp R ⟶ S₁) {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} {a : Fin n → R}
    {w : Sp (DualNumber R) ⟶ t'.G.left} (h : IsCombAtG t' x v a w) :
    IsCombAtG t (x ≫ f) (fun i => v i ≫ mm.φ) a (w ≫ mm.φ) := by
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv mm.cart
    (spMap (algebraMap R (DualNumber R)) ≫ x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) (Category.assoc _ _ _)
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨fun i => B (u i), fun i => ?_, ?_⟩
  · rw [hB, hu, Category.assoc]
  · have e : B (List.ofFn u).prod = (List.ofFn fun i => B (u i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [← e, hB, hw]

theorem isCombAtG_reflect {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f : S₁ ⟶ S₀} (mm : SABMap t' t f)
    {R : Type} [CommRing R] (x : Sp R ⟶ S₁) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left))
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) {a : Fin n → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t (x ≫ f) (fun i => v i ≫ mm.φ) a w) :
    ∃ w' : Sp (DualNumber R) ⟶ t'.G.left, w' ≫ mm.φ = w ∧ IsCombAtG t' x v a w' := by
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv mm.cart
    (spMap (algebraMap R (DualNumber R)) ≫ x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) (Category.assoc _ _ _)
  obtain ⟨u, hu, hw⟩ := h
  have hBs : ∀ z, (B.symm z).left ≫ mm.φ = z.left := fun z => by rw [← hB, B.apply_symm_apply]
  refine ⟨(B.symm (List.ofFn u).prod).left, by rw [hBs, hw], fun i => B.symm (u i), fun i => ?_, ?_⟩
  · refine mm.cart.1.hom_ext ?_ ?_
    · rw [hBs, hu, Category.assoc]
    · rw [Over.w (B.symm (u i)), Category.assoc, hv, ← Category.assoc, GlobalTheory.Exist.FlagBaseChange.epsMul_over]
      rfl
  · rw [map_list_prod, List.map_ofFn]
    rfl

theorem exists_sabMap_congr {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f f' : S₁ ⟶ S₀} (mm : SABMap t' t f)
    (h : f = f') : ∃ mm' : SABMap t' t f', mm'.φ = mm.φ := by
  subst h
  exact ⟨mm, rfl⟩

end GlobalTheory.ModelFrameCompare

namespace GlobalTheory.ModelFrameCompare


set_option maxHeartbeats 1000000 in
theorem images_eigenBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (σ : E →+* ℂ) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (xV : Sp T.V ⟶ Y.X) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ xV → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ v : Fin (Dw.mult σ) → (Sp (DualNumber T.V) ⟶ Y.t.G.left), (∀ j, IsTanAtG Y.t xV (v j)) ∧ (∀ u : Sp (DualNumber T.V) ⟶ Y.t.G.left, IsTanAtG Y.t xV u → (∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) → u ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u) → ∃ cf : Fin (Dw.mult σ) → T.V, IsCombAtG Y.t xV v cf u) ∧ ∀ (cf : Fin (Dw.mult σ) → T.V) (u : Sp (DualNumber T.V) ⟶ Y.t.G.left) (w : Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left), IsCombAtG Y.t xV v cf u → w ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u → (letI := io.toAlgebra; IsCombAt y₀.1.x (y₀.1.u σ) (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ ν.φ)) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν σ T io y₀ xV yy hxV hpt
  let _ := io.toAlgebra
  obtain ⟨G₂, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull xV Y.t
  obtain ⟨t₂, n₀, n₂, m', -, h2⟩ := GlobalTheory.ThetaFrameCheck.genFibre_tied Xo' c' T _ _ Y xV yy hxV G₂ m
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t t₂ _ yy ν m'
  obtain ⟨G, t', m1, m2, ⟨ub, ht, he, hb, hl⟩, -⟩ := y₀.2.2
  have hx : y₀.1.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hpt]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨m1', hm1'⟩ := exists_sabMap_congr m1 hx
  obtain ⟨k, n, hk1, hk2⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr _ G G₂ t' t₂ m1' m2 n₁ n₂
  obtain ⟨nm, hnm⟩ := sabComp pullCubComp E H _ _ _ Y.t G₂ G xV (𝟙 _) m n
  obtain ⟨q₀, hq₀⟩ := exists_sabMap_congr nm (Category.id_comp xV)
  rw [hnm] at hq₀
  obtain ⟨B, hB, hBt, hBe, hBc⟩ := GlobalTheory.FactorDepth.Extension.exists_tanEquiv q₀
  refine ⟨fun j => (B (ub σ j)).left, fun j => (hBt _).2 (ht σ j), ?_, ?_⟩
  · intro u hu hue
    obtain ⟨w', hw'⟩ := B.surjective (ovT hu)
    have e : u = (B w').left := by rw [hw']; rfl
    subst e
    obtain ⟨cf, hcf, -⟩ := hb σ w' ((hBt _).1 hu) fun a z hz => (hBe _ a z).1 (hue a z hz)
    exact ⟨cf, (hBc _ _ cf w').2 hcf⟩
  · intro cf u w hc hw
    have h3 := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t (algebraMap T.V T.Fr) hc
    obtain ⟨q, hq⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t₂ _ yy Y.m m'
    choose u' hu1 hu2 using hl σ
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub σ j), spMap_comp',
        ← dualMap_comp_alg, ← spMap_comp']
      rfl
    have hov' : ∀ j, (u' j ≫ k.φ) ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
      intro j
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, hov]
    have hvec : ∀ j, spMap (dualMap (algebraMap T.V T.Fr)) ≫ (B (ub σ j)).left = (u' j ≫ k.φ) ≫ q.φ := by
      intro j
      rw [hB, hq₀, hq, ← Category.assoc, ← hu2, Category.assoc, ← Category.assoc m2.φ, hk2]
      simp only [Category.assoc, h2]
    have hpt' : spMap (algebraMap T.V T.Fr) ≫ xV = 𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _ := by
      rw [Category.id_comp, ← hxV]; rfl
    have h4 : IsCombAtG Y.t (𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _) (fun j => (u' j ≫ k.φ) ≫ q.φ)
        (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ Y.m.φ) := by
      rw [← hpt', hw]
      simpa only [hvec] using h3
    obtain ⟨w₂, hw₂, hc₂⟩ := isCombAtG_reflect q (𝟙 _) (fun j => u' j ≫ k.φ) hov' h4
    have hw₂' : w₂ ≫ m'.φ = w := by
      refine Y.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, ← hq, hw₂]
      · have := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
        have hmono : Mono Y.j := inferInstance
        have e2 : w₂ ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
          obtain ⟨uu, -, hh⟩ := hc₂
          rw [← hh]; exact Over.w _
        have e1 : u ≫ Y.t.G.hom = spMap (algebraMap T.V (DualNumber T.V)) ≫ xV := by
          obtain ⟨uu, -, hh⟩ := hc
          rw [← hh]; exact Over.w _
        rw [Category.assoc, m'.cart.1.w, ← Category.assoc, e2, Category.comp_id]
        apply hmono.right_cancellation
        have e3 : spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) ≫ xV =
            spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ yy ≫ Y.j := by
          rw [← Category.assoc, spMap_comp', dualMap_comp_alg, ← spMap_comp', Category.assoc, hxV]
        show (spMap _ ≫ yy) ≫ Y.j = w ≫ Y.oF.t.G.hom ≫ Y.jQ ≫ pullback.fst _ _
        rw [← Y.m.cart.1.w, ← Category.assoc w, hw, Category.assoc (spMap _) u, e1, e3, Category.assoc]
    have h5 := isCombAtG_push n₁ (𝟙 _) hc₂
    have hv5 : (fun j => (u' j ≫ k.φ) ≫ n₁.φ) = y₀.1.u σ := by
      funext j
      rw [Category.assoc, hk1, hm1', hu1]
    rw [hv5, hn₁, ← Category.assoc w₂, hw₂', Category.id_comp, ← hx] at h5
    exact h5

end GlobalTheory.ModelFrameCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSmoothLiftOverSqZeroThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSmoothLiftOverSqZeroThickening
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

open MvPolynomial in
theorem mvPolynomial_map_pderiv_lift {κ R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (i : κ)
    (f : MvPolynomial κ R) :
    MvPolynomial.map π (pderiv i f) = pderiv i (MvPolynomial.map π f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), hp, map_X, pderiv_X]
    congr 1
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, Ne.symm h]

theorem isUnit_of_isUnit_map_of_sqZero_ker {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀)
    (hp : Function.Surjective p) (K : Ideal A) (hK : K ^ 2 = 0) (hker : ∀ a, p a = 0 → a ∈ K)
    (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp u
  have hn : x * y - 1 ∈ K := hker _ (by simp [hu])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this


open MvPolynomial in
theorem standardSmooth_lift_of_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.IsStandardSmooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B₀ _ _ hB₀
  obtain ⟨κ, τ, _, _, ⟨P⟩⟩ := hB₀.out
  classical
  have : Fintype τ := Fintype.ofFinite τ
  have hmap : Function.Surjective (MvPolynomial.map (σ := κ) π) := MvPolynomial.map_surjective π hπ
  let v : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (P.relation j)
  have hv : ∀ j, MvPolynomial.map π (v j) = P.relation j := fun j => Function.surjInv_eq hmap _
  let J : Ideal (MvPolynomial κ R) := Ideal.span (Set.range v)
  let φ : MvPolynomial κ R →+* B₀ := (aeval P.val).toRingHom.comp (MvPolynomial.map π)
  have hφ : ∀ f, φ f = aeval P.val (MvPolynomial.map π f) := fun _ => rfl
  have hJ : J ≤ RingHom.ker φ := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hφ, hv, Algebra.Presentation.aeval_val_relation]
  let p : (MvPolynomial κ R ⧸ J) →+* B₀ := Ideal.Quotient.lift J φ hJ
  have hp : ∀ f, p (Ideal.Quotient.mk J f) = φ f := fun _ => rfl
  have halg : ∀ r : R, p (algebraMap R _ r) = algebraMap R₀ B₀ (π r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial κ R) (MvPolynomial κ R ⧸ J)]
    simp [Ideal.Quotient.algebraMap_eq, hp, hφ]
  have hsemi : SemiHom π p := by
    intro r b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg]
  have hsurj : Function.Surjective p := by
    intro b
    obtain ⟨g, rfl⟩ := P.aeval_val_surjective b
    obtain ⟨f, rfl⟩ := hmap g
    exact ⟨Ideal.Quotient.mk J f, rfl⟩
  have hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R (MvPolynomial κ R ⧸ J)) := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    constructor
    · intro h0
      rw [hp, hφ] at h0
      have hmem : MvPolynomial.map π f ∈ Ideal.span (Set.range P.relation) := by
        rw [P.span_range_relation_eq_ker]
        first
          | exact h0
          | exact RingHom.mem_ker.mpr h0
          | (rw [Algebra.Generators.ker_eq_ker_aeval_val]; exact h0)
      obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
      let c' : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (c j)
      have hc' : ∀ j, MvPolynomial.map π (c' j) = c j := fun j => Function.surjInv_eq hmap _
      have hg : f - ∑ j, c' j * v j ∈ RingHom.ker (MvPolynomial.map (σ := κ) π) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [RingHom.mem_ker, map_sub, map_sum, ← hc]
        simp [hc', hv]
      rw [MvPolynomial.ker_map, hk] at hg
      have hs : ∑ j, c' j * v j ∈ J :=
        Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
      have : Ideal.Quotient.mk J f = Ideal.Quotient.mk J (f - ∑ j, c' j * v j) := by
        rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hs, sub_zero]
      rw [this]
      have hmm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hg
      rwa [Ideal.map_map] at hmm
    · intro hb
      have : I.map (algebraMap R (MvPolynomial κ R ⧸ J)) ≤ RingHom.ker p := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, RingHom.mem_ker, halg]
        have : π x = 0 := by rw [← RingHom.mem_ker, hk]; exact hx
        simp [this]
      exact this hb
  let Q := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  have hjac : p Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have h1 : ∀ f : MvPolynomial κ R, algebraMap Q.Ring (MvPolynomial κ R ⧸ Ideal.span (Set.range v)) f =
        Ideal.Quotient.mk J f := fun _ => rfl
    rw [h1, hp, hφ, Algebra.Generators.algebraMap_apply]
    congr 1
    rw [RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    show MvPolynomial.map π (pderiv (P.map i) (v j)) = pderiv (P.map i) (P.relation j)
    rw [mvPolynomial_map_pderiv_lift, hv]
  have hunit : IsUnit Q.jacobian := by
    refine isUnit_of_isUnit_map_of_sqZero_ker p hsurj (I.map (algebraMap R _)) ?_ (fun a ha => (hker a).1 ha) _
      (by rw [hjac]; exact P.jacobian_isUnit)
    rw [← Ideal.map_pow, hI]; simp
  let Q' : Algebra.SubmersivePresentation R (MvPolynomial κ R ⧸ J) κ τ :=
    { Q with jacobian_isUnit := hunit }
  have := Q'.isStandardSmooth
  exact ⟨_, inferInstance, inferInstance, p, hsemi, hsurj, hker, inferInstance⟩

end GlobalTheory.Obs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSmoothLiftOverSqZeroThickeningStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardSmooth_lift_over_sqZero_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.IsStandardSmooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.Obs.standardSmooth_lift_of_sqZero | exact GlobalTheory.Obs.standardSmooth_lift_of_sqZero | (intros; apply GlobalTheory.Obs.standardSmooth_lift_of_sqZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothLiftOfSquareZeroLiftSystemPresents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothLiftOfSquareZeroLiftSystemPresents
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

theorem isPushout_chart (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (S : Sys I π s₀) (U : AffOp X₀) :
    IsPushout (CommRingCat.ofHom (algebraMap R (S.F.obj U))) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (S.p U)) (CommRingCat.ofHom (algebraMap R₀ (Sec s₀ U.unop.1))) := by
  have hc : ∀ r : R, S.p U (algebraMap R (S.F.obj U) r) = algebraMap R₀ (Sec s₀ U.unop.1) (π r) :=
    fun r ↦ (S.semi U).map_algebraMap r
  have hz : ∀ a ∈ I, π a = 0 := fun a ha ↦ RingHom.mem_ker.1 (hk ▸ ha)
  have key : ∀ (t : Limits.PushoutCocone (CommRingCat.ofHom (algebraMap R (S.F.obj U))) (CommRingCat.ofHom π))
      (b : S.F.obj U), S.p U b = 0 → t.inl.hom b = 0 := by
    intro t b hb
    have hle : I.map (algebraMap R (S.F.obj U)) ≤ RingHom.ker t.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      have e : t.inl.hom (algebraMap R (S.F.obj U) a) = t.inr.hom (π a) := congr($(t.condition) a)
      rw [Ideal.mem_comap, RingHom.mem_ker, e, hz a ha, map_zero]
    exact hle ((S.ker U b).1 hb)
  let desc : ∀ t : Limits.PushoutCocone (CommRingCat.ofHom (algebraMap R (S.F.obj U))) (CommRingCat.ofHom π),
      Sec s₀ U.unop.1 →+* t.pt := fun t ↦
    (Ideal.Quotient.lift (RingHom.ker (S.p U)) t.inl.hom fun b hb ↦ key t b (RingHom.mem_ker.1 hb)).comp
      (RingHom.quotientKerEquivOfSurjective (S.surj U)).symm.toRingHom
  have hdesc : ∀ t b, desc t (S.p U b) = t.inl.hom b := by
    intro t b
    change Ideal.Quotient.lift _ t.inl.hom (fun b hb ↦ key t b (RingHom.mem_ker.1 hb)) ((RingHom.quotientKerEquivOfSurjective (S.surj U)).symm (S.p U b)) = _
    rw [show (RingHom.quotientKerEquivOfSurjective (S.surj U)).symm (S.p U b) = Ideal.Quotient.mk _ b by
      rw [RingEquiv.symm_apply_eq]; rfl]
    rfl
  refine ⟨⟨by ext r; exact hc r⟩, ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun t ↦ CommRingCat.ofHom (desc t)) ?_ ?_ ?_⟩⟩
  · intro t
    ext b
    exact hdesc t b
  · intro t
    ext r
    obtain ⟨a, rfl⟩ := hπ r
    change desc t (algebraMap R₀ (Sec s₀ U.unop.1) (π a)) = t.inr.hom (π a)
    rw [← hc, hdesc]
    exact congr($(t.condition) a)
  · intro t m h₁ _
    ext c
    obtain ⟨b, rfl⟩ := S.surj U c
    change m.hom (S.p U b) = desc t (S.p U b)
    rw [hdesc]
    exact congr($h₁ b)

theorem spMap_p_surjective (hI : I ^ 2 = 0) (S : Sys I π s₀) (U : AffOp X₀) :
    Function.Surjective (spMap (S.p U)) := by
  intro x
  have hx : x ∈ Set.range (PrimeSpectrum.comap (S.p U)) := by
    rw [range_comap_of_surjective (f := S.p U) (hf := S.surj U)]
    intro b hb
    have hb' : b ∈ I.map (algebraMap R (S.F.obj U)) := (S.ker U b).1 hb
    have h2 : b * b ∈ I.map (algebraMap R (S.F.obj U)) ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
    rw [map_sq hI] at h2
    have h0 : b * b ∈ (x : PrimeSpectrum (S.F.obj U)).asIdeal := by
      rw [show b * b = 0 from h2]; exact zero_mem _
    exact (Ideal.IsPrime.mem_or_mem (PrimeSpectrum.isPrime (x : PrimeSpectrum (S.F.obj U))) h0).elim id id
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, hz⟩

end GlobalTheory.LiftSys.Sys

namespace GlobalTheory.LiftSys.Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

theorem Presents.apply_red {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (P : S.Presents s i)
    (U : AffOp X₀) (z : Sp (Sec s₀ U.unop.1)) : P.y U (spMap (S.p U) z) = i (affPt s₀ U.unop z) := by
  have e := congrArg (fun f : Sp (Sec s₀ U.unop.1) ⟶ X ↦ f z) (P.red U)
  simpa only [Scheme.Hom.comp_apply] using e

instance isOpenImmersion_affPt (U : X₀.affineOpens) : IsOpenImmersion (affPt s₀ U) :=
  IsAffineOpen.isOpenImmersion_fromSpec U.2

theorem Presents.preimage_eq (hI : I ^ 2 = 0) {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}
    (hc : IsClosedImmersion i) (P : S.Presents s i) [∀ U, IsOpenImmersion (P.y U)] (U : AffOp X₀) :
    i ⁻¹ᵁ (P.y U).opensRange = (affPt s₀ U.unop).opensRange := by
  ext x
  simp only [Scheme.Hom.mem_preimage, Scheme.Hom.coe_opensRange, Set.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := spMap_p_surjective hI S U w
    refine ⟨z, i.isClosedEmbedding.injective ?_⟩
    rw [← P.apply_red, hw]
  · rintro ⟨z, rfl⟩
    exact ⟨_, P.apply_red U z⟩

end GlobalTheory.LiftSys.Sys


open GlobalTheory.LiftSys.Sys in
theorem GlobalTheory.LiftSys.presents_isLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i → Surjective i → S.Presents s i → IsPullback i s₀ s (spMap π) ∧ Smooth s := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S X s i hc hsurj P
  haveI : ∀ U, IsOpenImmersion (P.y U) := P.isOpen
  have hv : ∀ y : X, ∃ (U : AffOp X₀) (z : Sp (S.F.obj U)), P.y U z = y := by
    intro y
    obtain ⟨x, rfl⟩ := i.surjective y
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X₀.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hx' : x ∈ Set.range (affPt s₀ ⟨V, hV⟩) := by
      have e : Set.range (affPt s₀ ⟨V, hV⟩) = V := (show IsAffineOpen V from hV).range_fromSpec
      rw [e]; exact hx
    obtain ⟨z, rfl⟩ := hx'
    exact ⟨Opposite.op ⟨V, hV⟩, spMap (S.p _) z, P.apply_red _ z⟩
  constructor
  · refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Cover.mkOfCovers (AffOp X₀) _ P.y hv) fun (U : AffOp X₀) ↦ ?_
    change IsPullback (Limits.pullback.snd i (P.y U)) (Limits.pullback.fst i (P.y U) ≫ s₀) (P.y U ≫ s) (spMap π)
    have h := IsOpenImmersion.isPullback (spMap (S.p U)) (affPt s₀ U.unop) (P.y U) i (P.red U).symm
      (P.preimage_eq hI hc U)
    have h' : IsPullback (spMap (S.p U)) (affPt s₀ U.unop ≫ s₀) (P.y U ≫ s) (spMap π) := by
      rw [affPt_w, P.base]
      exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chart hπ hk S U)
    refine h'.of_iso h.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  · have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Scheme.Cover.mkOfCovers (AffOp X₀) _ P.y hv) fun (U : AffOp X₀) ↦ ?_
    change Smooth (P.y U ≫ s)
    rw [P.base, HasRingHomProperty.Spec_iff (P := @Smooth)]
    haveI := S.smooth U
    exact RingHom.smooth_algebraMap.2 inferInstance
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothLiftOfSquareZeroLiftSystemPresentsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothLift_of_squareZeroLiftSystemPresents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i → Surjective i → S.Presents s i → IsPullback i s₀ s (spMap π) ∧ Smooth s := by
  first | exact @GlobalTheory.LiftSys.presents_isLift | exact GlobalTheory.LiftSys.presents_isLift | (intros; apply GlobalTheory.LiftSys.presents_isLift <;> assumption)
end
end

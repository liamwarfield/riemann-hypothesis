module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ExistsLin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.OkDvr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CardResOK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtIdBC
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private lemma mem_basicOpen_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of O)) (a : O) (x : Y) :
    x ∈ Y.basicOpen (fn f a) ↔ a ∉ (f x).asIdeal := by
  have h1 : f ⁻¹ᵁ (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)
      = Y.basicOpen (fn f a) := Scheme.preimage_basicOpen_top f _
  rw [← h1, basicOpen_eq_of_affine]
  exact Iff.rfl

private lemma flat_h {O O' : Type} [CommRing O] [CommRing O'] (σ : O →+* O') (hσ : σ.Flat)
    {Y Y' : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of O)} {f' : Y' ⟶ Spec (CommRingCat.of O')} {h : Y' ⟶ Y}
    (hp : IsPullback h f' f (Spec.map (CommRingCat.ofHom σ))) : Flat h := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := Flat.SpecMap_iff.2 hσ
  exact MorphismProperty.of_isPullback hp.flip this

private lemma genPt_h {O O' : Type} [CommRing O] [CommRing O'] (σ : O →+* O') (hσ : σ.Flat) (ϖ : O) (ϖ' : O')
    (hr : ∀ P : Ideal O', P.IsPrime → (σ ϖ ∈ P ↔ ϖ' ∈ P))
    {Y Y' : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of O)} {f' : Y' ⟶ Spec (CommRingCat.of O')} {h : Y' ⟶ Y}
    (hp : IsPullback h f' f (Spec.map (CommRingCat.ofHom σ))) (x : Y') (hx : GenPt (fn f' ϖ') x) :
    GenPt (fn f ϖ) (h x) := by
  have key : ∀ w : Y', w ∈ Y'.basicOpen (fn f' ϖ') ↔ h w ∈ Y.basicOpen (fn f ϖ) := by
    intro w
    rw [mem_basicOpen_fn, mem_basicOpen_fn]
    have e : f (h w) = (Spec.map (CommRingCat.ofHom σ)) (f' w) := by
      have := congrArg (fun t => t w) (congrArg (fun t : Y' ⟶ _ => (t : Y' → _)) hp.w)
      simpa using this
    rw [e]
    have := hr (f' w).asIdeal (f' w).isPrime
    change ϖ' ∉ (f' w).asIdeal ↔ σ ϖ ∉ (f' w).asIdeal
    exact (not_congr this).symm
  have := flat_h σ hσ hp
  refine ⟨fun hb => hx.1 ((key x).2 hb), fun x' hx' hs => ?_⟩
  obtain ⟨w, hw, rfl⟩ := Flat.generalizingMap h hs
  have := hx.2 w (fun hb => hx' ((key w).1 hb)) hw
  rw [this]

private lemma twist_comp {κ : Type} [CommRing κ] (φ : κ →+* κ) {Y Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (x : Spec (CommRingCat.of κ) ⟶ Y') (m : ℕ) :
    (twist φ Y)^[m] (x ≫ h) = (twist φ Y')^[m] x ≫ h := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    simp only [twist, Category.assoc]

private lemma twist_base {κ : Type} [CommRing κ] (φ : κ →+* κ) {S Y' : Scheme.{0}} (f' : Y' ⟶ S)
    (β : Spec (CommRingCat.of κ) ⟶ S) (hβ : Spec.map (CommRingCat.ofHom φ) ≫ β = β)
    (x : Spec (CommRingCat.of κ) ⟶ Y') (hx : x ≫ f' = β) (m : ℕ) :
    (twist φ Y')^[m] x ≫ f' = β := by
  induction m generalizing x with
  | zero => exact hx
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    refine ih _ ?_
    simp only [twist, Category.assoc, hx, hβ]

private lemma beta_fix {O' V : Type} [CommRing O'] [CommRing V] [IsLocalRing V] (q : ℕ) (ϖ' : O')
    (hq : ∀ a : O', a ^ q - a ∈ Ideal.span {ϖ'})
    (φ : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField V) (hφ : ∀ a, φ a = a ^ q)
    (c : CommRingCat.of O' ⟶ CommRingCat.of V)
    (hc : ϖ' ∈ (IsLocalRing.maximalIdeal V).comap c.hom) :
    Spec.map (CommRingCat.ofHom φ) ≫ resPt V ≫ Spec.map c = resPt V ≫ Spec.map c := by
  rw [resPt, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  have h0 : IsLocalRing.residue V (c.hom ϖ') = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hc
  have h1 : IsLocalRing.residue V (c.hom (a ^ q - a)) = 0 := by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hq a)
    rw [← hb, map_mul, map_mul, h0, mul_zero]
  simp only [map_sub, map_pow, sub_eq_zero] at h1
  simpa [hφ] using h1

private lemma closed_mem {O' V : Type} [CommRing O'] [CommRing V] [IsLocalRing V] (ϖ' : O')
    {Y' : Scheme.{0}} (f' : Y' ⟶ Spec (CommRingCat.of O')) (y : Spec (CommRingCat.of V) ⟶ Y')
    (c : CommRingCat.of O' ⟶ CommRingCat.of V) (hc : y ≫ f' = Spec.map c)
    (hx : y (IsLocalRing.closedPoint V) ∉ Y'.basicOpen (fn f' ϖ')) :
    ϖ' ∈ (IsLocalRing.maximalIdeal V).comap c.hom := by
  rw [mem_basicOpen_fn, not_not] at hx
  have e : f' (y (IsLocalRing.closedPoint V)) = (Spec.map c) (IsLocalRing.closedPoint V) := by
    rw [← hc]; rfl
  rw [e] at hx
  exact hx

theorem UpperTheory.Gal.crystallineComparison.ptIdBC_of :
    PtIdBC := by
  classical
  intro l q n O O' _ _ σ hσ ϖ ϖ' hr hq Y Y' f f' h hp T T' g hg hrr hf hId V _ _ _ _ hl y hG φ hφ I _ z hz
  have hG' : GenPt (fn f ϖ) ((y ≫ h) (IsLocalRing.closedPoint V)) := genPt_h σ hσ ϖ ϖ' hr hp _ hG
  let z' : ∀ j, I j → (T j).Sec (y ≫ h) := fun j i => ⟨(z j i).1 ≫ g j, by
    rw [Category.assoc, ← (hg j).w, ← Category.assoc, (z j i).2]⟩
  have hz' : ∀ j, Function.Bijective (z' j) := by
    intro j
    constructor
    · intro i₁ i₂ e
      have e' : (z j i₁).1 ≫ g j = (z j i₂).1 ≫ g j := congrArg Subtype.val e
      refine (hz j).1 (Subtype.ext ((hg j).hom_ext ?_ e'))
      rw [(z j i₁).2, (z j i₂).2]
    · intro w
      obtain ⟨i, hi⟩ := (hz j).2 ⟨(hg j).lift y w.1 w.2.symm, (hg j).lift_fst _ _ _⟩
      refine ⟨i, Subtype.ext ?_⟩
      change (z j i).1 ≫ g j = w.1
      rw [hi]
      exact (hg j).lift_snd _ _ _
  have key := hId V hl (y ≫ h) hG' φ hφ I z' hz'
  let c : CommRingCat.of O' ⟶ CommRingCat.of V := Spec.preimage (y ≫ f')
  have hc : y ≫ f' = Spec.map c := (Spec.map_preimage _).symm
  have hmem := closed_mem ϖ' f' y c hc hG.1
  let β : Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Spec (CommRingCat.of O') := resPt V ≫ y ≫ f'
  have hβ : Spec.map (CommRingCat.ofHom φ) ≫ β = β := by
    simp only [β, hc]
    exact beta_fix q ϖ' hq φ hφ c hmem
  let Λ : (Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Y) → (Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Y') :=
    fun x => if hx : x ≫ f = β ≫ Spec.map (CommRingCat.ofHom σ) then hp.lift x β hx else resPt V ≫ y
  have hΛ : ∀ x' : Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Y', x' ≫ f' = β → Λ (x' ≫ h) = x' := by
    intro x' e
    have hx : (x' ≫ h) ≫ f = β ≫ Spec.map (CommRingCat.ofHom σ) := by
      rw [Category.assoc, hp.w, ← Category.assoc, e]
    simp only [Λ, dif_pos hx]
    apply hp.hom_ext
    · exact hp.lift_fst _ _ _
    · rw [hp.lift_snd, e]
  have hv : ∀ j i, (resPt V ≫ (z j i).1 ≫ (T' j).r) ≫ f' = β := by
    intro j i
    simp only [β, Category.assoc, hf j]
    rw [← Category.assoc (z j i).1, (z j i).2]
  have e1 : ∀ j i, resPt V ≫ (z' j i).1 ≫ (T j).r = (resPt V ≫ (z j i).1 ≫ (T' j).r) ≫ h := by
    intro j i
    change resPt V ≫ ((z j i).1 ≫ g j) ≫ (T j).r = _
    simp only [Category.assoc, hrr j]
  have hfin : ∀ (m : ℕ) j i, Λ ((twist φ Y)^[m] (resPt V ≫ (z' j i).1 ≫ (T j).r))
      = (twist φ Y')^[m] (resPt V ≫ (z j i).1 ≫ (T' j).r) := by
    intro m j i
    rw [e1, twist_comp]
    exact hΛ _ (twist_base φ f' β hβ _ (hv j i) m)
  unfold AltId at key ⊢
  have := congrArg (Multiset.map Λ) key
  rw [pts_map, pts_map] at this
  simpa only [hfin] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCorrPull
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

open CategoryTheory.Limits in
theorem UpperTheory.Gal.crystallineComparison.corrPull_of :
    CorrPull := by
  intro l S S' Y Y' u f f' h hY T hT
  have Q := IsPullback.of_hasPullback T.p h
  have hw : (pullback.fst T.p h ≫ T.r) ≫ f = (pullback.snd T.p h ≫ f') ≫ u := by
    rw [Category.assoc, hT, ← Category.assoc, pullback.condition, Category.assoc, hY.w,
      Category.assoc]
  have hfin : IsFinite (pullback.snd T.p h) := by
    have := T.fin
    exact MorphismProperty.of_isPullback Q this
  have het : Etale (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) := by
    have hle : Y'.basicOpen (l : Γ(Y', ⊤)) ≤ h ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) :=
      le_of_eq (by rw [Scheme.preimage_basicOpen_top, map_natCast])
    let k := Y'.homOfLE hle ≫ h ∣_ Y.basicOpen (l : Γ(Y, ⊤))
    have e1 : k ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι = (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ h := by
      simp only [k, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    have A := (isPullback_morphismRestrict (pullback.snd T.p h) (Y'.basicOpen (l : Γ(Y', ⊤)))).flip
    have outer := A.paste_horiz Q
    have R := (isPullback_morphismRestrict T.p (Y.basicOpen (l : Γ(Y, ⊤)))).flip
    have hw2 : ((pullback.snd T.p h ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ pullback.fst T.p h) ≫ T.p
        = (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤)) ≫ k) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      simp only [Category.assoc, pullback.condition, e1, morphismRestrict_ι_assoc]
    have outer' : IsPullback (R.lift _ _ hw2 ≫ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι)
        (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) T.p (k ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι) := by
      rw [R.lift_fst, e1]
      exact outer
    have L := IsPullback.of_right outer' (R.lift_snd _ _ _) R
    exact MorphismProperty.of_isPullback L T.et
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K], (l : K) ≠ 0 →
      ∀ (y : Spec (CommRingCat.of K) ⟶ Y'),
        Nat.card { z // z ≫ pullback.snd T.p h = y } = T.d := by
    intro K _ _ hl y
    rw [← T.deg K hl (y ≫ h)]
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1 ≫ pullback.fst T.p h, by rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]⟩
        invFun := fun z => ⟨Q.lift z.1 y z.2, Q.lift_snd _ _ _⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro z
      apply Subtype.ext
      apply Q.hom_ext
      · simp
      · simp [z.2]
    · intro z
      apply Subtype.ext
      simp
  refine ⟨⟨pullback T.p h, pullback.snd T.p h, hY.lift _ _ hw, T.d, hfin, het, hdeg⟩,
    pullback.fst T.p h, Q.flip, hY.lift_fst _ _ _, hY.lift_snd _ _ _, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FlatOfDvr
open CategoryTheory AlgebraicGeometry

private lemma flat_of_dvr {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
    (φ : O →+* O') (ϖ : O) (hϖ : Irreducible ϖ) (h0 : φ ϖ ≠ 0) : φ.Flat := by
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    rw [map_mul, map_pow] at ha
    rcases mul_eq_zero.1 ha with h | h
    · exact (u.isUnit.map φ).ne_zero h
    · exact pow_ne_zero k h0 h
  algebraize [φ]
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hinj
  have : Module.IsTorsionFree O O' := inferInstance
  exact (inferInstance : Module.Flat O O')

theorem UpperTheory.Ru.crystallineComparison.ptIdBC :
    UpperTheory.Ru.crystallineComparison.PtIdBC := by
  intro l q n O O' _ _ _ _ _ _ φ ϖ hϖ hϖ' hq Y Y' p p' g hpb T hT hId
  have hflat : φ.Flat := flat_of_dvr φ ϖ hϖ hϖ'.ne_zero
  choose T' κ h1 h2 h3 _ using fun j => UpperTheory.Gal.crystallineComparison.corrPull_of l _ _ Y Y' _ p p' g hpb (T j) (hT j)
  refine ⟨T', κ, fun j => ⟨(h1 j).flip, (h2 j).symm, h3 j⟩, ?_⟩
  exact UpperTheory.Gal.crystallineComparison.ptIdBC_of l q n O O' φ hflat ϖ (φ ϖ) (fun _ _ => Iff.rfl)
    (fun a => Ideal.mem_span_singleton.2 (hq a)) Y Y' p p' g hpb T T' κ h1 h2 h3 hId
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.Pst TensorProduct Module Matrix CrystallineSemistableComparison
open GlobalTheory.GalV (HTower)

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.Int.Geo UpperTheory.Gal.Seam

private theorem mem_OK_iff {l : ℕ} [Fact l.Prime] (K : FinExt l) (x : ↥K.1) : x ∈ OK l K.1 ↔ x ∈ OL K := by
  rw [OK_eq]; rfl

private def okEquiv {l : ℕ} [Fact l.Prime] (K : FinExt l) : ↥(OL K) ≃+* ↥(OK l K.1) where
  toFun b := ⟨b.1, (mem_OK_iff K b.1).2 b.2⟩
  invFun c := ⟨c.1, (mem_OK_iff K c.1).1 c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private theorem card_res_OK {l : ℕ} [Fact l.Prime] (K : FinExt l) [IsLocalRing ↥(OK l K.1)] :
    Nat.card (IsLocalRing.ResidueField ↥(OK l K.1)) = l ^ GlobalTheory.AinfK.fK K := by
  rw [← GlobalTheory.AinfK.card_res K]
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (okEquiv K)).toEquiv).symm

private theorem dvd_pow_sub {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {q : ℕ} (hq : q ≠ 0)
    (hc : Nat.card (IsLocalRing.ResidueField R) = q) {t : R} (ht : Irreducible t) (x : R) : t ∣ x ^ q - x := by
  have : Finite (IsLocalRing.ResidueField R) := Nat.finite_of_card_ne_zero (by rwa [hc])
  letI := Fintype.ofFinite (IsLocalRing.ResidueField R)
  have h := FiniteField.pow_card (IsLocalRing.residue R x)
  rw [← Nat.card_eq_fintype_card, hc] at h
  rw [← Ideal.mem_span_singleton, ← ht.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h, sub_self]

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.Int.Geo UpperTheory.Gal.Seam UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.congBC :
    UpperTheory.Ru.crystallineComparison.CongBC := by
  intro E Ω _ _ _ _ _ l _ L _ H θ w hl n ϑ hC A hA O _ _ _ Bw hB
  obtain ⟨C, p, f, hp, hpw, hN, hO, ϖ, T, γ, m, hϖ, hid, hT⟩ := hC
  have epl : p = l := by
    by_contra hne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp Fact.out).2 hne)
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      have h := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at h
      rw [← h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpw) (Ideal.mul_mem_left _ _ hl)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  subst epl
  have hNv : normV w = p ^ f := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hf : resDeg p w = f := by
    rw [resDeg, hNv, Nat.log_pow hp.one_lt]
  subst hf
  have hpos : 0 < resDeg p w := Nat.pos_of_ne_zero fun h0 =>
    w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 (by rw [hN, h0, pow_zero]))
  haveI := Bw.Kw.2
  obtain ⟨hD, hV, -⟩ := CrystallineSemistableComparison.Pb.Kap.ok_dvr_pf (l := p) (K := Bw.Kw.1)
  haveI := hD
  haveI := hV
  haveI : IsDiscreteValuationRing (Ow w) := (w.valuation E).valuationSubring_isDiscreteValuationRing
  obtain ⟨φ, hφ, hφi⟩ := UpperTheory.Gal.Seam.intMap E Ω p w A hA O Bw hB
  have hcard : Nat.card (IsLocalRing.ResidueField ↥(OK p Bw.Kw.1)) = p ^ resDeg p w := by
    rw [card_res_OK, GlobalTheory.AinfK.fK_eq_resDeg Bw hA hB]
  obtain ⟨C', u, hu, -, hOnto, -, hLies⟩ :=
    UpperTheory.Gal.Seam.bcCover E ↥Bw.Kw.1 (Ow w) ↥(OK p Bw.Kw.1) L (UpperTheory.Gal.Seam.kOf Bw) φ hφ H θ C
  have hirr := hφi ϖ hϖ
  obtain ⟨T', κ, hκ, hid'⟩ := UpperTheory.Ru.crystallineComparison.ptIdBC p (p ^ resDeg p w) n (Ow w) ↥(OK p Bw.Kw.1) φ ϖ hϖ hirr
    (dvd_pow_sub (pow_ne_zero _ hp.ne_zero) hcard hirr) C.Y C'.Y C.p C'.p u hu T (fun j => (hT j).1) hid
  refine ⟨hD, hV, hpos, hNv, hcard, C', hOnto hO, φ ϖ, T', γ, m, hirr, hid', fun j => ⟨(hκ j).2.2, ?_, (hT j).2.2⟩⟩
  exact hLies (γ j) (T j).Z (T j).p (T j).r (m j) (hT j).1 (hT j).2.1 (T' j).Z (κ j) (T' j).p (T' j).r (hκ j).1
    (hκ j).2.1.symm (hκ j).2.2
end
end

theorem UpperTheory.Gal.Int.Geo.geoSide_of :
    UpperTheory.Gal.crystallineComparison.Br.FinAll → CrystallineSemistableComparison.SmoothModelCrystalline → UpperTheory.Ru.crystallineComparison.GeoSide := by
  intro hFin hCr E Ω _ _ _ _ _ l _ H θ hN a ρ₀ hMat w hw n ϑ hCong P AI hT A hA O _ _ _ Bw hj
  obtain ⟨hD, hDV, hf, hnorm, hcard, C, hOnto, hCg⟩ :=
    UpperTheory.Ru.crystallineComparison.congBC E Ω l _ H θ w hw n ϑ hCong A hA O Bw hj
  obtain ⟨ρ₁, hM₁, hρ₁⟩ :=
    UpperTheory.Gal.Seam.locTower_holds l E ↥Bw.Kw.1 Ω _
      (UpperTheory.Gal.Seam.kOf Bw) Bw.j (fun _ => rfl) H hN _ θ a ρ₀ hMat
  obtain ⟨V, i₁, i₂, i₃, ρ, T, b, hcr, hann, hinj, hact, heig⟩ :=
    UpperTheory.Ru.crystallineComparison.geoLoc hFin hCr l P AI hT Bw.Kw _ hf hcard
      (UpperTheory.Gal.Int.Geo.bcAlong H (UpperTheory.Gal.Seam.kOf Bw)) θ
      (UpperTheory.Gal.Seam.niceBc _ _ (UpperTheory.Gal.Seam.kOf Bw) H hN) C hOnto n ϑ hCg a ρ₁ hM₁
  rw [hnorm]
  refine ⟨V, i₁, i₂, i₃, ρ, T, b, hcr, hann, hinj, fun g x => ?_, heig⟩
  have h := hact (Bw.e g) x
  rwa [hρ₁ (g : Ω ≃ₐ[E] Ω) _ fun y => Bw.e_comm g y] at h

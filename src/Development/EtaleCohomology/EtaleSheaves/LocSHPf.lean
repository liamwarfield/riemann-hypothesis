module

public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.EtaleCohomology.EtaleSheaves.SHTensorPf
public import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocSHPf
noncomputable section
open Polynomial IsLocalRing GlobalTheory.EtC

namespace LateralTheory.E.LocSHPf

theorem aic_localization (S : Type) [CommRing S] (hS : AIC S) (M : Submonoid S) (R : Type) [CommRing R]
    [Algebra S R] [IsLocalization M R] : AIC R := by
  intro P hP hd
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M ((Finset.range (P.natDegree + 1)).image P.coeff)
  set s : R := algebraMap S R (b : S) with hs
  have hlift : P.scaleRoots s ∈ lifts (algebraMap S R) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · obtain ⟨y, hy⟩ := hb (P.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      refine ⟨y * (b : S) ^ k, ?_⟩
      rw [map_mul, map_pow, hy, hk, pow_succ, Algebra.smul_def, ← hs]
      ring
    · subst hi
      rw [Nat.sub_self, pow_zero, mul_one]
      exact ⟨1, by rw [map_one]; exact hP.symm⟩
    · rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact ⟨0, map_zero _⟩
  have hmon : (P.scaleRoots s).Monic := by
    rw [Monic, leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]; exact hP
  obtain ⟨Q, hQ, hQd, hQm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  obtain ⟨a, ha⟩ := hS Q hQm (by rw [hQd, natDegree_scaleRoots]; exact hd)
  have hu : IsUnit s := IsLocalization.map_units R b
  refine ⟨hu.unit⁻¹ * algebraMap S R a, ?_⟩
  have h1 := scaleRoots_eval₂_mul (p := P) (RingHom.id R) (hu.unit⁻¹ * algebraMap S R a) s
  have h2 : s * (hu.unit⁻¹ * algebraMap S R a) = algebraMap S R a := by
    rw [← mul_assoc, hu.mul_val_inv, one_mul]
  rw [RingHom.id_apply, h2, ← eval, ← eval, ← hQ, eval_map, eval₂_hom, ha, map_zero] at h1
  have := (hu.pow P.natDegree).mul_right_eq_zero.1 h1.symm
  exact this

theorem root_near (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) (a₀ : R) :
    ∀ n : ℕ, ∀ f : R[X], f.natDegree = n → f.Monic → f.eval a₀ ∈ maximalIdeal R →
      ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  intro n
  induction n with
  | zero =>
    intro f hn hf he
    rw [eq_one_of_monic_natDegree_zero hf hn, eval_one] at he
    exact absurd he (Ideal.IsMaximal.ne_top inferInstance |> fun h => fun h1 => h ((Ideal.eq_top_iff_one _).2 h1))
  | succ n ih =>
    intro f hn hf he
    obtain ⟨a, ha⟩ := hR f hf (by omega)
    have hfac := (mul_divByMonic_eq_iff_isRoot (p := f) (a := a)).2 ha
    have hgm : (f /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hf)
    have hgd : (f /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at he
    rcases Ideal.IsPrime.mem_or_mem (inferInstance : (maximalIdeal R).IsPrime) he with h | h
    · refine ⟨a, ha, ?_⟩
      rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 h
    · obtain ⟨b, hb, hb'⟩ := ih _ hgd hgm h
      refine ⟨b, ?_, hb'⟩
      rw [← hfac, IsRoot, eval_mul, hb.eq_zero, mul_zero]

theorem henselian_of_aic (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) : HenselianLocalRing R where
  is_henselian f hf a₀ he _ := root_near R hR a₀ _ f rfl hf he

theorem residue_algClosed (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) : IsAlgClosed (ResidueField R) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hl : p ∈ lifts (residue R) := by
    rw [lifts_iff_coeff_lifts]; intro n; exact residue_surjective _
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hp
  have hpos : 0 < p.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)
  obtain ⟨a, ha⟩ := hR q hqm (by omega)
  exact ⟨residue R a, by rw [← hq, eval_map, eval₂_hom, ha, map_zero]⟩

theorem LocSH_of : LateralTheory.E.ZarLocalPf.LocSH := by
  intro S _ hS p
  have hA := aic_localization S hS p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  have := residue_algClosed _ hA
  exact ⟨henselian_of_aic _ hA, inferInstance⟩

end LateralTheory.E.LocSHPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IntHensPf
noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.IntHensPf

theorem mem_sub (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (m : Ideal A) (S : Subalgebra A B)
    {n : ℕ} (c : Fin n → B) (g : Fin n → (algebraMap A B '' (m : Set A))) (hc : ∀ i, c i ∈ S) :
    ∃ y ∈ m.map (algebraMap A S), (y : B) = ∑ i, c i • (g i : B) := by
  choose a ha hag using fun i => (g i).2
  refine ⟨∑ i, ⟨c i, hc i⟩ * algebraMap A S (a i), Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i)), ?_⟩
  change S.val _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, smul_eq_mul, ← hag]; rfl

theorem jac (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B] [Algebra.IsIntegral A B] :
    (maximalIdeal A).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro n ⟨-, hn⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (n.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal n
  exact le_of_eq (IsLocalRing.eq_maximalIdeal this).symm

theorem evalS (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Subalgebra A B) (p : S[X]) (y : S) :
    ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := by
  rw [eval_map]; exact (eval₂_hom S.val.toRingHom y).symm

theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Algebra A B]
    [Algebra.IsIntegral A B] : HenselianRing B ((maximalIdeal A).map (algebraMap A B)) := by
  classical
  refine ⟨by simpa only [Ideal.jacobson_bot] using jac A B, fun f hf a0 h0 h1 => ?_⟩
  set J := (maximalIdeal A).map (algebraMap A B) with hJ
  obtain ⟨n1, c1, g1, hs1⟩ := Submodule.mem_span_set'.1 h0
  obtain ⟨v, hv⟩ := h1.exists_left_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hu : u * f.derivative.eval a0 - 1 ∈ J := by
    rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
  obtain ⟨n2, c2, g2, hs2⟩ := Submodule.mem_span_set'.1 hu
  set s : Finset B := insert a0 (insert u (f.coeffs ∪ (Finset.univ.image c1 ∪ Finset.univ.image c2)))
  let S := Algebra.adjoin A (s : Set B)
  have hsS : ∀ x ∈ s, x ∈ S := fun x hx => Algebra.subset_adjoin hx
  haveI : Module.Finite A S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)
  let JS := (maximalIdeal A).map (algebraMap A S)
  haveI : HenselianRing S JS := GlobalTheory.henselianRing_of_finite A JS (GlobalTheory.map_maximalIdeal_le_jacobson_of_finite A S)
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc => hsS c (by simp [s, Finset.mem_coe.1 hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, hsS a0 (by simp [s])⟩
  let uS : S := ⟨u, hsS u (by simp [s])⟩
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  have h0S : g.eval b0 ∈ JS := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c1 g1 (fun i => hsS _ (by simp [s]))
    convert hy using 1
    apply Subtype.ext
    rw [hyv, hs1, evalS, hgf]
  have h1S : IsUnit (Ideal.Quotient.mk JS (g.derivative.eval b0)) := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c2 g2 (fun i => hsS _ (by simp [s]))
    have : uS * g.derivative.eval b0 - 1 ∈ JS := by
      convert hy using 1
      apply Subtype.ext
      rw [hyv, hs2]
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one, evalS]
      rw [← derivative_map, hgf]
    rw [← Ideal.Quotient.eq, map_mul, map_one] at this
    exact ⟨⟨_, _, (mul_comm _ _).trans this, this⟩, rfl⟩
  obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian g hgm b0 h0S h1S
  refine ⟨(a : B), ?_, ?_⟩
  · rw [IsRoot.def, ← hgf, ← evalS, ha.eq_zero]; rfl
  · have := Ideal.mem_map_of_mem S.val.toRingHom ha'
    rw [Ideal.map_map] at this
    simpa using this

theorem IntHens_of : LateralTheory.E.IntPBPf.IntHens := by
  intro A B _ _ _ φ hφ
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  exact hens A B

end LateralTheory.E.IntHensPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FreeCoprodPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.E.FreeCoprodPf

variable {ι : Type} (X : ι → Scheme.{0})

def P0 : PSh where
  obj U := Σ j, (unop U ⟶ X j)
  map {U V} h := ↾fun (s : Σ j, (unop U ⟶ X j)) => (⟨s.1, h.unop ≫ s.2⟩ : Σ j, (unop V ⟶ X j))
  map_id U := by ext s <;> simp
  map_comp f g := by ext s <;> simp

def inj (j : ι) : yoneda.obj (X j) ⟶ P0 X where
  app U := ↾fun f => (⟨j, f⟩ : Σ j, (unop U ⟶ X j))

def isColimitCofanSigmaOfRepresentablePresheaves : IsColimit (Cofan.mk (P0 X) (inj X)) :=
  Cofan.IsColimit.mk _
    (fun s => { app := fun U => ↾fun (x : Σ j, (unop U ⟶ X j)) => (s.inj x.1).app U x.2
                naturality := fun U V h => by
                  ext x
                  exact NatTrans.naturality_apply (s.inj x.1) h x.2 })
    (fun s j => by ext U f; rfl)
    (fun s m hm => by
      ext U ⟨j, f⟩
      exact ConcreteCategory.congr_hom (congr_app (hm j) U) f)

def φ : P0 X ⟶ yoneda.obj (∐ X) where
  app U := ↾fun (x : Σ j, (unop U ⟶ X j)) => x.2 ≫ Sigma.ι X x.1

lemma inj_φ (j : ι) : inj X j ≫ φ X = yoneda.map (Sigma.ι X j) := rfl

abbrev ψ := Functor.whiskerRight (φ X) uliftFunctor.{1}

instance : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (ψ X) where
  imageSieve_mem {U} s := by
    let 𝒰 := (sigmaOpenCover X).pullback₁ s.down
    apply Scheme.etaleTopology.superset_covering _
      (Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰))
    refine (Sieve.generate_le_iff _ _).2 ?_
    rintro _ _ ⟨i⟩
    refine ⟨⟨⟨i, pullback.snd _ _⟩⟩, ?_⟩
    apply ULift.ext
    exact (pullback.condition (f := s.down) (g := (sigmaOpenCover X).f i)).symm

instance : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (ψ X) where
  equalizerSieve_mem {U} x y h := by
    obtain ⟨⟨j, a⟩⟩ := x
    obtain ⟨⟨k, b⟩⟩ := y
    have h' : a ≫ Sigma.ι X j = b ≫ Sigma.ι X k := congrArg ULift.down h
    by_cases hjk : j = k
    · subst hjk
      obtain rfl := (cancel_mono (Sigma.ι X j)).1 h'
      refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.top_mem _)
      intro V g _
      simp [Presheaf.equalizerSieve]
    · have := isEmpty_of_commSq_sigmaι_of_ne ⟨h'⟩ hjk
      exact Scheme.etaleTopology.superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

variable (R : Type) [CommRing R]

instance : (ModuleCat.free (ULift.{1} R)).IsLeftAdjoint := ⟨_, ⟨ModuleCat.adj _⟩⟩

instance : PreservesColimitsOfShape (Discrete ι) (freeP R) := by
  unfold freeP; infer_instance

instance : PreservesColimitsOfShape (Discrete ι) (free R) := by
  unfold free; infer_instance

lemma isIso_free_φ : IsIso ((free R).map (φ X)) := by
  have h1 : Scheme.etaleTopology.W (ψ X) := GrothendieckTopology.W_of_isLocallyBijective _ _
  have h2 := Scheme.etaleTopology.W_of_preservesSheafification (ModuleCat.free (ULift.{1} R)) _ h1
  rw [GrothendieckTopology.W_iff] at h2
  exact h2

theorem FreeCoprod_of : LateralTheory.E.CoprodPf.FreeCoprod := by
  intro R _ ι X
  have := isIso_free_φ X R
  have h0 := isColimitCofanMkObjOfIsColimit (free R) _ _ (isColimitCofanSigmaOfRepresentablePresheaves X)
  refine ⟨IsColimit.ofIsoColimit h0 (Cofan.ext (asIso ((free R).map (φ X))) fun j => ?_)⟩
  show (free R).map (inj X j) ≫ (free R).map (φ X) = (free R).map (yoneda.map (Sigma.ι X j))
  rw [← Functor.map_comp, inj_φ]

end LateralTheory.E.FreeCoprodPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StdPBPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StandardPushout

variable {S : Type} [CommRing S] (f g : S)

def descR {T : Type} [CommRing T] (a : Localization.Away f →+* T) (b : Localization.Away g →+* T)
    (h : a.comp (algebraMap S _) = b.comp (algebraMap S _)) : Localization.Away (f * g) →+* T :=
  IsLocalization.Away.lift (f * g) (g := a.comp (algebraMap S _)) (by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    · exact (IsLocalization.Away.algebraMap_isUnit f).map a
    · rw [h]; exact (IsLocalization.Away.algebraMap_isUnit g).map b)

theorem descR_alg {T : Type} [CommRing T] (a : Localization.Away f →+* T) (b : Localization.Away g →+* T)
    (h : a.comp (algebraMap S _) = b.comp (algebraMap S _)) (s : S) :
    descR f g a b h (algebraMap S _ s) = a (algebraMap S _ s) :=
  IsLocalization.lift_eq _ _

theorem rL_alg (s : S) : LateralTheory.E.t_E1Cut.rL f g (algebraMap S _ s) = algebraMap S _ s :=
  IsLocalization.Away.awayToAwayRight_eq f g s

theorem rR_alg (s : S) : LateralTheory.E.t_E1Cut.rR f g (algebraMap S _ s) = algebraMap S _ s :=
  IsLocalization.Away.awayToAwayLeft_eq g f s

theorem isPushout_away :
    IsPushout (CommRingCat.ofHom (algebraMap S (Localization.Away f)))
      (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
      (CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rL f g)) (CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rR f g)) := by
  have hw : CommRingCat.ofHom (algebraMap S (Localization.Away f)) ≫ CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rL f g)
      = CommRingCat.ofHom (algebraMap S (Localization.Away g)) ≫ CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rR f g) := by
    ext x
    simp [rL_alg, rR_alg]
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw) ?_
  have hc : ∀ s : PushoutCocone (CommRingCat.ofHom (algebraMap S (Localization.Away f)))
      (CommRingCat.ofHom (algebraMap S (Localization.Away g))),
      s.inl.hom.comp (algebraMap S _) = s.inr.hom.comp (algebraMap S _) := fun s => by
    have := congrArg CommRingCat.Hom.hom s.condition
    simpa using this
  refine PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom (descR f g s.inl.hom s.inr.hom (hc s)))
    ?_ ?_ ?_
  · intro s
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp [rL_alg, descR_alg]
  · intro s
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext x
    have := congrArg (fun φ => φ x) (hc s)
    simp only [RingHom.comp_apply] at this
    simp [rR_alg, descR_alg, this]
  · intro s m h1 _
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (algebraMap S (Localization.Away f) x)) h1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, rL_alg] at this
    simp [descR_alg, this]

instance constPreserves (J : Type) [SmallCategory J] :
    PreservesLimitsOfShape J (SimplicialObject.const PSh) := by
  apply preservesLimitsOfShape_of_evaluation
  intro k
  exact preservesLimitsOfShape_of_natIso
    (NatIso.ofComponents (fun X => Iso.refl X) (by intros; rfl) :
      𝟭 PSh ≅ SimplicialObject.const PSh ⋙ (evaluation _ _).obj k)

instance schPreserves (J : Type) [SmallCategory J] : PreservesLimitsOfShape J sch := by
  unfold sch
  infer_instance

theorem isPullback_sp :
    IsPullback (spMap (LateralTheory.E.t_E1Cut.rL f g)) (spMap (LateralTheory.E.t_E1Cut.rR f g))
      (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_away f g)).map sch

end LateralTheory.E.StandardPushout

open LateralTheory.E.StandardPushout in
theorem LateralTheory.E.MVPf.StdPB_of : LateralTheory.E.MVPf.StdPB := by
  intro S _ f g
  have h := isPullback_sp f g
  exact ⟨h.isoPullback.hom, inferInstance, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafRepVanishPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRepVanishPf

variable (R : Type) [CommRing R]

theorem free_mono {P Q : PSh} (φ : P ⟶ Q) [Mono φ] : Mono ((free R).map φ) := by
  have : Mono ((freeP R).map φ) := by
    rw [NatTrans.mono_iff_mono_app]
    intro Y
    rw [ModuleCat.mono_iff_injective]
    have hi : Function.Injective (φ.app Y) := (mono_iff_injective _).1 inferInstance
    have hu : Function.Injective (uliftFunctor.{1}.map (φ.app Y)) := by
      intro a b h; exact ULift.ext (hi (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  unfold free
  simp only [Functor.comp_map]
  infer_instance

theorem chains_f (E E' : Spc) (f : E ⟶ E') (N : ℕ) :
    ((chains R).map f).f (-(N : ℤ)) = (chainsXIso R E N).hom ≫ (free R).map (f.app (op (SimplexCategory.mk N))) ≫ (chainsXIso R E' N).inv := by
  exact (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := N) rfl).trans rfl

theorem freeGen_nat {P Q : PSh} (φ : P ⟶ Q) (Y : Scheme.{0}) (x : P.obj (op Y)) :
    (((free R).map φ).hom.app (op Y)).hom (freeGen R P Y x) = freeGen R Q Y (φ.app _ x) := by
  have e := congrArg (fun t => (t.app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map φ))
  have e2 : (((freeP R).map φ).app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)) =
      ModuleCat.freeMk (ULift.up.{1} (φ.app _ x)) := ModuleCat.free_map_apply _ _
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  refine e.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op Y))) e2

theorem ev_pull {U E : Spc} (f : U ⟶ E) {K : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) K n) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y) :
    ev ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add n)) N w h Y y = ev γ N w h Y ((f.app _).app _ y) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, chains_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← freeGen_nat]
  rfl

theorem chains_mono {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) : Mono (((chains R).map f).f p) := by
  by_cases hp : p ≤ 0
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    rw [chains_f]
    have := free_mono R (f.app (op (SimplexCategory.mk N)))
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
        change -(i : ℤ) = p at hi; omega)
    exact ⟨fun a b _ => hz.eq_of_tgt a b⟩

theorem LeafRepVanish_of : LateralTheory.E.LeafA6suppPf.LeafRepVanish := by
  intro R _ U E f hf F n a ha
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  have hg := chains_mono R f
  have hinj : ∀ q, Injective ((res R F).X q) := fun q =>
    (inferInstance : Injective ((injectiveResolution F).cochainComplex.X q))
  have h1 : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 := ha
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h1
  obtain ⟨β', hβ'⟩ := h1
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.mk fun p q hpq => Injective.factorThru (β'.v p q hpq) (((chains R).map f).f p)
  have hβ : (Cochain.ofHom ((chains R).map f)).comp β (zero_add _) = β' := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    simp only [β, Cochain.mk_v]
    exact Injective.comp_factorThru _ _
  let b : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - b, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, (CohomologyClass.mk_eq_zero_iff b).2
      ((mem_coboundaries_iff b (n - 1) (by omega)).2 ⟨β, rfl⟩), sub_zero]
  · intro N w h Y y
    rw [← ev_pull]
    have e : (Cochain.ofHom ((chains R).map f)).comp (α - b).1 (zero_add n) = 0 := by
      rw [Cocycle.coe_sub, Cochain.comp_sub]
      have : (Cochain.ofHom ((chains R).map f)).comp (b : Cochain _ _ n) (zero_add n) = δ (n - 1) n β' := by
        rw [← hβ]; simp [b]
      rw [this, hβ']
      simp [zcomp]
    rw [e]
    simp [ev]

end LateralTheory.E.LeafRepVanishPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.OpenCovPtaPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.OpenCov_ptaPf

variable (R : Type) [CommRing R]

abbrev gen (P : PSh) {W : Scheme.{0}ᵒᵖ} (x : P.obj W) : ((freeP R).obj P).obj W :=
  ModuleCat.freeMk (X := uliftFunctor.{1}.obj (P.obj W)) (ULift.up x)

abbrev adj {P : PSh} {G : Shv R} (a : (free R).obj P ⟶ G) : (freeP R).obj P ⟶ G.obj :=
  toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ a.hom

theorem adj_inj {P : PSh} {G : Shv R} (a b : (free R).obj P ⟶ G) (h : adj R a = adj R b) : a = b := by
  ext1
  exact sheafify_hom_ext _ _ _ G.property h

theorem adj_comp {P Q : PSh} {G : Shv R} (φ : P ⟶ Q) (a : (free R).obj Q ⟶ G) :
    adj R ((free R).map φ ≫ a) = (freeP R).map φ ≫ adj R a := by
  show toSheafify _ _ ≫ (sheafifyMap _ ((freeP R).map φ) ≫ a.hom) = _
  show _ = (freeP R).map φ ≫ toSheafify _ _ ≫ a.hom
  erw [toSheafify_naturality_assoc]

theorem freePresheaf_obj_map_freeMk (P : PSh) {W W' : Scheme.{0}ᵒᵖ} (h : W ⟶ W') (x : P.obj W) :
    ((freeP R).obj P).map h (gen R P x) = gen R P (P.map h x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

theorem freePresheaf_map_freeMk {P Q : PSh} (φ : P ⟶ Q) (W : Scheme.{0}ᵒᵖ) (x : P.obj W) :
    ((freeP R).map φ).app W (gen R P x) = gen R Q (φ.app W x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

theorem adj_val {X Y : Scheme.{0}} {G : Shv R} (a : (free R).obj (yoneda.obj X) ⟶ G) (x : Y ⟶ X) :
    (adj R a).app (op Y) (gen R (yoneda.obj X) (W := op Y) x) =
      G.obj.map x.op ((adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X))) := by
  rw [← ConcreteCategory.comp_apply, ← (adj R a).naturality, ConcreteCategory.comp_apply, freePresheaf_obj_map_freeMk]
  simp

theorem ext_of_cover {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hcov : Set.range f ∪ Set.range g = Set.univ) {G : Shv R} (a b : (free R).obj (yoneda.obj X) ⟶ G)
    (hf : (free R).map (yoneda.map f) ≫ a = (free R).map (yoneda.map f) ≫ b)
    (hg : (free R).map (yoneda.map g) ≫ a = (free R).map (yoneda.map g) ≫ b) : a = b := by
  let Z : Bool → Scheme.{0} := fun i => Bool.rec V U i
  let φ : ∀ i, Z i ⟶ X := fun i => Bool.rec (motive := fun i => Z i ⟶ X) g f i
  have hS : Sieve.ofArrows Z φ ∈ Scheme.etaleTopology X := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => ?_⟩
    · have hx : x ∈ Set.range f ∪ Set.range g := hcov ▸ Set.mem_univ x
      rcases hx with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩
    · cases i <;> infer_instance
  have hf' := congrArg (adj R) hf
  have hg' := congrArg (adj R) hg
  rw [adj_comp, adj_comp] at hf' hg'
  have key : (adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) =
      (adj R b).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) := by
    refine Presheaf.IsSheaf.isSeparated G.property _ _ hS _ _ ?_
    intro Y' h hh
    obtain ⟨W, k, _, ⟨i⟩, rfl⟩ := hh
    rw [← adj_val, ← adj_val]
    cases i
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj V) (W := op _) k)) hg'
      simpa [freePresheaf_map_freeMk] using this
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj U) (W := op _) k)) hf'
      simpa [freePresheaf_map_freeMk] using this
  apply adj_inj
  ext Y : 2
  induction Y with | op Y => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact (adj_val R a x).trans ((congrArg _ key).trans (adj_val R b x).symm)

theorem openCov : LateralTheory.E.MayerVietorisSequence.OpenCov := by
  intro R _ U V X f g _ _ hcov
  have : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance
  have : sch.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  refine ⟨inferInstance, inferInstance, fun n => ⟨fun {G} a b h => ?_⟩⟩
  apply ext_of_cover R f g hcov a b
  · have h1 : (free R).map ((sch.map f).app n) ≫ a = (free R).map ((sch.map f).app n) ≫ b := by
      simpa using congrArg (biprod.inl ≫ ·) h
    exact h1
  · have h1 : (free R).map ((sch.map g).app n) ≫ a = (free R).map ((sch.map g).app n) ≫ b := by
      simpa using congrArg (biprod.inr ≫ ·) h
    exact h1

end LateralTheory.E.OpenCov_ptaPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ZCovPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

namespace LateralTheory.E.ZCovPf
set_option linter.style.haveILetI false

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hc : (e : R →+* S).comp e.symm.toRingHom = RingHom.id S := by ext x; simp
  have hq : p = (p.map e.symm.toRingHom).map (e : R →+* S) := by
    rw [Polynomial.map_map, hc, Polynomial.map_id]
  rw [hq, show e a = (e : R →+* S) a from rfl, Polynomial.eval_map_apply, ha, map_zero]

theorem good_of_affine {A : Type} [CommRing A] {Z W : Scheme.{0}} (hZ : AICSch Z) (j : W ⟶ Z) [IsOpenImmersion j]
    [IsAffine W] (p : Z ⟶ Spec (CommRingCat.of A)) : Good (j ≫ p) := by
  by_cases hW : IsEmpty W
  · exact Or.inl hW
  right
  obtain ⟨x⟩ : Nonempty W := not_isEmpty_iff.mp hW
  have hO : IsAffineOpen (j ''ᵁ ⊤) := (isAffineOpen_top W).image_of_isOpenImmersion j
  have hne : ((j ''ᵁ ⊤ : Z.Opens) : Set Z).Nonempty := ⟨j x, x, trivial, rfl⟩
  have hA : AIC Γ(W, ⊤) := aic_of_equiv (j.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ hO hne)
  haveI : IsIntegral Z := hZ.1
  haveI : Nonempty W := ⟨x⟩
  haveI : IsIntegral W := isIntegral_of_isOpenImmersion j
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨x, trivial⟩⟩
  let φ : A →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop).hom
  letI : Algebra A Γ(W, ⊤) := φ.toAlgebra
  refine ⟨Γ(W, ⊤), inferInstance, inferInstance, inferInstance, hA, W.isoSpec, ?_⟩
  have hφ : CommRingCat.ofHom (algebraMap A Γ(W, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop := rfl
  rw [hφ, Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

attribute [local instance] MvPolynomial.gradedAlgebra

def D (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

theorem D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_X ℤ i)) (hm := Nat.one_pos)

theorem D_inf : IsAffineOpen (D 0 ⊓ D 1) := by
  have h := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (MvPolynomial.X 0 * MvPolynomial.X 1) (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    ((MvPolynomial.isHomogeneous_X ℤ 0).mul (MvPolynomial.isHomogeneous_X ℤ 1))) (hm := Nat.two_pos)
  rw [Proj.basicOpen_mul] at h
  exact h

theorem D_cover : D 0 ⊔ D 1 = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ)) ?_
  · refine eq_top_iff.mpr (le_trans (le_of_eq h.symm) (iSup_le fun i => ?_))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · intro x hx
    have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx
    have hc : AddMonoidAlgebra.coeff x 0 = 0 := by
      rw [GradedRing.proj_apply] at h0
      have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) x) 0 : MvPolynomial (Fin 2) ℤ) =
          MvPolynomial.homogeneousComponent 0 x := MvPolynomial.decomposition.decompose'_apply x 0
      rw [e] at h0
      have := congrArg (AddMonoidAlgebra.coeff · 0) h0
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero] at this
      simpa using this
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hne
    push Not at hne
    have hm0 : m = 0 := Finsupp.ext fun i => hne i trivial
    subst hm0
    exact (MvPolynomial.mem_support_iff.mp hm) hc

theorem projectiveLine_integers_affine_cover_absolutely_integrally_closed : ZCov := by
  intro A _ Z p hp hZ
  obtain ⟨L, u, l, hu, ⟨-, f0, hpb⟩, rfl⟩ := hp
  have hf0 : IsAffineHom f0 :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  let φ : Z ⟶ P1 := u ≫ f0
  let U : Z.Opens := φ ⁻¹ᵁ D 0
  let V : Z.Opens := φ ⁻¹ᵁ D 1
  have hU : IsAffineOpen U := (D_affine 0).preimage φ
  have hV : IsAffineOpen V := (D_affine 1).preimage φ
  have hUV : IsAffineOpen (U ⊓ V) := D_inf.preimage φ
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  haveI : IsAffine (U ⊓ V : Z.Opens) := hUV
  haveI : IsAffine (pullback U.ι V.ι) := IsAffine.of_isIso (isPullback_opens_inf U V).isoPullback.inv
  refine ⟨U, V, U.ι, V.ι, inferInstance, inferInstance, ?_, good_of_affine hZ U.ι _, good_of_affine hZ V.ι _, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have h := congrArg (fun O : P1.Opens => ((φ ⁻¹ᵁ O : Z.Opens) : Set Z)) D_cover
    simpa [U, V] using h
  · rw [← Category.assoc]
    exact good_of_affine hZ (pullback.fst U.ι V.ι ≫ U.ι) _

end LateralTheory.E.ZCovPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GlueOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.Gluing₂

theorem orth {S : Type} [CommRing S] : ∀ (n : ℕ) (ε : Fin n → S), (∀ j, IsIdempotentElem (ε j)) →
    ∃ ε' : Fin n → S, OrthogonalIdempotents ε' ∧ (∀ j, ∃ c, ε' j = ε j * c) ∧
      ∑ j, ε' j = 1 - ∏ j, (1 - ε j) := by
  intro n
  induction n with
  | zero => intro ε _; exact ⟨fun _ => 0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, by simp⟩
  | succ n ih =>
    intro ε hε
    obtain ⟨ε₀, ho, hd, hs⟩ := ih (fun j => ε j.succ) (fun j => hε j.succ)
    have ha : IsIdempotentElem (ε 0) := hε 0
    have ha' : IsIdempotentElem (1 - ε 0) := ha.one_sub
    refine ⟨Fin.cons (ε 0) (fun j => (1 - ε 0) * ε₀ j), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simp only [Fin.cons_succ]
        exact ha'.mul (ho.idem j)
    · intro i k hik
      induction i using Fin.cases with
      | zero =>
        induction k using Fin.cases with
        | zero => exact absurd rfl hik
        | succ k =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
      | succ i =>
        induction k using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm, ← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
        | succ k =>
          simp only [Fin.cons_succ]
          have hik' : i ≠ k := fun h => hik (by rw [h])
          calc (1 - ε 0) * ε₀ i * ((1 - ε 0) * ε₀ k) = ((1 - ε 0) * (1 - ε 0)) * (ε₀ i * ε₀ k) := by ring
            _ = 0 := by rw [ho.ortho hik', mul_zero]
    · intro i
      refine Fin.cases ⟨1, by simp⟩ (fun j => ?_) i
      obtain ⟨c, hc⟩ := hd j
      exact ⟨(1 - ε 0) * c, by simp only [Fin.cons_succ, hc]; ring⟩
    · rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Finset.mul_sum, hs]
      ring

theorem glue : LateralTheory.E.FinEtSectionPf.Glue := by
  intro S C _ _ _ n e he hsurj ε hε hr hh
  obtain ⟨ε', ho, hd, hs⟩ := orth n ε hε

  have hf0 : ∏ j, (1 - ε j) = 0 := by
    have hidem : IsIdempotentElem (∏ j, (1 - ε j)) := by
      have := ho.isIdempotentElem_sum (s := Finset.univ).one_sub
      rwa [hs, sub_sub_cancel] at this
    refine hidem.eq_zero_of_isNilpotent ((nilpotent_iff_mem_prime).2 fun J hJ => ?_)
    obtain ⟨q, hq⟩ := hsurj ⟨J, hJ⟩
    have : ∃ j, e j ∉ q.asIdeal := by
      by_contra hall
      push_neg at hall
      exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (he.complete ▸ Ideal.sum_mem _ fun j _ => hall j))
    obtain ⟨j, hj⟩ := this
    have hq' : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away (e j)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (e j)) (e j)]; exact hj
    obtain ⟨q', rfl⟩ := hq'
    have hmem : (⟨J, hJ⟩ : PrimeSpectrum S) ∈ (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S)) := by
      rw [← hr j]; exact ⟨q', by rw [PrimeSpectrum.comap_comp_apply, hq]⟩
    have hεj : ε j ∉ J := hmem
    have h1 : 1 - ε j ∈ J := by
      have : ε j * (1 - ε j) ∈ J := by rw [mul_sub, mul_one, (hε j).eq, sub_self]; exact J.zero_mem
      exact (hJ.mem_or_mem this).resolve_left hεj
    exact J.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => 1 - ε i) (Finset.mem_univ j)) h1
  have hco : CompleteOrthogonalIdempotents ε' := ⟨ho, by rw [hs, hf0, sub_zero]⟩
  choose h hh using hh
  choose c hc using hd
  have hunit : ∀ j, IsUnit (Ideal.Quotient.mk (Ideal.span {1 - ε' j}) (ε j)) := by
    intro j
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ (c j), ?_⟩
    rw [← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_mul, ← hc j, ← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_one, Ideal.Quotient.eq]
    have hm := (Ideal.span {1 - ε' j}).neg_mem (Ideal.mem_span_singleton_self (1 - ε' j))
    rwa [neg_sub] at hm
  let L : ∀ j, Localization.Away (ε j) →+* S ⧸ Ideal.span {1 - ε' j} :=
    fun j => IsLocalization.Away.lift (ε j) (hunit j)
  let Φ : C →+* (∀ j, S ⧸ Ideal.span {1 - ε' j}) :=
    RingHom.pi fun j => ((L j).comp (h j)).comp (algebraMap C (Localization.Away (e j)))
  let E := RingEquiv.ofBijective _ hco.bijective_pi
  have hΦ : ∀ s : S, Φ (algebraMap S C s) = E s := by
    intro s
    funext j
    have := congrArg (fun g => L j (g s)) (hh j)
    simp only [RingHom.comp_apply] at this
    show L j (h j (algebraMap C _ (algebraMap S C s))) = Ideal.Quotient.mk _ s
    rw [this]
    exact IsLocalization.Away.lift_eq (ε j) (hunit j) s
  refine ⟨{ E.symm.toRingHom.comp Φ with commutes' := fun s => ?_ }⟩
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, hΦ]
  simp

theorem Glue_of (_hL : LateralTheory.E.t_E1Cut.EtLift) (_hA : LateralTheory.E.t_E1Cut.EtAIC) : LateralTheory.E.FinEtSectionPf.Glue := glue

end LateralTheory.E.Gluing₂
end
end

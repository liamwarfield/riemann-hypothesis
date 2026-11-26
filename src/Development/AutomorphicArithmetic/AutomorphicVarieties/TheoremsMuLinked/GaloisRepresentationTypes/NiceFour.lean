module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.RedBChiComap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.H4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RegCoset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DataEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DirGPowOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CountNormInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GaloisRepIneqOfAllIrreducibleNonvanishing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExModel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocBase
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.NumsZero

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.NiceFour
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CharpolyCompNegRoots
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem charpoly_neg {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    (-M).charpoly = (-1) ^ n * M.charpoly.comp (-X) := by
  have h : (M.charmatrix).map (Polynomial.compRingHom (-X : R[X])) = -(-M).charmatrix := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [charmatrix_apply_eq]
      ring
    · simp [charmatrix_apply_ne _ _ _ hij]
  have h2 : M.charpoly.comp (-X) = (-1) ^ n * (-M).charpoly := by
    rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det, RingHom.mapMatrix_apply, h,
      det_neg, Fintype.card_fin]
    rfl
  rw [h2, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

private theorem charpoly_comp_neg_roots {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) :
    (-1 : R[X]) ^ n * (∏ i, (X - C (a i))).comp (-X) = ∏ i, (X - C (-a i)) := by
  rw [Polynomial.prod_comp, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [sub_comp, X_comp, C_comp, map_neg]
  ring

theorem UpperTheory.V.Th.Det.perm4 :
    ∀ (K k B G : Type) [Field K] [Field k] [CommRing B] [Group G] (n : ℕ) (r : G →* GL (Fin n) K) (j : B →+* K) (φ : B →+* k) (χ : Fin n → G →* kˣ) (η : G →* ℤˣ), Function.Injective j → Pr.RedTo r j φ χ → (∀ g, (W.mat r g).charpoly = ((((η g : ℤˣ) : ℤ) : K) • W.mat r g).charpoly) → ∀ i, ∃ i', W.pushCh (Int.castRingHom k) η * χ i = χ i' := by
  intro K k B G _ _ _ _ n r j φ χ η hj hred hsym
  let χ' : Fin n → G →* kˣ := fun i => W.pushCh (Int.castRingHom k) η * χ i
  have hval : ∀ g i, (((χ' i) g : kˣ) : k) = (((η g : ℤˣ) : ℤ) : k) * ((χ i g : kˣ) : k) := by
    intro g i
    simp [χ', W.pushCh]
  have key : ∀ g, Pr.chPoly χ g = Pr.chPoly χ' g := by
    intro g
    rcases Int.units_eq_one_or (η g) with h | h
    · unfold Pr.chPoly
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hval g i, h]
      simp
    · obtain ⟨p, hp1, hp2⟩ := hred g
      have hp1' : Polynomial.map j p = (W.mat r g).charpoly := hp1
      have hM : (W.mat r g).charpoly = (-1) ^ n * (W.mat r g).charpoly.comp (-X) := by
        rw [← charpoly_neg, hsym g, h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
          neg_one_smul]
      have hp : p = (-1) ^ n * p.comp (-X) := by
        apply Polynomial.map_injective j hj
        rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
          Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, hp1']
        exact hM
      have hq := congrArg (Polynomial.map φ) hp
      rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
        Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, hp2] at hq
      rw [hq]
      unfold Pr.chPoly
      rw [charpoly_comp_neg_roots (fun i => (((χ i) g : kˣ) : k))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hval g i, h]
      simp
  obtain ⟨σ, hσ⟩ := Pr.charPerm G k n χ χ' key
  intro i
  exact ⟨σ i, hσ i⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AdDown
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem avg {Γ k M : Type} [Group Γ] [Field k] [CharZero k] [AddCommGroup M] [Module k M] (R : Representation k Γ M)
    (H : Subgroup Γ) [H.FiniteIndex] (c : Γ → M) (hc : ∀ g h, c (g * h) = c g + R g (c h)) (X : M)
    (hX : ∀ h ∈ H, c h = R h X - X) : ∃ Y, ∀ g, c g = R g Y - Y := by
  classical
  haveI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let d : Γ → M := fun g => c g - (R g X - X)
  have hd : ∀ g h, d (g * h) = d g + R g (d h) := fun g h => by
    simp only [d, hc, map_mul, map_sub, Module.End.mul_apply]
    abel
  have hd0 : ∀ g, ∀ h ∈ H, d (g * h) = d g := fun g h hh => by
    have : d h = 0 := by simp only [d, hX h hh, sub_self]
    rw [hd, this, map_zero, add_zero]
  let e : Γ ⧸ H → M := fun q => d q.out
  have he : ∀ g : Γ, e (g : Γ ⧸ H) = d g := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    show d _ = d g
    rw [hh, hd0 _ _ h.2]
  have hs : ∀ g : Γ, ∑ q, e q = (Fintype.card (Γ ⧸ H) : k) • d g + R g (∑ q, e q) := fun g => by
    have h1 : ∀ q : Γ ⧸ H, e (g • q) = d g + R g (e q) := fun q => by
      induction q using QuotientGroup.induction_on with
      | H a => rw [MulAction.Quotient.smul_mk, he, he, smul_eq_mul, hd]
    conv_lhs => rw [← Equiv.sum_comp (MulAction.toPerm g) e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [MulAction.toPerm_apply, h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum,
      Nat.cast_smul_eq_nsmul]
  have hn : (Fintype.card (Γ ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨X - (Fintype.card (Γ ⧸ H) : k)⁻¹ • ∑ q, e q, fun g => ?_⟩
  have h2 : d g = (Fintype.card (Γ ⧸ H) : k)⁻¹ • (∑ q, e q - R g (∑ q, e q)) := by
    rw [sub_eq_of_eq_add (hs g), smul_smul, inv_mul_cancel₀ hn, one_smul]
  have h3 : c g = d g + (R g X - X) := by simp only [d, sub_add_cancel]
  rw [h3, h2, map_sub, map_smul, smul_sub]
  abel

private theorem cc_eq {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] (c : Ω → Ω) (j : Ω →+* ℂ)
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) (x : K) :
    c (algebraMap K Ω x) = algebraMap K Ω (IsCMField.complexConj K x) := by
  apply j.injective
  rw [h]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K Ω)) x).symm

private theorem zero_NS {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] [T2Space V]
    {ρ : Representation C (G F Ω) V} {c : G F Ω → V} (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → w ∈ S)
    (hρ : ∀ s ∈ NS Ω S, ρ s = 1) : ∀ s ∈ NS Ω S, c s = 0 := by
  have c1 : c 1 = 0 := by
    have := hc.2 1 1
    simpa using this
  let N : Subgroup (G F Ω) :=
    { carrier := {s | s ∈ NS Ω S ∧ c s = 0}
      one_mem' := ⟨one_mem _, c1⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hc.2, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => by
        have h1 := hc.2 a a⁻¹
        rw [mul_inv_cancel, c1, hρ a ha.1, ha.2, zero_add] at h1
        exact ⟨inv_mem ha.1, h1.symm⟩ }
  haveI : N.Normal := ⟨fun a ha g => by
    refine ⟨(inferInstance : (NS Ω S).Normal).conj_mem a ha.1 g, ?_⟩
    have h1 := hc.2 g g⁻¹
    rw [mul_inv_cancel, c1] at h1
    rw [hc.2, hc.2, map_mul, hρ a ha.1, ha.2, mul_one, map_zero, add_zero, ← h1]⟩
  have hcl : IsClosed (N : Set (G F Ω)) := (isClosed_NS Ω S).inter (isClosed_eq hc.1 continuous_const)
  have hin : ∀ w, w ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := F) A, s ∈ NS Ω S := by
    intro w hw A hA s hs
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
    simp only [Set.mem_iUnion]
    exact ⟨w, hw, A, hA, hs⟩
  have hN : NS Ω S ≤ N := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun s hs => ?_) hcl
    simp only [Set.mem_iUnion] at hs
    obtain ⟨w, hw, A, hA, hs⟩ := hs
    obtain ⟨A₀, hA₀, x, hx⟩ := hb.away w fun h => hw (hS w h)
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA₀ hA
    have hs' : s ∈ Ine (F := F) A := hs
    rw [← hg] at hs'
    have ht := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hs'
    have hm := hin w hw A₀ hA₀ _ ht
    have h1 : g⁻¹ * s * g ∈ N := ⟨hm, by rw [hx _ ht, hρ _ hm, Module.End.one_apply, sub_self]⟩
    have h2 := (inferInstance : N.Normal).conj_mem _ h1 g
    have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    rwa [e] at h2
  exact fun s hs => (hN hs).2

theorem UpperTheory.V.Th.adDown :
    AdDown := by
  intro Ω _ _ _ l _ K L _ _ _ _ _ _ _ _ _ _ hLK s V n r μ R _ hR ρ ka h1 h2 hz c hc hb
  obtain ⟨c0, P, ⟨j, hj⟩, hP, hRK, hRc⟩ := hR
  obtain ⟨j', hj'⟩ := s.hc
  obtain ⟨hc', hb'⟩ := X.Kato.bkRes l (W.Lp L) Ω _ _ R c hc hb
  have he : ∀ g, V.frame.eps ℤ_[l] (Qbar l) (V.pr g) = cycBar L Ω l g := by
    intro g
    have : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := DFunLike.congr_fun V.hε _
    ext
    show algebraMap ℤ_[l] (Qbar l) (V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]) = _
    rw [this]
    rfl
  have hK : ∀ σ ∈ Base.galOf ℚ K Ω, ∃ t, Base.galEmb ℚ K Ω t = σ := fun σ h => by
    rwa [← Base.range_galEmb] at h
  have hc0 : ∀ x : K, c0⁻¹ (algebraMap K Ω x) = algebraMap K Ω (IsCMField.complexConj K x) := fun x => by
    refine c0.symm_apply_eq.2 ?_
    rw [cc_eq c0 j hj, IsCMField.complexConj_apply_apply]
  obtain ⟨w, hw⟩ := hK (Base.galEmb ℚ (W.Lp L) Ω s.c * c0⁻¹) fun x => by
    rw [AlgEquiv.mul_apply, hc0, Base.galEmb_apply, cc_eq s.c j' hj', IsCMField.complexConj_apply_apply]
  have hconj : ∀ t : G K Ω, ∃ t', Base.galEmb ℚ K Ω t' = c0 * Base.galEmb ℚ K Ω t * c0⁻¹ := fun t => hK _ fun x => by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc0, Base.galEmb_apply, t.commutes, cc_eq c0 j hj,
      IsCMField.complexConj_apply_apply]
  have hT : ∀ g : G L Ω, ∃ t, Base.galEmb ℚ L Ω g = Base.galEmb ℚ K Ω t := fun g =>
    (hK _ (hLK (Base.galEmb_mem ℚ L Ω g))).imp fun _ h => h.symm
  have hpr : ∀ x : V.frame.G₀, ∃ g, V.pr g = x := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g, rfl⟩ := (V.hη y).1 hx
    exact ⟨g, rfl⟩
  have had : ∀ (g : G L Ω) X, R (Base.galEmb ℚ L Ω g) X = Loc.adGL ρ (V.pr g) X := fun g X => by
    obtain ⟨t, ht⟩ := hT g
    have a1 : (ρ (V.pr g)).val = (ka g).val • (r t).val := h1 g t ht
    have a2 : (ρ (V.pr g)⁻¹).val = (ka g⁻¹).val • (r t⁻¹).val :=
      map_inv V.pr g ▸ h1 g⁻¹ t⁻¹ (by rw [map_inv, map_inv, ht])
    rw [map_inv ka, map_inv r, show ρ (V.pr g)⁻¹ = (ρ (V.pr g))⁻¹ from map_inv ρ (V.pr g)] at a2
    rw [ht]
    refine (hRK t X).trans ?_
    show _ = (ρ (V.pr g)).val * X * ((ρ (V.pr g))⁻¹).val
    rw [a1, a2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul]
  have hN : ∀ x ∈ NS Ω V.S', R (Base.galEmb ℚ (W.Lp L) Ω x) = 1 := fun x hx => by
    have e : toGS Ω V.S' x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    obtain ⟨g, rfl⟩ := (V.hη x).1 (by rw [e, map_one])
    have e' : V.pr g = 1 := Subtype.ext e
    refine LinearMap.ext fun X => (had g X).trans ?_
    rw [e']
    exact LinearMap.congr_fun (map_one (Loc.adGL ρ)) X
  have hN' := zero_NS hc' hb' V.S' (fun v hv => V.sub (Or.inl hv)) hN
  let R' : Representation (Qbar l) V.frame.Γ (Matrix (Fin n) (Fin n) (Qbar l)) :=
    QuotientGroup.lift (NS Ω V.S') (R.comp (Base.galEmb ℚ (W.Lp L) Ω)) hN
  let z : V.frame.Γ → Matrix (Fin n) (Fin n) (Qbar l) := fun q =>
    Quotient.liftOn' q (fun x => c (Base.galEmb ℚ (W.Lp L) Ω x)) fun a b hab => by
      have h := QuotientGroup.leftRel_apply.1 hab
      have h' := hc'.2 a (a⁻¹ * b)
      have h0 := hN' _ h
      beta_reduce at h' h0
      rw [mul_inv_cancel_left, h0, map_zero, add_zero] at h'
      exact h'.symm
  have hz1 : z ∈ Z1 R' := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨hc'.1.quotient_liftOn' _, fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hc'.2 a b
  have hform : V.frame.IsForm ℤ_[l] n ρ (P * (r w)⁻¹) := by
    intro x
    obtain ⟨g, rfl⟩ := hpr x
    obtain ⟨g', hg'⟩ := (V.hη (s.c * W.resP L Ω g * s.c⁻¹)).1 (V.frame.conj (V.pr g)).2
    have e : V.frame.conj (V.pr g) = V.pr g' := Subtype.ext (by
      show _ = toGS Ω V.S' (W.resP L Ω g')
      rw [hg', map_mul, map_mul, map_inv]
      rfl)
    obtain ⟨t, ht⟩ := hT g
    obtain ⟨t', ht'⟩ := hconj t
    have e2 : Base.galEmb ℚ L Ω g' = Base.galEmb ℚ K Ω (w * t' * w⁻¹) := by
      show Base.galEmb ℚ (W.Lp L) Ω (W.resP L Ω g') = _
      rw [hg', map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hw, ht', ← ht]
      show _ * Base.galEmb ℚ L Ω g * _ = _
      group
    have e3 : (P * (r w)⁻¹).val * W.mat r (w * t' * w⁻¹) = P.val * (r t').val * ((r w)⁻¹).val := by
      show _ * (r (w * t' * w⁻¹)).val = _
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, map_mul, map_mul, map_inv]
      congr 1
      group
    have e4 : (W.mat r t).transpose * P.val * (r t').val = (μ t).val • P.val := hP t t' ht'
    rw [e, h1 g t ht, h1 g' _ e2, he, ← h2 g g' t hg' ht, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e4, Matrix.smul_mul,
      smul_smul, smul_smul, Units.val_mul, Units.val_mul, Units.val_mul]
  have hext : Ws.Eb.IsAdExt V.frame ρ (P * (r w)⁻¹) R' := by
    refine ⟨fun x X => ?_, fun X => ?_⟩
    · obtain ⟨g, rfl⟩ := hpr x
      exact had g X
    · show R (Base.galEmb ℚ (W.Lp L) Ω s.c) X = _
      rw [mul_inv_eq_iff_eq_mul.1 hw.symm, map_mul, Module.End.mul_apply, hRc]
      refine (hRK w _).trans ?_
      simp only [mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  obtain ⟨X, hX⟩ := hz _ R' hform hext z hz1 hb'
  haveI : (Base.galOf ℚ (W.Lp L) Ω).FiniteIndex :=
    ⟨by rw [(Base.galEmbTop ℚ (W.Lp L) Ω).2.2]; exact Module.finrank_pos.ne'⟩
  refine (mem_coboundaries1 _ _).2 (avg R (Base.galOf ℚ (W.Lp L) Ω) c hc.2 X fun h hh => ?_)
  rw [← Base.range_galEmb] at hh
  obtain ⟨x, rfl⟩ := hh
  exact hX (toGS Ω V.S' x)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.NiceSmall
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.IrrSmall
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) : (Pr.gm r s).charpoly = Pr.chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (Pr.gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

private theorem root_eq {k : Type} [Field k] {n : ℕ} (x y : Fin n → k) (c : k) (hy : ∀ i, y i = c)
    (h : ∏ i, (X - C (x i)) = ∏ i, (X - C (y i))) (a : Fin n) : x a = c := by
  have h3 := congrArg (Polynomial.eval (x a)) h
  rw [Polynomial.eval_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero (f := fun i => Polynomial.eval (x a) (X - C (x i))) (Finset.mem_univ a) (by simp),
    eq_comm, Finset.prod_eq_zero_iff] at h3
  obtain ⟨i, _, h4⟩ := h3
  rw [← hy i]
  simpa [sub_eq_zero] using h4

theorem UpperTheory.V.Th.Det.irrSmall :
    ∀ {K k B G D : Type} [Field K] [IsAlgClosed K] [Field k] [CommRing B] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [Group D] {n : ℕ}, n.Prime → ∀ (G' : Subgroup G) [G'.Normal] (ρ : G →* GL (Fin n) K) (j : B →+* K) (φ : B →+* k) (χ : Fin n → G →* kˣ) (ι : D →* G) (ψ : Fin n → D →* Kˣ) (ψb : Fin n → D →* kˣ), U3.MatIrr ⊤ (W.mat ρ) → Function.Injective j → Pr.RedTo ρ j φ χ → W.HasFlag (ρ.comp ι) ψ → (∀ i g, ∃ a : B, j a = (ψ i g : K) ∧ φ a = (ψb i g : k)) → (∃ g, ι g ∈ G' ∧ Pr.FreeRatios fun i => ψ i g) → (∃ a b g, ψb a g ≠ ψb b g) → ∀ U : Subgroup G, IsOpen (U : Set G) → U3.MatIrr (U ⊓ G') (W.mat ρ) := by
  intro K k B G D _ _ _ _ _ _ _ _ _ n hn G' _ ρ j φ χ ι ψ ψb hirr hj hred hflag hlift hfree hne U hU
  classical
  have hfi : U.FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen U hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hch : ∀ g, (Pr.gm ρ (ι g)).charpoly = Pr.chPoly ψ g := fun g => charpoly_flag _ _ hflag g
  have key := Pr.irrNormal G K k B n hn ρ hirr j φ χ hj hred D ι ψ hch (U.normalCore ⊓ G') (fun a b hab => ?_) ?_
  · intro W hW
    exact key W fun g hg => hW g ⟨U.normalCore_le hg.1, hg.2⟩
  · obtain ⟨g, hg, hfr⟩ := hfree
    have hpos : 0 < U.normalCore.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    refine ⟨g ^ U.normalCore.index, ?_, ?_⟩
    · rw [map_pow]
      exact ⟨U.normalCore.pow_index_mem _, G'.pow_mem hg _⟩
    · rw [map_pow, map_pow]
      exact hfr a b hab _ hpos
  · obtain ⟨a, b, g, hab⟩ := hne
    by_contra hcon
    push Not at hcon
    apply hab
    choose c hc1 hc2 using fun i => hlift i g
    obtain ⟨p, hp1, hp2⟩ := hred (ι g)
    have hp : p = ∏ i, (X - C (c i)) := by
      apply Polynomial.map_injective j hj
      rw [hp1, hch, Pr.chPoly, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc1]
    rw [hp, Pr.chPoly, Polynomial.map_prod] at hp2
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc2] at hp2
    have h := root_eq (fun i => ((ψb i g : kˣ) : k)) (fun i => ((χ i (ι g) : kˣ) : k)) (χ a (ι g) : kˣ)
      (fun i => by rw [hcon i a g]) hp2
    exact Units.ext ((h a).trans (h b).symm)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CharpolyPow
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolyPowersRatios
noncomputable def UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios :
    {κ ι : Type} → [inst : Field κ] → (ι → κˣ) → Prop :=
    fun {κ ι : Type} [Field κ] (α : ι → κˣ) ↦ ∀ (i j : ι), i ≠ j → ∀ (m : ℕ), (0 : ℕ) < m → α i ^ m ≠ α j ^ m

theorem UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ),
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (↑(a i) : K)) →
        UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios a →
          ∀ (d : ℕ),
            (0 : ℕ) < d →
              (M ^ d).charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) ((↑(a i) : K) ^ d)) := by
  intro K _ n M a hM hfree d _
  have hinj : Function.Injective (fun i => (a i : K)) := by
    intro i j hij
    by_contra hne
    exact hfree i j hne 1 one_pos (by simpa using Units.ext hij)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i : K) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ (fun i => (a i : K)) hinj v hv
  let b : Module.Basis (Fin n) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' v hli _
  have hpow : ∀ j, Matrix.toLin' (M ^ d) (v j) = ((a j : K) ^ d) • v j := by
    intro j
    rw [Matrix.toLin'_pow]
    exact (hv j).pow_apply d
  have hmat : LinearMap.toMatrix b b (Matrix.toLin' (M ^ d)) =
      Matrix.diagonal (fun i => (a i : K) ^ d) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, hpow, map_smul, ← hb]
    simp only [Module.Basis.repr_self, Matrix.diagonal_apply, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul, mul_one]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, hmat, Matrix.charpoly_diagonal]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Det

open UpperTheory.V.U3 UpperTheory.V.Pr

private lemma open_basis {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (O : Set G) (hO : IsOpen O) (h1 : (1 : G) ∈ O) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ (V : Set G) ⊆ O := by
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  exact ⟨H.toSubgroup, H.isOpen', hH⟩

private lemma strong_of {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {m : ℕ} (G' V : Subgroup G) (hV : IsOpen (V : Set G))
    (r : G →* GL (Fin m) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r)) :
    StrongIrr (r.comp (V ⊓ G').subtype) := by
  refine strongIrrOfOpen _ κ m _ (fun f => (hc f).preimage continuous_subtype_val) ?_
  intro U hU W hW
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ O := by
    have : (1 : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := U.one_mem
    rw [← hOU] at this
    exact this
  obtain ⟨V', hV', hsub⟩ := open_basis (O ∩ V) (hO.inter hV) ⟨h1, V.one_mem⟩
  refine hirr V' hV' W fun g hg => ?_
  have h2 := hsub hg.1
  have h3 : (⟨g, h2.2, hg.2⟩ : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := by
    rw [← hOU]; exact h2.1
  exact hW _ h3

private lemma coset_in {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (U : Set G) (hU : IsOpen U) (s : G) (hs : s ∈ U) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ h ∈ V, s * h ∈ U := by
  obtain ⟨V, hV, hsub⟩ := open_basis ((fun h => s * h) ⁻¹' U) (hU.preimage (continuous_const.mul continuous_id))
    (by simpa using hs)
  exact ⟨V, hV, fun h hh => hsub hh⟩

private lemma cosetI {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {n : ℕ} (hn : n ≤ 3) (G' : Subgroup G)
    (r : G →* GL (Fin n) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r))
    (hsep : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ u ∈ U ⊓ G', ∃ α : Fin n → κˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)))
    (U : Set G) (hU : IsOpen U) (hne : (U ∩ (G' : Set G)).Nonempty) :
    ∃ σ ∈ U ∩ (G' : Set G), (gm r σ).charpoly.Separable := by
  obtain ⟨s, hs, hs'⟩ := hne
  obtain ⟨V, hV, hsV⟩ := coset_in U hU s hs
  obtain ⟨u, hu, α, hα, hch⟩ := hsep V hV
  obtain ⟨h, hh⟩ := regCoset _ κ n hn _ (strong_of G' V hV r hc hirr) ⟨u, hu⟩ α hα hch (r s)
  refine ⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩
  simp only [gm, map_mul, Units.val_mul]
  exact hh

private lemma charpoly_pow {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ)
    (hM : M.charpoly = ∏ i, (X - C (a i : K))) (ha : FreeRatios a) (d : ℕ) (hd : 0 < d) :
    (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d)) :=
  _root_.UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow M a hM ha d hd

end UpperTheory.V.Th.Det

theorem UpperTheory.V.Th.Det.n3small :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {n : ℕ}, n ≤ 3 → ∀ (G' : Subgroup G) (ρ : G →* GL (Fin n) (Qbar l)), Continuous ρ → (∀ U : Subgroup G, IsOpen (U : Set G) → U3.MatIrr (U ⊓ G') (W.mat ρ)) → (∃ u ∈ G', ∃ α : Fin n → (Qbar l)ˣ, Pr.FreeRatios α ∧ (W.mat ρ u).charpoly = ∏ i, (X - C ((α i : (Qbar l)ˣ) : Qbar l))) → ∀ U : Set G, IsOpen U → (U ∩ (G' : Set G)).Nonempty → ∃ σ ∈ U ∩ (G' : Set G), (W.mat ρ σ).charpoly.Separable := by
  intro l _ G _ _ _ _ _ n hn G' ρ hρ hirr ⟨u, hu, α, hα, hch⟩ U hU hne
  have hc : Pr.LinClosed (Pr.gm ρ) := by
    intro f
    have h1 : Continuous (Pr.gm ρ) := Units.continuous_val.comp hρ
    have h2 : Continuous fun g => f (Pr.gm ρ g) := by
      have e : (fun g => f (Pr.gm ρ g)) = fun g => ∑ i, ∑ j, Pr.gm ρ g i j * f (Matrix.single i j 1) := by
        funext g
        conv_lhs => rw [Matrix.matrix_eq_sum_single (Pr.gm ρ g)]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
      rw [e]
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      exact (h1.matrix_elem i j).mul continuous_const
    exact isClosed_eq h2 continuous_const
  refine cosetI hn G' ρ hc hirr ?_ U hU hne
  intro V hV
  haveI : Finite (G ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨d, hd, -, hdV⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := V)) u
  refine ⟨u ^ d, ⟨hdV, G'.pow_mem hu d⟩, fun i => α i ^ d, ?_, ?_⟩
  · intro i j hij m hm
    simp only [← pow_mul]
    exact hα i j hij _ (Nat.mul_pos hd hm)
  · have := charpoly_pow _ α hch hα d hd
    rw [← map_pow] at this
    simp only [Units.val_pow_eq_pow_val]
    exact this
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem charpoly_flag' {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) : (Pr.gm r s).charpoly = Pr.chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (Pr.gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

theorem UpperTheory.V.Th.nice0small :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r} (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), (n = 2 ∨ n = 3) → Th.APt ι x ρ → U3.MatIrr ⊤ (W.mat ρ) → Th.Free V.frame (fun v => x.psi v) → (∃ v a b g, r.psib v a g ≠ r.psib v b g) → Th.NiceAPt ι x ρ := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B ι x ρ hn hA hirr hfree ⟨v, hne⟩
  have hp : n.Prime := by
    rcases hn with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  have h3 : n ≤ 3 := by omega
  obtain ⟨-, A, _, j, φ, hj, hred, hlift⟩ := Th.Det.redB x ρ hA.rep
  haveI : V.frame.G'.Normal := MonoidHom.normal_ker _
  haveI : CompactSpace V.frame.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ V.frame.η_open).isCompact
  have key := Th.Det.irrSmall hp V.frame.G' ρ j φ r.chib (V.frame.φ v) (x.psi v) (r.psib v) hirr hj hred
    (hA.flag v) (hlift v) (hfree v) hne
  refine ⟨hA, hfree, ?_, ?_⟩
  · have h := key ⊤ (by simp)
    rwa [top_inf_eq] at h
  · obtain ⟨g, hg, hfr⟩ := hfree v
    exact Th.Det.n3small h3 V.frame.G' ρ hA.cont key
      ⟨V.frame.φ v g, hg, fun i => x.psi v i g, hfr, charpoly_flag' _ _ (hA.flag v) g⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ConductorAtMapInjectiveCoeff

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th

section Transfer

variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')

end Transfer

end

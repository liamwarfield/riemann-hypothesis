module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.RecFunctA
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

section general

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def smulBil (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] : V →ₗ[R] R →ₗ[R] V :=
  (LinearMap.lsmul R V).flip

noncomputable def smulPairing (M : TRep ℤ G) [DiscreteTopology M.V] : Pairing M (trivRep G ℤ) M where
  β := @smulBil ℤ M.V _ _ M.mod
  cont := continuous_of_discreteTopology
  equiv g m n := (@LinearMap.map_smul ℤ M.V M.V _ _ _ M.mod M.mod (M.rho g) (show ℤ from n) m).symm

theorem smulPairing_apply (M : TRep ℤ G) [DiscreteTopology M.V] (x : M.V) (n : ℤ) :
    (smulPairing M).β x n = n • x := int_smul_eq_zsmul M.mod n x

theorem exists_int_cocycle (t : G → ℚ) (m : (Fin 2 → G) → ℤ) (ht : IsLocallyConstant t)
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (y : (trivRep G ℤ).coch.X 2), (trivRep G ℤ).coch.d 2 y = 0 ∧ ∀ g, y.1 g = m g := by
  obtain ⟨z, hz, hzm⟩ := exists_defect_cocycle (trivRep G ℤ) (a := (1 : ℤ)) (fun _ => rfl) ht hm
  exact ⟨z, hz, fun g => (hzm g).trans (mul_one (m g))⟩

theorem cupFun_zero_two {M N P : TRep ℤ G} (b : Pairing M N P) (f : (Fin 0 → G) → M.V) (f' : (Fin 2 → G) → N.V)
    (g : Fin (0 + 2) → G) : cupFun b 0 2 f f' g = b.β (f ![]) (f' g) := by
  unfold cupFun
  rw [show (fun i : Fin 0 => g (Fin.castAdd 2 i)) = ![] from Subsingleton.elim _ _,
    show (fun j : Fin 2 => g (Fin.natAdd 0 j)) = g from funext fun j => congrArg g (Fin.ext (by simp))]
  simp

theorem trep_dn_zero {R : Type} [CommRing R] (M : TRep R G) (f : (Fin 0 → G) → M.V) (v : Fin 1 → G) :
    ReciprocityTheory.Gal.dn M.rho 0 f v = M.rho (v 0) (f ![]) - f ![] :=
  LowDeg.dn_zero_apply M.rho f v

theorem cor_smul_cocycle (M : TRep ℤ G) [DiscreteTopology M.V] (U : Subgroup G) [U.FiniteIndex]
    (hU : IsOpen (U : Set G)) (cor : Cx.Hom (M.resSub U).coch M.coch) (hcor : IsCor M U cor)
    (x : M.V) (hx : ∀ g ∈ U, M.rho g x = x) (x' : M.V) (hx' : corFun M U 0 (fun _ => x) ![] = x')
    (y : (trivRep G ℤ).coch.X 2) (hy : (trivRep G ℤ).coch.d 2 y = 0)
    (zU : (M.resSub U).coch.X 2) (hzU : (M.resSub U).coch.d 2 zU = 0)
    (hzU1 : ∀ g, zU.1 g = (show ℤ from y.1 fun i => (g i : G)) • x)
    (z : M.coch.X 2) (hz : M.coch.d 2 z = 0) (hz1 : ∀ g, z.1 g = (show ℤ from y.1 g) • x') :
    cor.H 2 ((M.resSub U).coch.cls 2 zU hzU) = M.coch.cls 2 z hz := by
  let bP := smulPairing M
  let bU : Pairing (M.resSub U) ((trivRep G ℤ).resSub U) (M.resSub U) :=
    ⟨bP.β, bP.cont, fun g m n => bP.equiv g.1 m n⟩
  let x0 : (M.resSub U).coch.X 0 := ⟨fun _ => x, continuous_const⟩
  have hx0 : (M.resSub U).coch.d 0 x0 = 0 := by
    refine Subtype.ext (funext fun g => ?_)
    refine (trep_dn_zero (M.resSub U) x0.1 g).trans ?_
    show M.rho (g 0).1 x - x = 0
    rw [hx _ (g 0).2, sub_self]
  have hry : ((trivRep G ℤ).resSub U).coch.d 2
      ((Pair.res (trivRep G ℤ) U.subtype continuous_subtype_val).hom.f 2 y) = 0 := Cx.Hom.d_f_eq_zero _ hy
  have hcx : M.coch.d 0 (cor.f 0 x0) = 0 := Cx.Hom.d_f_eq_zero _ hx0
  have key : cor.H (0 + 2) (cupCoh bU 0 2 ((M.resSub U).coch.cls 0 x0 hx0)
      (((trivRep G ℤ).resSub U).coch.cls 2 _ hry)) =
      cupCoh bP 0 2 (M.coch.cls 0 (cor.f 0 x0) hcx) ((trivRep G ℤ).coch.cls 2 y hy) :=
    cupCor_holds ℤ G M (trivRep G ℤ) M U bP bU (cupCoh bP) (cupCoh bU) cor cor hU rfl (cupCoh_isCup bP)
      (cupCoh_isCup bU) hcor hcor 0 2 ((M.resSub U).coch.cls 0 x0 hx0) ((trivRep G ℤ).coch.cls 2 y hy)
  obtain ⟨zU', hzU', hzU1', hzU2'⟩ := cupCoh_isCup bU 0 2 x0 _ hx0 hry
  obtain ⟨w, hw, hw1, hw2⟩ := cupCoh_isCup bP 0 2 (cor.f 0 x0) y hcx hy
  rw [hzU2', hw2] at key
  have e1 : zU' = zU := by
    refine Subtype.ext (funext fun g => ?_)
    rw [hzU1', cupFun_zero_two]
    exact (smulPairing_apply M x _).trans (hzU1 g).symm
  have e2 : w = z := by
    refine Subtype.ext (funext fun g => ?_)
    rw [hw1, cupFun_zero_two, hcor, hx']
    exact (smulPairing_apply M x' _).trans (hz1 g).symm
  subst e1 e2
  exact key

end general

theorem corFun_zero_eq_normHom (hL : FiniteDimensional ℚ_[p] L) (y : KbarMult p) (hy : y ∈ multOf p L)
    (f : (Fin 0 → subG p K L) → (kbarT p K).V) (hf : ∀ g, f g = y) (g : Fin 0 → GK p K) :
    corFun (kbarT p K) (subG p K L) 0 f g = normHom p K L y := by
  have := finite_GalLK (p := p) (K := K) hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  rw [normHom_apply, ← finsum_eq_sum_of_fintype,
    ← finsum_comp_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel (subG p K L))]
  unfold corFun
  simp only [hf]
  refine finsum_congr fun c => ?_
  have h1 : QuotientGroup.quotientRightRelEquivQuotientLeftRel (subG p K L) c =
      (QuotientGroup.mk (c.out⁻¹) : GK p K ⧸ subG p K L) := by
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [h1, kbarRep_out y hy]
  rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem qz_div (n : ℕ) (hn : 0 < n) (q : QZ) : ∃ q' : QZ, n • q' = q := by
  induction q using QuotientAddGroup.induction_on with
  | H r =>
    refine ⟨QuotientAddGroup.mk (r / n), ?_⟩
    rw [← QuotientAddGroup.mk_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    field_simp

theorem restriction_brauer_surjective (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : Surjective ((resPair h).hom.H 2) := by
  intro y
  obtain ⟨q', hq'⟩ := qz_div (degLK p K L) (degLK_pos hL) (invBr p L y)
  obtain ⟨x, rfl⟩ := (invBr_bijective hK).2 q'
  exact ⟨x, (invBr_bijective hL).1 ((invBr_res hK hL h x).trans hq')⟩

theorem invBr_cor (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (cor : Br p L →+ Br p K)
    (hcor : ∀ x, cor ((resPair h).hom.H 2 x) = degLK p K L • x) (y : Br p L) :
    invBr p K (cor y) = invBr p L y := by
  obtain ⟨x, rfl⟩ := restriction_brauer_surjective hK hL h y
  rw [hcor, map_nsmul, invBr_res hK hL h]

theorem exists_cor_pairBr (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    ∃ cor : Br p L →+ Br p K, (∀ x, cor ((resPair h).hom.H 2 x) = degLK p K L • x) ∧
      ∀ (b : Lˣ) (a : Kˣ), ofK p K (Additive.ofMul a) = normHom p K L (ofK p L (Additive.ofMul b)) →
        ∀ χ : charGrp (GK p K), cor (pairBr p L b (resChar h χ)) = pairBr p K a χ := by
  have := finiteIndex_subG (K := K) hL
  have hU := isOpen_subG (K := K) hL
  obtain ⟨e, he, hc, hc'⟩ := exists_equiv_subG h
  have hes : ∀ g : subG p K L, resGK h (e.symm g) = g.1 := fun g => by
    rw [← he, MulEquiv.apply_symm_apply]
  let PLU : Pair (kbarT p L) ((kbarT p K).resSub (subG p K L)) :=
    { φ := e.symm.toMonoidHom
      u := LinearMap.id
      φ_cont := hc'
      u_cont := continuous_id
      equiv := fun g m => by
        show kbarRep p K (resGK h (e.symm g)) m = kbarRep p K g.1 m
        rw [hes] }
  obtain ⟨corP, hcorP, hcr⟩ := cor_holds ℤ (GK p K) (kbarT p K) (subG p K L) hU
  refine ⟨(corP.H 2).toAddMonoidHom.comp (PLU.hom.H 2).toAddMonoidHom, fun x => ?_, fun b a ha χ => ?_⟩
  · show corP.H 2 (PLU.hom.H 2 ((resPair h).hom.H 2 x)) = _
    have h1 : PLU.hom.H 2 ((resPair h).hom.H 2 x) =
        (Pair.res (kbarT p K) (subG p K L).subtype continuous_subtype_val).hom.H 2 x := by
      induction x using Cx.H_ind with
      | h x hx =>
        refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
        show x.1 (fun i => resGK h (e.symm (g i))) = x.1 fun i => (g i).1
        simp only [hes]
    rw [h1, hcr]; rfl
  · show corP.H 2 (PLU.hom.H 2 (pairBr p L b (resChar h χ))) = _
    obtain ⟨t, m, z, hz, ht, htχ, hm, hzm, hcl⟩ := isPairClass_pairBr a χ
    obtain ⟨y, hy, hym⟩ := exists_int_cocycle t m ht hm
    have hm' : ∀ g : Fin 2 → GK p L, ((m fun i => resGK h (g i) : ℤ) : ℚ) =
        t (resGK h (g 0)) + t (resGK h (g 1)) - t (resGK h (g 0 * g 1)) := fun g => by
      rw [hm, map_mul]
    obtain ⟨zL, hzL, hzL1⟩ := exists_defect_cocycle (kbarT p L) (a := ofK p L (Additive.ofMul b))
      (fun g => kbarT_rho_ofK g _) (t := fun g => t (resGK h g)) (ht.comp_continuous (resGK_continuous h))
      (m := fun g => m fun i => resGK h (g i)) hm'
    have hpL : pairBr p L b (resChar h χ) = (kbarT p L).coch.cls 2 zL hzL :=
      (isPairClass_pairBr b (resChar h χ)).unique
        ⟨_, _, zL, hzL, ht.comp_continuous (resGK_continuous h), fun g => htχ _, hm', hzL1, rfl⟩
    rw [hpL, hcl]
    refine cor_smul_cocycle (kbarT p K) (subG p K L) hU corP hcorP (ofK p L (Additive.ofMul b))
      (fun g hg => (mem_multOf_iff_fixed h _).1 (ofK_mem p L _) g hg) (ofK p K (Additive.ofMul a))
      ((corFun_zero_eq_normHom hL _ (ofK_mem p L _) _ (fun _ => rfl) _).trans ha.symm) y hy
      (PLU.hom.f 2 zL) (Cx.Hom.d_f_eq_zero _ hzL) (fun g => ?_) z hz (fun g => ?_)
    · show zL.1 (fun i => e.symm (g i)) = _
      rw [hzL1, hym]
      simp only [hes]
      rfl
    · rw [hzm, hym]

theorem pairK_norm (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (b : Lˣ) (a : Kˣ)
    (ha : ofK p K (Additive.ofMul a) = normHom p K L (ofK p L (Additive.ofMul b))) (χ : charGrp (GK p K)) :
    pairK p K a χ = pairK p L b (resChar h χ) := by
  obtain ⟨cor, hcor, hpr⟩ := exists_cor_pairBr hK hL h
  unfold pairK
  rw [← hpr b a ha χ, invBr_cor hK hL h cor hcor]

noncomputable def conjL (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) : GK p L →* GK p L where
  toFun g :=
    { (σ.toRingEquiv.trans (g.toRingEquiv.trans σ.symm.toRingEquiv)) with
      commutes' := fun x => by
        show σ.symm (g (σ x.1)) = x.1
        rw [show g (σ x.1) = σ x.1 from g.commutes ⟨σ x.1, hσ x.1 x.2⟩, AlgEquiv.symm_apply_apply] }
  map_one' := AlgEquiv.ext fun x => σ.symm_apply_apply x
  map_mul' g g' := AlgEquiv.ext fun x => by
    show σ.symm (g (g' (σ x))) = σ.symm (g (σ (σ.symm (g' (σ x)))))
    rw [AlgEquiv.apply_symm_apply]

theorem resGK_conjL (h : K ≤ L) (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) (g : GK p L) :
    resGK h (conjL σ hσ g) = σ⁻¹ * resGK h g * σ := rfl

theorem conjL_continuous (h : K ≤ L) (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) : Continuous (conjL σ hσ) := by
  rw [(isClosedEmbedding_resGK h).isInducing.continuous_iff]
  exact (continuous_const.mul (resGK_continuous h)).mul continuous_const

noncomputable def conjPairL (h : K ≤ L) (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) : Pair (kbarT p L) (kbarT p L) where
  φ := conjL σ hσ
  u := kbarRep p K σ
  φ_cont := conjL_continuous h σ hσ
  u_cont := continuous_of_discreteTopology
  equiv _ _ := Units.ext (σ.apply_symm_apply _)

noncomputable def innPair (σ : GK p K) : Pair (kbarT p K) (kbarT p K) where
  φ := (MulAut.conj σ⁻¹).toMonoidHom
  u := kbarRep p K σ
  φ_cont := (continuous_const.mul continuous_id).mul continuous_const
  u_cont := continuous_of_discreteTopology
  equiv _ _ := Units.ext (σ.apply_symm_apply _)

theorem conjPairL_res (h : K ≤ L) (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) (n : ℕ) (x : (kbarT p K).H n) :
    (conjPairL h σ hσ).hom.H n ((resPair h).hom.H n x) = (resPair h).hom.H n x := by
  have h1 : (innPair σ).hom.H n = LinearMap.id :=
    inner_holds ℤ (GK p K) (kbarT p K) (innPair σ) σ (fun g => by simp [innPair]) (fun _ => rfl) n
  have h2 : (conjPairL h σ hσ).hom.H n ((resPair h).hom.H n x) =
      (resPair h).hom.H n ((innPair σ).hom.H n x) := by
    induction x using Cx.H_ind with
    | h x hx => rfl
  rw [h2, h1]; rfl

theorem conjugation_pairing_h2_fixed (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (σ : GK p K)
    (hσ : ∀ x ∈ L, σ x ∈ L) (y : Br p L) : (conjPairL h σ hσ).hom.H 2 y = y := by
  obtain ⟨x, rfl⟩ := restriction_brauer_surjective hK hL h y
  exact conjPairL_res h σ hσ 2 x

theorem pairBr_conj (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (σ : GK p K)
    (hσ : ∀ x ∈ L, σ x ∈ L) (b b' : Lˣ)
    (hb : ((b' : L) : PadicAlgCl p) = σ ((b : L) : PadicAlgCl p)) (χ χ' : charGrp (GK p L))
    (hχ : ∀ g g' : GK p L, resGK h g' = σ * resGK h g * σ⁻¹ →
      χ'.1 (Additive.ofMul g') = χ.1 (Additive.ofMul g)) :
    pairBr p L b' χ' = pairBr p L b χ := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzm, hc⟩ := isPairClass_pairBr b χ
  rw [← conjugation_pairing_h2_fixed hK hL h σ hσ (pairBr p L b χ)]
  refine (isPairClass_pairBr b' χ').unique ?_
  have hbb : ofK p L (Additive.ofMul b') = kbarRep p K σ (ofK p L (Additive.ofMul b)) := Units.ext hb
  refine ⟨fun g => t (conjL σ hσ g), fun g => m fun i => conjL σ hσ (g i), (conjPairL h σ hσ).hom.f 2 z,
    by rw [← (conjPairL h σ hσ).hom.comm, hz, map_zero],
    ht.comp_continuous (conjL_continuous h σ hσ), fun g => ?_, fun g => ?_, fun g => ?_, by rw [hc]; rfl⟩
  · rw [htχ]
    refine (hχ _ _ ?_).symm
    rw [resGK_conjL]; group
  · rw [hm]; simp only [map_mul]
  · show kbarRep p K σ (z.1 fun i => conjL σ hσ (g i)) = _
    rw [hzm, hbb]
    exact LinearMap.map_smul (kbarRep p K σ) _ _

theorem pairK_conj (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (σ : GK p K)
    (hσ : ∀ x ∈ L, σ x ∈ L) (b b' : Lˣ)
    (hb : ((b' : L) : PadicAlgCl p) = σ ((b : L) : PadicAlgCl p)) (χ χ' : charGrp (GK p L))
    (hχ : ∀ g g' : GK p L, resGK h g' = σ * resGK h g * σ⁻¹ →
      χ'.1 (Additive.ofMul g') = χ.1 (Additive.ofMul g)) :
    pairK p L b' χ' = pairK p L b χ := by
  unfold pairK
  rw [pairBr_conj hK hL h σ hσ b b' hb χ χ' hχ]

end ReciprocityTheory.DiscreteGroups.LocalClassField

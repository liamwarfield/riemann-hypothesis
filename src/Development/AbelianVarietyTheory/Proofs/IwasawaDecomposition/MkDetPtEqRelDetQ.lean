module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MkDetPtEqRelDetQ
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.Mem.Chr hiding ordF
open Neutral.B1 hiding Ideles
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.Mem.Chr.RelDet GlobalTheory.Mem.Chr.IdlFact
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetLat

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem ordSub_conj {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ P) (detSub N) = -ordSub P (detSub N) := by
  have hfr (w : HeightOneSpectrum (𝓞 E)) : IsFr w N (latFr w N) := by
    first | exact isFr_latFr w ⟨hN, hu⟩ | exact isFr_latFr w hN
  have hfull : Submodule.IsFullLattice E N := by
    letI : Submodule.IsLattice E N := hN
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (latFr P N)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hfr P _).2 (CharValCompare.single_mem_stdAt P i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ P.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • (latFr P N) (Pi.single i 1) ∈ N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  have h := CharValCompare.val_dual (P := P) ⟨hN, hu⟩ (hfr P) (hfr (conjPrime₂ P))
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq hfull (hfr P), ordSub_detSub_eq hfull (hfr (conjPrime₂ P))]
  unfold ordF
  rw [eq_inv_of_mul_eq_one_right h, WithZero.log_inv]

theorem ordSub_std (w : HeightOneSpectrum (𝓞 E)) : ordSub w (detSub (stdLat E n)) = 0 := by
  have hfull : Submodule.IsFullLattice E (stdLat E n) := by
    letI : Submodule.IsLattice E (stdLat E n) := stdLat_lattice
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map ((1 : Sp E n ≃ₗ[E] Sp E n))).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 (((show IsFr w (stdLat E n) 1 from fun _ => Iff.rfl) _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • ((1 : Sp E n ≃ₗ[E] Sp E n)) (Pi.single i 1) ∈ (stdLat E n) := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E ((stdLat E n) : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  rw [ordSub_detSub_eq (f := 1) hfull fun _ => Iff.rfl]
  simp [ordF]


open Classical in
theorem ordI_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    {fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n} (hf : ∀ P, IsFr P N (fr P)) (w : HeightOneSpectrum (𝓞 E)) :
    ordI w (detIdl SB N fr) =
      if w ∈ SB then ordSub w (detSub N) else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub N)).toNat : ℤ) := by
  have hfull : Submodule.IsFullLattice E N := by
    letI : Submodule.IsLattice E N := hN
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (fr w)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hf w _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • (fr w) (Pi.single i 1) ∈ N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  have e : valAt w (detIdl SB N fr) = Valued.v (compAt w (detIdl SB N fr)) := valAt_apply _ _
  rw [ordI, e, compAt_detIdl SB hN]
  split_ifs
  · rw [valued_algebraMap, ordSub_detSub_eq hfull (hf w)]
    rfl
  · simp
  · have h := ordF_unif_self w
    unfold ordF at h
    rw [map_pow, valued_algebraMap, WithZero.log_pow, neg_eq_iff_eq_neg.1 h]
    simp

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_mk_eq_of_ord {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {a b : Ideles H.E}
    (h : ∀ w, ordI w a - ordI (conjPrime₂ w) a = ordI w b - ordI (conjPrime₂ w) b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtQ H SQ ⧸ UOQ H SQ) = QuotientGroup.mk (QuotientGroup.mk b) := by
  refine QuotientGroup.eq.2 ?_
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mk_mem_UOQ, KDq_sup_unitIdl]
  refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
  rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv,
    (isConjPl_iff H w w').1 hw]
  have := h w
  congr 1
  omega

end GlobalTheory.Mem.Col2.DetLat

namespace GlobalTheory.Mem.Col2

open DetLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_detPt_eq_relDetQ : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → (QuotientGroup.mk (detPt H SQ p) : DtQ H SQ ⧸ UOQ H SQ) = relDetQ H SQ n (stdLat H.E n) p.deco.1.N := by
  intro R H n ST SG Q SQ p hL
  have hN := p.deco.2.lat
  have hf : {w | (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat ≠ 0}.Finite :=
    (finite_ordSub hN).subset fun v hv h0 => hv (by simp [h0, ordSub_std])
  refine mk_mk_eq_of_ord H SQ (a := ptIdl H SQ p)
    (b := powI fun w => (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat) fun w => ?_
  rw [ordI_powI _ hf, ordI_powI _ hf, ptIdl, ordI_detIdl _ hN (isFr_ptFr p), ordI_detIdl _ hN (isFr_ptFr p),
    CharValCompare.conjP_conjP, ordSub_std, ordSub_std, ordSub_conj hN p.deco.2.uni]
  have hs := hL.split w
  by_cases h1 : w ∈ uSG SG SQ
  · rw [if_pos h1, if_neg (hs h1), if_pos h1]
    omega
  · by_cases h2 : conjPrime₂ w ∈ uSG SG SQ
    · rw [if_neg h1, if_pos h2, if_pos h2]
      omega
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
      omega

end GlobalTheory.Mem.Col2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeTjEqImageOfCoordinateLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeTjEqImageOfCoordinateLattice
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.LiftForms

theorem TjL_eq_map_matLat : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hL : OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P0 ψ0 i t)) (hZ : Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec (Pi.single k 1))))) (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x))))), Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  intro D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hL hZ hθ
  classical
  set J := (D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap with hJdef
  have hJ : ∀ x, J x = D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) := fun x => rfl
  have hspan : Idx.Z0 D (tup t) ((i : ℕ) + 1) =
      Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) := by
    rw [hZ, span_range_mulVec]
    rfl

  have hproj : ∀ x, (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J x) =
      J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hspan]
      exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
    · intro w hw
      rw [hspan] at hw
      have hle : Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) ≤
          (Submodule.span ℂ {J x - J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x))})ᗮ := by
        rw [Submodule.span_le]
        rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hF.inner, hF.inner,
          hform_orth hP, sub_self]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hw)

  have hθall : ∀ y, D.what₂.thetaP (tup t) ((i : ℕ) + 1) y =
      D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y) := by
    have h := LinearMap.ext_on_range hF.span (f := D.what₂.thetaP (tup t) ((i : ℕ) + 1))
      (g := (D.what₂.thetaP (tup t) ((i : ℕ) + 1)).comp
        ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection : D.what₂.Mt (tup t) ((i : ℕ) + 1) →L[ℂ] _).toLinearMap)
      (fun k => by
        show D.what₂.thetaP (tup t) ((i : ℕ) + 1) (J (Pi.single k 1)) =
          D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J (Pi.single k 1)))
        rw [hproj]
        exact hθ _)
    intro y
    exact LinearMap.congr_fun h y
  have hle1 : (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ ≤ LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)) := by
    intro w hw
    rw [LinearMap.mem_ker, hθall, (Submodule.starProjection_apply_eq_zero_iff _).2 hw, map_zero]
  have hZj : D.what₂.Zj (tup t) ((i : ℕ) + 1) = Idx.Z0 D (tup t) ((i : ℕ) + 1) := by
    have h1 : D.what₂.Zj (tup t) ((i : ℕ) + 1) = (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ := by
      rw [LinearMap.orthogonal_ker]
      rfl
    rw [h1]
    apply le_antisymm
    · have := Submodule.orthogonal_le hle1
      rwa [Submodule.orthogonal_orthogonal] at this
    · exact inf_le_left
  have hfix : ∀ y ∈ LinearMap.range (D.what₂.eMt (tup t) ((i : ℕ) + 1)), D.what₂.eMt (tup t) ((i : ℕ) + 1) y = y := by
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun f : D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] D.what₂.Mt (tup t) ((i : ℕ) + 1) => f y) (D.what₂.eMt_idem _ _)
  have h4' : ∀ y, D.what₂.eMt (tup t) ((i : ℕ) + 1) ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection y) =
      (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y := by
    intro y
    simp only [hZj]
    exact hfix _ (inf_le_right (a := (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ)
      (Submodule.starProjection_apply_mem (Idx.Z0 D (tup t) ((i : ℕ) + 1)) y))

  have h6 : Submodule.span (𝓞 D.what₂.LL)
      {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} =
      (lNab D A P0 ψ0 i t).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro u hu
      obtain ⟨c, hc⟩ := hu
      refine ⟨(eMt i t).symm u, (hL.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, ?_⟩, by simp⟩
      rw [hJ, LinearEquiv.apply_symm_apply, hc]
      rfl
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := (hL.2 x).1 hx
      have hc' : D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) =
          ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      have key : ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
          D.what₂.jMt (tup t) ((i : ℕ) + 1) y =
            ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := by
        refine Finset.sum_induction _ (fun m => ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
            D.what₂.jMt (tup t) ((i : ℕ) + 1) y = m) ?_ ⟨0, zero_mem _, map_zero _⟩ fun v hv => ?_
        · rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y + z, add_mem hy hz, map_add _ _ _⟩
        · obtain ⟨y, hy⟩ := D.what₂.MtLat_sub (tup t) ((i : ℕ) + 1) v hv
          refine ⟨c v • y, Submodule.smul_mem _ _ (Submodule.subset_span ?_), by rw [Idx.smul_def, map_smulₛₗ, hy]⟩
          refine ⟨fun u => if u = v then 1 else 0, ?_⟩
          rw [hy, Finset.sum_eq_single v]
          · simp
          · intro u _ hu
            simp [hu]
          · intro h; exact absurd hv h
      obtain ⟨y, hy, hyx⟩ := key
      have hxy : y = eMt i t x := jMt_injective _ _ (hyx.trans hc'.symm)
      change eMt i t x ∈ _
      rw [← hxy]
      exact hy

  let π : D.what₂.MtL (tup t) ((i : ℕ) + 1) →ₗ[𝓞 D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1) :=
    ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P0 ψ0 Zs i t).mulVecLin ∘ₗ
      (lPrj D A P0 ψ0 Zs i t).mulVecLin ∘ₗ (eMt i t).symm.toLinearMap).restrictScalars (𝓞 D.what₂.LL)
  have hπe : ∀ x, π (eMt i t x) = eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    show eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ (eMt i t).symm (eMt i t x))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hπ : ∀ x, D.what₂.jMt (tup t) ((i : ℕ) + 1) (π x) = D.what₂.eMt (tup t) ((i : ℕ) + 1)
      ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) := by
    intro x
    obtain ⟨x, rfl⟩ := (eMt i t).surjective x
    rw [h4', ← hJ, hproj, hπe]
    rfl
  have hset : {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ D.what₂.TjSet (tup t) ((i : ℕ) + 1)} =
      π '' {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} := by
    ext x
    constructor
    · rintro ⟨m, hm, hx⟩
      obtain ⟨u, rfl⟩ := carrier_subset _ _ m hm
      exact ⟨u, hm, jMt_injective _ _ ((hπ u).trans hx)⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hu, (hπ u).symm⟩
  unfold Idx.TjL
  rw [hset, ← Submodule.map_span, h6]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, (hπe y).symm⟩
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hπe y⟩

end GlobalTheory.Mem.LiftForms

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeTjEqImageOfCoordinateLatticeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_Tj_eq_image_of_coordinate_lattice : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hL : OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P0 ψ0 i t)) (hZ : Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec (Pi.single k 1))))) (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x))))), Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  first | exact @GlobalTheory.Mem.LiftForms.TjL_eq_map_matLat | exact GlobalTheory.Mem.LiftForms.TjL_eq_map_matLat | (intros; apply GlobalTheory.Mem.LiftForms.TjL_eq_map_matLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeOverSplitNotMemConj
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeOverSplitNotMemConj
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

namespace GlobalTheory.Mem.Col2.SplitPrime

theorem mem_xor {A : Type*} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (p t m : ℤ) (hp : (p : A) ∈ P) (a a' : A)
    (hm : a * a' = (p : A) * m) (ht : a + a' = t) (hc : IsCoprime p t) :
    (a ∈ P ∧ a' ∉ P) ∨ (a' ∈ P ∧ a ∉ P) := by
  have hnot : ¬ (a ∈ P ∧ a' ∈ P) := by
    rintro ⟨h1, h2⟩
    have h3 : (t : A) ∈ P := ht ▸ P.add_mem h1 h2
    obtain ⟨u, v, huv⟩ := hc
    have h4 : (u : A) * p + (v : A) * t = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) huv
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (h4 ▸ P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h3)))
  have h5 : a * a' ∈ P := hm ▸ P.mul_mem_right _ hp
  rcases hP.mem_or_mem h5 with h | h
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩

theorem exists_over (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥ (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K)))]
    exact bot_le)
  have hmem : (p : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Ideal.mem_bot).1 hmem)

theorem exists_elt {R : Ranks} (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (a : H.K) (t m : ℤ), IsIntegral ℤ a ∧ a * HostK.conjK H a = (p : H.K) * m ∧ a + HostK.conjK H a = t ∧
      IsCoprime (p : ℤ) t := by
  set θ : H.K := ⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ with hθ
  have hsq : θ ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa [hθ] using H.sqrtMinusD_sq)
  have hcj : HostK.conjK H θ = -θ := Subtype.ext (by simpa [hθ, HostK.coe_conjK] using H.conj_sqrtMinusD)
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 8 * m := by
      have := H.hyp.2.2.2.1
      exact ⟨(H.d + 1) / 8, by omega⟩
    have hm' : (H.d : H.K) + 1 = 8 * m := by exact_mod_cast hm
    refine ⟨(1 + θ) / 2, 1, m, HostK.isIntegral_half H, ?_, ?_, isCoprime_one_right⟩
    · rw [map_div₀, map_add (f := _), map_one, hcj, map_ofNat]
      push_cast
      linear_combination (-1 / 4 : H.K) * hsq + (1 / 4 : H.K) * hm'
    · rw [map_div₀, map_add (f := _), map_one, hcj, map_ofNat]
      push_cast
      ring
  · have hj : jacobiSym (-(H.d : ℤ)) p = 1 := hs.resolve_left h2
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
    have hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h
      rw [(legendreSym.eq_zero_iff p _).2 h] at hj
      exact zero_ne_one hj
    obtain ⟨s, hs'⟩ := (legendreSym.eq_one_iff p hne).1 hj
    obtain ⟨r, rfl⟩ := ZMod.intCast_surjective s
    have hr : ¬ (p : ℤ) ∣ r := by
      intro h
      rw [hs', (ZMod.intCast_zmod_eq_zero_iff_dvd r p).2 h] at hne
      exact hne (mul_zero _)
    have hdiv : (p : ℤ) ∣ r * r + H.d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast at hs' ⊢
      linear_combination -hs'
    obtain ⟨m, hm⟩ := hdiv
    have hm' : (r : H.K) * r + H.d = (p : H.K) * m := by exact_mod_cast congrArg (Int.cast : ℤ → H.K) hm
    have hθi : IsIntegral ℤ θ := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hsq]
      exact (isIntegral_natCast H.d).neg
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    refine ⟨r + θ, 2 * r, m, (isIntegral_intCast r).add hθi, ?_, ?_, ?_⟩
    · rw [map_add (f := _), map_intCast, hcj]
      linear_combination hm' - hsq
    · rw [map_add (f := _), map_intCast, hcj]
      push_cast
      ring
    · refine (hpi.coprime_iff_not_dvd).2 fun h => ?_
      rcases hpi.dvd_or_dvd h with h | h
      · have h' : p ∣ 2 := by exact_mod_cast h
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
      · exact hr h

theorem exists_prime_not_conj (R : Ranks) (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧
      (β : H.K) = HostK.conjK H α := by
  obtain ⟨a, t, m, hai, hm, ht, hc⟩ := exists_elt H p hp hs
  have hai' : IsIntegral ℤ (HostK.conjK H a) := by
    have : HostK.conjK H a = t - a := by linear_combination ht
    rw [this]
    exact (isIntegral_intCast t).sub hai
  obtain ⟨𝔭, h𝔭⟩ := exists_over H.K p hp
  let x : 𝓞 H.K := ⟨a, hai⟩
  let y : 𝓞 H.K := ⟨HostK.conjK H a, hai'⟩
  have hx : (x : H.K) = a := rfl
  have hy : (y : H.K) = HostK.conjK H a := rfl
  have h1 : x * y = ((p : ℤ) : 𝓞 H.K) * m := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using hm
  have h2 : x + y = t := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using ht
  rcases mem_xor 𝔭.asIdeal 𝔭.isPrime p t m (by exact_mod_cast h𝔭) x y h1 h2 hc with h | h
  · exact ⟨𝔭, x, y, h𝔭, h.1, h.2, rfl⟩
  · exact ⟨𝔭, y, x, h𝔭, h.1, h.2, by rw [hx, hy, HostK.conjK_conjK]⟩

end GlobalTheory.Mem.Col2.SplitPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeOverSplitNotMemConjStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_over_split_not_mem_conj : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → Th.SplitK H p → ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧ (β : H.K) = HostK.conjK H α := by
  first | exact @GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | exact GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | (intros; apply GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCurveLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCurveLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

noncomputable section

namespace GlobalTheory.Mem.Col2.CurveLat

theorem exists_periodPair_mul_image {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : 𝓞 K →+* ℂ) (hσ : Function.Injective σ) (a : 𝓞 K) (ha : (σ a).im ≠ 0) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ c : 𝓞 K, z = δ * σ c := by
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans hK)
  have hs : ∀ x : 𝓞 K, σ x = b.repr x 0 * σ (b 0) + b.repr x 1 * σ (b 1) := by
    intro x
    have := congrArg σ (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ (b 0) ≠ 0 := (map_ne_zero_iff σ hσ).2 (b.ne_zero 0)
  have h0 : (σ (b 1) * starRingEnd ℂ (σ (b 0))).im ≠ 0 := by
    intro h0
    have e := hs (a * b 0)
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ (b 0))).im) e
    simp only [map_mul] at e'
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨δ * σ (b 0), δ * σ (b 1), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e0
    have e : (x : ℂ) * σ (b 0) + (y : ℂ) * σ (b 1) = 0 := by
      apply mul_left_cancel₀ hδ
      simp only [Complex.real_smul] at e0
      linear_combination e0
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 1)).im * e1 - (σ (b 1)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 0)).re * e2 - (σ (b 0)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m • b 0 + n • b 1, by simp; ring⟩
    · rintro ⟨x, rfl⟩
      exact ⟨b.repr x 0, b.repr x 1, by rw [hs x]; ring⟩

theorem not_isIntegral_half : ¬ IsIntegral ℤ (1 / 2 : ℂ) := by
  intro h
  have h1 : IsIntegral ℤ (1 / 2 : ℚ) := by
    refine (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).1 ?_
    simpa using h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  have h2 : (2 * y : ℚ) = 1 := by
    simp only [eq_intCast] at hy
    rw [hy]; norm_num
  have h3 : 2 * y = 1 := by exact_mod_cast h2
  omega

theorem not_isIntegral_of_re {z : ℂ} (hz : z.re = 1 / 4) : ¬ IsIntegral ℤ z := by
  intro h
  have h1 : IsIntegral ℤ (starRingEnd ℂ z) := h.map (starRingEnd ℂ).toIntAlgHom
  have h2 := h.add h1
  rw [Complex.add_conj, hz] at h2
  apply not_isIntegral_half
  have e : ((2 * (1 / 4) : ℝ) : ℂ) = 1 / 2 := by
    push_cast
    norm_num
  rwa [e] at h2

variable {R : Ranks} (H : Host R)

def embO : 𝓞 H.K →+* ℂ := (H.φ₀.comp H.K.val.toRingHom).comp (algebraMap (𝓞 H.K) H.K)

theorem mem_lamOf_top (δ z : ℂ) : z ∈ Th.lamOf H ⊤ δ ↔ ∃ c : 𝓞 H.K, z = δ * embO H c := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, -, rfl⟩ := hx
      exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by rw [map_add (f := _), mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, by rw [map_neg, mul_neg]⟩
  · rintro ⟨c, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, rfl⟩

theorem exists_periodPair_lamOf (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Th.lamOf H ⊤ δ ↔ z ∈ L.lattice := by
  have hK : Module.finrank ℚ H.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq
  have hinj : Function.Injective (embO H) :=
    (H.φ₀.comp H.K.val.toRingHom).injective.comp RingOfIntegers.coe_injective
  have ha : (embO H ⟨_, HostK.isIntegral_half H⟩).im ≠ 0 := by
    have e : embO H ⟨_, HostK.isIntegral_half H⟩ = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2 := by
      rw [← HostK.φ₀_sqrt]
      change (H.φ₀.comp H.K.val.toRingHom) ((1 + (⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ : H.K)) / 2) = _
      rw [map_div₀, map_add (f := _), map_one, map_ofNat]
      rfl
    have hd : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
    rw [e]
    simp [hd.ne']
  obtain ⟨L, hL⟩ := exists_periodPair_mul_image hK (embO H) hinj _ ha δ hδ
  exact ⟨L, fun z => by rw [mem_lamOf_top, hL]⟩

theorem not_mem_lamOf (δ : ℂ) (hδ : δ ≠ 0) {z : ℂ} (hz : z.re = 1 / 4) : δ * z ∉ Th.lamOf H ⊤ δ := by
  rw [mem_lamOf_top]
  rintro ⟨c, hc⟩
  apply not_isIntegral_of_re hz
  rw [mul_left_cancel₀ hδ hc]
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) c).map (embO H).toIntAlgHom

end GlobalTheory.Mem.Col2.CurveLat

namespace GlobalTheory.Mem.Col2

open CurveLat

theorem exists_curve_lattice : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  intro R H
  obtain ⟨L₁, h₁⟩ := exists_periodPair_lamOf H 1 one_ne_zero
  have hΔ := (GlobalTheory.LatticeInvariants.invariants_dictionary L₁ _ h₁).2.2.1
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (Th.lamOf H ⊤ 1)) (n := 12) (by norm_num)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hδ]; norm_num)
  obtain ⟨L, hL⟩ := exists_periodPair_lamOf H δ hδ0
  refine ⟨δ, L, δ, hδ, AddSubgroup.ext fun z => (hL z).symm, ?_, ?_, ?_⟩
  · exact (mem_lamOf_top H δ _).2 ⟨1, by rw [map_one]; ring⟩
  · have := not_mem_lamOf H δ hδ0 (z := (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring
  · have := not_mem_lamOf H δ hδ0 (z := (1 - Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring

end GlobalTheory.Mem.Col2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCurveLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodPair_lattice_eq_lamOf : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  first | exact @GlobalTheory.Mem.Col2.exists_curve_lattice | exact GlobalTheory.Mem.Col2.exists_curve_lattice | (intros; apply GlobalTheory.Mem.Col2.exists_curve_lattice <;> assumption)
end
end

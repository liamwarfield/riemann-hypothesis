module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecOfF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ContinuousInvT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupport
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.MemComm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.FrameTh
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SepConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisintegrationDensityExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateEigenSubDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldedEqOrbitalReps

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SplitC
set_option autoImplicit false

namespace UpperTheory.Gal.Spc

open UpperTheory.Gal.W2.Seed GlobalTheory.LKTrip GlobalTheory.UPel.HT

private def splitEquiv {X M : Type} [Group X] [Group M] (L : Loc X M) : X ≃* M × L.pr.ker where
  toFun g := (L.pr g, ⟨(L.loc (L.pr g))⁻¹ * g, by simp [MonoidHom.mem_ker, L.pr_loc]⟩)
  invFun x := L.loc x.1 * (x.2 : X)
  left_inv g := by simp
  right_inv x := by
    obtain ⟨m, h, hh⟩ := x
    have hh' : L.pr h = 1 := hh
    ext <;> simp [L.pr_loc, hh']
  map_mul' g h := by
    have hc : L.pr ((L.loc (L.pr g))⁻¹ * g) = 1 := by simp [L.pr_loc]
    have key := L.comm (L.pr h)⁻¹ _ hc
    rw [map_inv] at key
    refine Prod.ext (map_mul _ _ _) (Subtype.ext ?_)
    show (L.loc (L.pr (g * h)))⁻¹ * (g * h) = (L.loc (L.pr g))⁻¹ * g * ((L.loc (L.pr h))⁻¹ * h)
    rw [← mul_assoc ((L.loc (L.pr g))⁻¹ * g), ← key]
    simp [mul_assoc]

private theorem t2Space_hTGroup_gAf {p : ℕ} [Fact p.Prime] (G : HTGroup p) : T2Space G.GAf := by
  haveI := GlobalTheory.GfTop.t2Space_afP p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_locallyCompactSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_totallyDisconnectedSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_secondCountableTopology p
  exact (GlobalTheory.GfTop.upts_props G.star (AfP p)).2.1

theorem splitC : SplitC := by
  intro p _ G Lv k _ _ _ _ P L hcont hat Kw hKo hKc hF
  haveI := t2Space_hTGroup_gAf G
  have hker : IsClosed (L.pr.ker : Set G.GAf) := isClosed_singleton.preimage hcont
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨splitEquiv L, fun g => (hat g).symm, Kw, (Lv.K : Subgroup G.GAf).subgroupOf L.pr.ker,
      hKo, hKc, ?_, ?_, ?_⟩, fun g h => rfl⟩
  · exact Lv.K.isOpen.preimage continuous_subtype_val
  · exact hker.isClosedEmbedding_subtypeVal.isCompact_preimage Lv.compact
  · ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hF.2 g hg, ?_⟩
      show (L.loc (L.pr g))⁻¹ * g ∈ (Lv.K : Subgroup G.GAf)
      exact mul_mem (inv_mem (hF.1 _ (hF.2 g hg))) hg
    · rintro ⟨hm, hh⟩
      exact ⟨L.loc x.1 * (x.2 : G.GAf), mul_mem (hF.1 _ hm) hh,
        (splitEquiv L).apply_symm_apply x⟩

end UpperTheory.Gal.Spc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.FacCont
set_option autoImplicit false

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef
open GlobalTheory.CuspRep (pLoc)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw mat)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem small_of_nhds {E : Type} [Field E] [NumberField E] (w : Plc E) {U : Set (w.adicCompletion E)}
    (hU : U ∈ 𝓝 (0 : w.adicCompletion E)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : w.adicCompletion E, Valued.v x ≤ Valued.v (M : w.adicCompletion E) → x ∈ U := by
  obtain ⟨γ, -, hγ⟩ := (Valued.hasBasis_nhds_zero (w.adicCompletion E) _).mem_iff.1 hU
  have hball := (Valued.hasBasis_nhds_zero (w.adicCompletion E) _).mem_of_mem (i := γ) trivial
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hlt : Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) < 1 := by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w _).2 hm
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E)) =
        w.valuation E (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have h3 : algebraMap E (w.adicCompletion E) (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E) =
        ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) := by simp
    rw [h3] at h2
    rw [h2]
    exact h1
  obtain ⟨m, hm⟩ := ((Valued.tendsto_zero_pow_of_v_lt_one hlt).eventually hball).exists
  refine ⟨Ideal.absNorm w.asIdeal ^ m, Nat.pos_of_ne_zero (pow_ne_zero _ hN0), fun x hx => hγ ?_⟩
  have hx' : Valued.v x ≤ Valued.v (((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) ^ m) := by
    simpa using hx
  exact lt_of_le_of_lt ((Valuation.restrict_le_iff _).2 hx') hm

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.facCont :
    UpperTheory.Gal.Spc.FacCont := by
  intro E _ _ _ A n p _ S F w L hL
  have hI := pKNIff (pLatCoord pRepLaws)
  have key : ∀ M : ℕ, 0 < M → ∀ k ∈ S.L.KN M, Cong1 M w.1 (F.a w.1 * L.pr k * (F.a w.1)⁻¹) := by
    intro M hM k hk
    obtain ⟨g, rfl⟩ := F.surj k
    have h1 : S.L.CongOne M (F.tr.j g) := by rw [← F.j_tr]; exact hk.1
    have h2 := ((hI E A n p S F.tr g).2 M hM).1 h1 w.1 w.2.2
    have h3 : UpperTheory.Gal.CertificateRingHomMap.comp w.1 g = GeneralLinearGroup.map (pLoc E w.1) (mat g) := rfl
    rw [hL.1 g, F.a_tr, h3]
    simpa [map_mul, map_inv] using h2
  have hopen : ∀ M : ℕ, 0 < M → (S.L.KN M : Set S.G.GAf) ∈ 𝓝 (1 : S.G.GAf) := by
    intro M hM
    obtain ⟨K, hK⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p S.D S.G S.L M hM
    have ho : IsOpen (S.L.KN M : Set S.G.GAf) := hK ▸ K.K.isOpen
    exact ho.mem_nhds (one_mem _)

  have hent : ∀ i j, Filter.Tendsto (fun k => ((F.a w.1 * L.pr k * (F.a w.1)⁻¹).val - 1) i j) (𝓝 (1 : S.G.GAf)) (𝓝 0) := by
    intro i j U hU
    obtain ⟨M, hM, hsm⟩ := small_of_nhds w.1 hU
    exact Filter.mem_map.2 (Filter.mem_of_superset (hopen M hM) fun k hk => hsm _ (key M hM k hk i j))
  have hmat : Filter.Tendsto (fun k => (F.a w.1 * L.pr k * (F.a w.1)⁻¹).val) (𝓝 (1 : S.G.GAf))
      (𝓝 (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E))) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have := (hent i j).add_const ((1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j)
    simpa [Matrix.sub_apply] using this
  have hval : ContinuousAt (fun k => (L.pr k).val) (1 : S.G.GAf) := by
    have h := ((tendsto_const_nhds (x := ((F.a w.1)⁻¹).val)).mul hmat).mul (tendsto_const_nhds (x := (F.a w.1).val))
    have h1 : ((F.a w.1)⁻¹).val * 1 * (F.a w.1).val = (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) := by
      rw [mul_one]; exact (F.a w.1).inv_mul
    rw [h1] at h
    have h2 : ∀ k, ((F.a w.1)⁻¹).val * (F.a w.1 * L.pr k * (F.a w.1)⁻¹).val * (F.a w.1).val = (L.pr k).val := by
      intro k
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    simp only [h2] at h
    simpa [ContinuousAt] using h
  have hinv : ContinuousAt (fun k => (((L.pr k)⁻¹ : GL (Fin n) (w.1.adicCompletion E))).val) (1 : S.G.GAf) := by
    have h : ContinuousAt (fun k : S.G.GAf => k⁻¹) 1 := continuous_inv.continuousAt
    have h' : ContinuousAt (fun k => (L.pr k).val) ((1 : S.G.GAf)⁻¹) := by simpa using hval
    have h2 : (fun k => (((L.pr k)⁻¹ : GL (Fin n) (w.1.adicCompletion E))).val) =
        (fun k => (L.pr k).val) ∘ (fun k : S.G.GAf => k⁻¹) := by
      funext k
      simp only [Function.comp, map_inv]
    rw [h2]
    exact ContinuousAt.comp h' h
  refine continuous_of_continuousAt_one L.pr ?_
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  exact hval.prodMk (MulOpposite.continuous_op.continuousAt.comp hinv)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AdmCusp
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSliceAlt
set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL

namespace UpperTheory.Gal.Spc

private def lreg (G : Type) [Group G] : Representation ℂ G (G → ℂ) where
  toFun g :=
    { toFun := fun F x => F (g⁻¹ * x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext F x
    simp
  map_mul' a b := by
    ext F x
    simp [mul_assoc]

private theorem lreg_apply {G : Type} [Group G] (g : G) (F : G → ℂ) (x : G) : lreg G g F x = F (g⁻¹ * x) := rfl

private theorem finsum_shift {G : Type} [Group G] (K : Subgroup G) (Φ : G → ℂ) (hΦ : ∀ g, ∀ k ∈ K, Φ (g * k) = Φ g) (z : G) :
    ∑ᶠ q : G ⧸ K, Φ q.out = ∑ᶠ q : G ⧸ K, Φ (z * q.out) := by
  have hc : ∀ g g' : G, (g : G ⧸ K) = g' → Φ g = Φ g' := by
    intro g g' h
    have h1 : g⁻¹ * g' ∈ K := QuotientGroup.eq.1 h
    have := hΦ g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm
  have h2 : ∀ q : G ⧸ K, Φ (z * q.out) = Φ (z • q).out := by
    intro q
    apply hc
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  simp only [h2]
  exact (finsum_comp_equiv (MulAction.toPerm z : Equiv.Perm (G ⧸ K)) (f := fun q => Φ q.out)).symm

private theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (F : G → ℂ) (hF : HasCompactSupport F) :
    (Function.support fun q : G ⧸ K => F q.out).Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hcomp : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport F) :=
    hF.isCompact.image QuotientGroup.continuous_mk
  refine hcomp.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

section Core

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace A]

private def transl (e : G → ℂ) : Subrepresentation (lreg G) :=
  ⟨Submodule.span ℂ (Set.range fun g : G => lreg G g e), by
    intro g F hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      refine Submodule.subset_span ⟨g * t, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c hx⟩

private theorem mem_transl_self (e : G → ℂ) : e ∈ (transl e).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

private theorem transl_cont {e : G → ℂ} (hc : Continuous e) (hs : HasCompactSupport e) {F : G → ℂ}
    (hF : F ∈ (transl e).toSubmodule) : Continuous F ∧ HasCompactSupport F := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    refine ⟨hc.comp (continuous_const.mul continuous_id), ?_⟩
    exact hs.comp_homeomorph (Homeomorph.mulLeft t⁻¹)
  | zero => exact ⟨continuous_const, HasCompactSupport.zero⟩
  | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, hx.2.add hy.2⟩
  | smul c x _ hx => exact ⟨continuous_const.mul hx.1, hx.2.smul_left⟩

private theorem transl_smooth {e : G → ℂ} (K : Subgroup G) (hK : IsOpen (K : Set G)) (hKe : ∀ k ∈ K, lreg G k e = e) :
    IsSmooth (transl e).toRepresentation := by
  refine isSmooth_of_nhds fun F => ?_
  have key : ∀ x ∈ (transl e).toSubmodule, {g : G | lreg G g x = x} ∈ nhds (1 : G) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      have hcont : Continuous fun g : G => t⁻¹ * g * t := (continuous_const.mul continuous_id).mul continuous_const
      have h1 : (fun g : G => t⁻¹ * g * t) ⁻¹' (K : Set G) ∈ nhds (1 : G) :=
        (hK.preimage hcont).mem_nhds (by simp [K.one_mem])
      refine Filter.mem_of_superset h1 fun g hg => ?_
      have h2 := hKe _ hg
      show lreg G g (lreg G t e) = lreg G t e
      have h3 : lreg G g (lreg G t e) = lreg G t (lreg G (t⁻¹ * g * t) e) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [h3]
      exact congrArg _ h2
    | zero => simp
    | add x y _ _ hx hy =>
      refine Filter.mem_of_superset (Filter.inter_mem hx hy) fun g hg => ?_
      show lreg G g (x + y) = x + y
      rw [map_add (f := _), hg.1, hg.2]
    | smul c x _ hx =>
      refine Filter.mem_of_superset hx fun g hg => ?_
      show lreg G g (c • x) = c • x
      rw [map_smul, hg]
  refine Filter.mem_of_superset (key F.1 F.2) fun g hg => ?_
  exact Subtype.ext hg

private def noTerm (e : G → ℂ) (hc : Continuous e) (hs : HasCompactSupport e) (μ : Measure A) (U : A → G)
    (hint : ∀ F : G → ℂ, Continuous F → HasCompactSupport F → ∀ z w : G, Integrable (fun X => F (z * U X * w)) μ) :
    Subrepresentation (lreg G) :=
  ⟨{ carrier := {F | F ∈ (transl e).toSubmodule ∧ ∀ x, ∫ X, F (x * U X * 1) ∂μ = 0}
     add_mem' := by
       rintro F F' ⟨h1, h2⟩ ⟨h1', h2'⟩
       refine ⟨Submodule.add_mem _ h1 h1', fun x => ?_⟩
       have c1 := transl_cont hc hs h1
       have c2 := transl_cont hc hs h1'
       simp only [Pi.add_apply]
       rw [integral_add (hint F c1.1 c1.2 x 1) (hint F' c2.1 c2.2 x 1), h2, h2', add_zero]
     zero_mem' := ⟨Submodule.zero_mem _, fun x => by simp⟩
     smul_mem' := by
       rintro c F ⟨h1, h2⟩
       refine ⟨Submodule.smul_mem _ c h1, fun x => ?_⟩
       simp only [Pi.smul_apply, smul_eq_mul]
       rw [integral_const_mul, h2, mul_zero] }, by
    rintro g F ⟨h1, h2⟩
    refine ⟨(transl e).apply_mem_toSubmodule g h1, fun x => ?_⟩
    have := h2 (g⁻¹ * x)
    simpa only [lreg_apply, mul_assoc] using this⟩

end Core

section Core2

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace A]

private theorem core (μ : Measure A) (U : A → G)
    (hint : ∀ F : G → ℂ, Continuous F → HasCompactSupport F → ∀ z w : G, Integrable (fun X => F (z * U X * w)) μ)
    (J : Subgroup G) (hJo : IsOpen (J : Set G)) (hJc : IsCompact (J : Set G)) (χ : J →* ℂˣ) (hχ : IsOpen (χ.ker : Set J))
    (e : G → ℂ) (he1 : ∀ g (hg : g ∈ J), e g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) (he0 : ∀ g, g ∉ J → e g = 0)
    (hne : ∫ X, e (1 * U X * 1) ∂μ ≠ 0) :
    ∃ (σ : GlobalTheory.SmGL.IrrRep G) (v : σ.V), v ≠ 0 ∧ (∀ g : J, σ.ρ g v = ((χ g : ℂˣ) : ℂ) • v) ∧
      ∀ K₂ : Subgroup G, K₂ ≤ χ.ker.map J.subtype → IsOpen (K₂ : Set G) → ∀ f : G → ℂ, Continuous f → HasCompactSupport f →
        (∀ g, ∀ k ∈ K₂, f (g * k) = f g) → (∀ z w : G, ∫ X, f (z * U X * w) ∂μ = 0) →
        ∀ (l : Module.Dual ℂ σ.V) (S : Finset (G ⧸ K₂)), (∀ q, q ∉ S → f q.out = 0) →
          ∑ q ∈ S, f q.out * l (σ.ρ q.out v) = 0 := by
  classical
  have hKo : IsOpen ((χ.ker.map J.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact hJo.isOpenMap_subtype_val _ hχ
  have hR : ∀ g, ∀ k ∈ χ.ker.map J.subtype, e (g * k) = e g := by
    rintro g _ ⟨y, hy, rfl⟩
    have h1 : χ y = 1 := hy
    show e (g * (y : G)) = e g
    by_cases hg : g ∈ J
    · have hm : g * (y : G) ∈ J := J.mul_mem hg y.2
      rw [he1 _ hm, he1 g hg]
      have : (⟨g * (y : G), hm⟩ : J) = ⟨g, hg⟩ * y := rfl
      rw [this, map_mul, h1, mul_one]
    · rw [he0 g hg, he0 _ (fun h => hg ((J.mul_mem_cancel_right y.2).1 h))]
  have hL : ∀ (j : J) (g : G), e ((j : G)⁻¹ * g) = ((χ j : ℂˣ) : ℂ) * e g := by
    intro j g
    by_cases hg : g ∈ J
    · have hm : (j : G)⁻¹ * g ∈ J := J.mul_mem (J.inv_mem j.2) hg
      rw [he1 _ hm, he1 g hg]
      have : (⟨(j : G)⁻¹ * g, hm⟩ : J) = j⁻¹ * ⟨g, hg⟩ := rfl
      rw [this, map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]
    · rw [he0 g hg, he0 _ (fun h => hg ((J.mul_mem_cancel_left (J.inv_mem j.2)).1 h)), mul_zero]
  have hlc : IsLocallyConstant e := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' ((χ.ker.map J.subtype : Subgroup G) : Set G),
      hKo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
      exact Subgroup.one_mem _
    · intro x hx
      have := hR g _ hx
      rwa [mul_inv_cancel_left] at this
  have hcont : Continuous e := hlc.continuous
  have hcs : HasCompactSupport e := HasCompactSupport.intro' hJc (J.isClosed_of_isOpen hJo) (fun g hg => he0 g hg)
  have hKe : ∀ k ∈ χ.ker.map J.subtype, lreg G k e = e := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : χ y = 1 := hy
    funext x
    rw [lreg_apply]
    have := hL y x
    rw [h1] at this
    simpa using this
  set S := transl e with hS
  set T := noTerm e hcont hcs μ U hint with hT
  have hSs : IsSmooth S.toRepresentation := transl_smooth _ hKo hKe
  have hQs : IsSmooth (subQuot S T) :=
    (IsSubquotient.of_surjective (σ := subQuot S T) (ρ := S.toRepresentation) ⟨Submodule.mkQ _, fun _ => rfl⟩
      (Submodule.Quotient.mk_surjective _)).isSmooth hSs
  let ê : S.toSubmodule := ⟨e, mem_transl_self e⟩
  let w : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype := Submodule.Quotient.mk ê
  have hw : w ≠ 0 := by
    intro h0
    have h1 : ê ∈ T.toSubmodule.comap S.toSubmodule.subtype := (Submodule.Quotient.mk_eq_zero _).1 h0
    exact hne (h1.2 1)
  have hgen : Submodule.span ℂ (Set.range fun p : G × ({w} : Finset _) => subQuot S T p.1 (p.2 : _)) = ⊤ := by
    set M := Submodule.span ℂ (Set.range fun p : G × ({w} : Finset _) => subQuot S T p.1 (p.2 : _)) with hM
    have hmem : ∀ g, subQuot S T g w ∈ M := fun g => Submodule.subset_span ⟨(g, ⟨w, by simp⟩), rfl⟩
    have hall : ∀ (F : G → ℂ) (hF : F ∈ S.toSubmodule),
        (Submodule.Quotient.mk ⟨F, hF⟩ : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ M := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t, rfl⟩ := hx
        exact hmem t
      | zero => exact Submodule.zero_mem _
      | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
      | smul c x hx ih => exact Submodule.smul_mem _ c ih
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨⟨F, hF⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact hall F hF
  haveI : Nontrivial (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) := ⟨⟨w, 0, hw⟩⟩
  have exists_quot : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), GlobalTheory.PRep.IsSmooth π → Nontrivial V → ∀ s : Finset V, Submodule.span ℂ (Set.range fun p : G × s => π p.1 (p.2 : V)) = ⊤ → ∃ (σ : IrrRep G) (p : V →ₗ[ℂ] σ.V), Function.Surjective p ∧ ∀ g v, p (π g v) = σ.ρ g (p v) := by
    intro G V _ _ _ _ _ π hπ hV s hs
    classical
  
    have htop : ∀ N : Submodule ℂ V, (∀ (g : G), ∀ v ∈ N, π g v ∈ N) →
        Submodule.span ℂ ((s : Set V)) ≤ N → N = ⊤ := by
      intro N hN hsN
      rw [eq_top_iff, ← hs, Submodule.span_le]
      rintro _ ⟨⟨g, v⟩, rfl⟩
      exact hN g _ (hsN (Submodule.subset_span v.2))
    let S : Set (Submodule ℂ V) := {N | (∀ (g : G), ∀ v ∈ N, π g v ∈ N) ∧ N ≠ ⊤}
    have hbot : (⊥ : Submodule ℂ V) ∈ S := ⟨fun g v hv => by
      rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], bot_ne_top⟩
    have hcomp := Submodule.finset_span_isCompactElement (R := ℂ) s
    obtain ⟨N, -, hmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
      have hne : c.Nonempty := ⟨y, hy⟩
      have hd : DirectedOn (· ≤ ·) c := hc.directedOn
      refine ⟨sSup c, ⟨fun g v hv => ?_, fun htop' => ?_⟩, fun z hz => le_sSup hz⟩
      · obtain ⟨M, hM, hvM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hv
        exact le_sSup hM ((hcS hM).1 g v hvM)
      · obtain ⟨M, hM, hsM⟩ := (isCompactElement_iff_le_of_directed_sSup_le _).1 hcomp c hne hd
          (by rw [htop']; exact le_top)
        exact (hcS hM).2 (htop M (hcS hM).1 hsM)) ⊥ hbot
    obtain ⟨hNst, hNtop⟩ := hmax.prop
    let T : Subrepresentation π := ⟨N, fun g v hv => hNst g v hv⟩
    have hT : IsCoatom T := by
      refine ⟨fun h => hNtop (congrArg Subrepresentation.toSubmodule h), fun T' hT' => ?_⟩
      by_contra hne
      have hmem : T'.toSubmodule ∈ S := ⟨fun g v hv => T'.apply_mem_toSubmodule g hv,
        fun h => hne (Subrepresentation.toSubmodule_injective h)⟩
      have heq : T'.toSubmodule = N := le_antisymm (hmax.2 hmem hT'.le) hT'.le
      exact hT'.ne (Subrepresentation.toSubmodule_injective heq.symm)
    have hi := isIrreducible_subQuot hT.covBy_top
    let q : (⊤ : Subrepresentation π).toRepresentation.IntertwiningMap (subQuot ⊤ T) :=
      ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hsm : IsSmooth (subQuot ⊤ T) :=
      IsSubquotient.isSmooth ⟨⊤, q, Submodule.Quotient.mk_surjective _⟩ hπ
    let σ : IrrRep G := ⟨_, subQuot ⊤ T, hsm, hi⟩
    let p : V →ₗ[ℂ] σ.V := (Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
      LinearMap.id (fun _ => trivial)
    refine ⟨σ, p, fun w => ?_, fun g v => rfl⟩
    obtain ⟨⟨v, -⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨v, rfl⟩
  obtain ⟨σ, p, hp, hpi⟩ := exists_quot G _ (subQuot S T) hQs inferInstance {w} hgen
  refine ⟨σ, p w, ?_, ?_, ?_⟩
  · intro h0
    have hker : Submodule.span ℂ (Set.range fun p : G × ({w} : Finset _) => subQuot S T p.1 (p.2 : _)) ≤ LinearMap.ker p := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨g, y⟩, rfl⟩
      have hy : (y : _) = w := Finset.mem_singleton.1 y.2
      simp only [SetLike.mem_coe, LinearMap.mem_ker, hy, hpi, h0, map_zero]
    rw [hgen] at hker
    have := nontrivial_of_irreducible σ.irr
    obtain ⟨x, hx⟩ := exists_ne (0 : σ.V)
    obtain ⟨y, rfl⟩ := hp x
    exact hx (hker Submodule.mem_top)
  · intro g
    rw [← hpi, ← map_smul]
    congr 1
    have : S.toRepresentation (g : G) ê = ((χ g : ℂˣ) : ℂ) • ê := by
      apply Subtype.ext
      funext x
      exact hL g x
    show Submodule.Quotient.mk (S.toRepresentation (g : G) ê) = _
    rw [this]
    rfl
  · intro K₂ hK₂ hK₂o f hfc hfs hfR hfZ l Sf hSf
    let Θ : S.toSubmodule := ∑ q ∈ Sf, f q.out • S.toRepresentation q.out ê
    have hB := finite_cosets K₂ hK₂o (fun t => e t⁻¹) (hcs.comp_homeomorph (Homeomorph.inv G))
    have hval : ∀ z, (Θ : G → ℂ) z = ∑ q ∈ hB.toFinset, e q.out⁻¹ * f (z * q.out) := by
      intro z
      have h1 : (Θ : G → ℂ) z = ∑ q ∈ Sf, f q.out * e (q.out⁻¹ * z) := by
        simp only [Θ, Submodule.coe_sum, Finset.sum_apply]
        rfl
      let Φ : G → ℂ := fun t => f t * e (t⁻¹ * z)
      have hΦ : ∀ g, ∀ k ∈ K₂, Φ (g * k) = Φ g := by
        intro g k hk
        have h2 := congrFun (hKe k (hK₂ hk)) (g⁻¹ * z)
        rw [lreg_apply] at h2
        simp only [Φ, hfR g k hk, _root_.mul_inv_rev, mul_assoc, h2]
      rw [h1, show (∑ q ∈ Sf, f q.out * e (q.out⁻¹ * z)) = ∑ᶠ q : G ⧸ K₂, Φ q.out from ?_, finsum_shift K₂ Φ hΦ z]
      · rw [finsum_eq_sum_of_support_subset (s := hB.toFinset)]
        · refine Finset.sum_congr rfl fun q _ => ?_
          simp only [Φ, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
          rw [mul_comm]
        · intro q hq
          simp only [Set.Finite.coe_toFinset, Function.mem_support] at hq ⊢
          intro h0
          apply hq
          simp only [Φ, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, h0, mul_zero]
      · symm
        refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
        by_contra hqS
        exact hq (by simp only [Φ, hSf q hqS, zero_mul])
    have hΘ : (Θ : G → ℂ) ∈ T.toSubmodule := by
      refine ⟨Θ.2, fun x => ?_⟩
      simp only [hval]
      rw [integral_finsetSum]
      · refine Finset.sum_eq_zero fun q _ => ?_
        rw [integral_const_mul]
        have := hfZ x q.out
        simp only [mul_one]
        rw [this, mul_zero]
      · intro q _
        have := (hint f hfc hfs x q.out).const_mul (e q.out⁻¹)
        simpa only [mul_one] using this
    have hz : p (Submodule.Quotient.mk Θ) = 0 := by
      have : (Submodule.Quotient.mk Θ : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hΘ
      rw [this, map_zero]
    have hexp : p (Submodule.Quotient.mk Θ) = ∑ q ∈ Sf, f q.out • σ.ρ q.out (p w) := by
      have : (Submodule.Quotient.mk Θ : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) =
          ∑ q ∈ Sf, f q.out • subQuot S T q.out w := by
        simp only [Θ]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Submodule.mkQ_apply, map_sum]
        rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, hpi]
    have := congrArg l (hexp.symm.trans hz)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using this

end Core2

section Slice

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n a b : ℕ}

private theorem u_zero (ε : Fin n ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin n) k)
    (hu : ∀ X, (u X : Matrix (Fin n) (Fin n) k) = Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) :
    u 0 = 1 := by
  apply Units.ext
  rw [hu]
  have h0 : (Matrix.of (0 : Fin a → Fin b → k)) = 0 := rfl
  rw [h0, Matrix.fromBlocks_one]
  simp

private theorem u_neg (ε : Fin n ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin n) k)
    (hu : ∀ X, (u X : Matrix (Fin n) (Fin n) k) = Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1))
    (X : Fin a → Fin b → k) : (u X)⁻¹ = u (-X) := by
  have h := GlobalTheory.typeFunction_unip_add ε u hu X (-X)
  rw [neg_add_cancel, u_zero ε u hu] at h
  exact inv_eq_of_mul_eq_one_right h.symm

private theorem u_val_cont (ε : Fin n ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin n) k)
    (hu : ∀ X, (u X : Matrix (Fin n) (Fin n) k) = Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) :
    Continuous fun X => (u X : Matrix (Fin n) (Fin n) k) := by
  refine continuous_matrix fun i j => ?_
  simp only [hu, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rcases ε i with p | p <;> rcases ε j with q | q
  · simpa only [Matrix.fromBlocks_apply₁₁] using continuous_const
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    exact (continuous_apply q).comp (continuous_apply p)
  · simpa only [Matrix.fromBlocks_apply₂₁] using continuous_const
  · simpa only [Matrix.fromBlocks_apply₂₂] using continuous_const

private theorem u_cont (ε : Fin n ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin n) k)
    (hu : ∀ X, (u X : Matrix (Fin n) (Fin n) k) = Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) :
    Continuous u := by
  refine Units.continuous_iff.2 ⟨u_val_cont ε u hu, ?_⟩
  have h1 : (fun X => (((u X)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) = (fun X => (u X : Matrix (Fin n) (Fin n) k)) ∘ Neg.neg := by
    funext X
    simp only [Function.comp_apply, u_neg ε u hu]
  exact h1 ▸ (u_val_cont ε u hu).comp continuous_neg

private theorem slice_compact (ε : Fin n ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin n) k)
    (hu : ∀ X, (u X : Matrix (Fin n) (Fin n) k) = Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1))
    (h z w : GL (Fin n) k) (C : Set (GL (Fin n) k)) (hC : IsCompact C) :
    ∃ D : Set (Fin a → Fin b → k), IsCompact D ∧ ∀ X, z * (h⁻¹ * u X * h) * w ∈ C → X ∈ D := by
  let ψ : GL (Fin n) k → Fin a → Fin b → k := fun g p q =>
    ((h * z⁻¹ * g * w⁻¹ * h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (ε.symm (Sum.inl p)) (ε.symm (Sum.inr q))
  have hψ : Continuous ψ := by
    refine continuous_pi fun p => continuous_pi fun q => ?_
    have h1 : Continuous fun g : GL (Fin n) k => h * z⁻¹ * g * w⁻¹ * h⁻¹ :=
      ((continuous_const.mul continuous_id).mul continuous_const).mul continuous_const
    exact (Units.continuous_val.comp h1).matrix_elem _ _
  refine ⟨ψ '' C, hC.image hψ, fun X hX => ⟨_, hX, ?_⟩⟩
  funext p q
  have h2 : h * z⁻¹ * (z * (h⁻¹ * u X * h) * w) * w⁻¹ * h⁻¹ = u X := by group
  simp only [ψ, h2, hu, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Matrix.fromBlocks_apply₁₂, Matrix.of_apply]

end Slice

theorem typeSlice : TypeSlice := by
  intro k _ _ _ _ _ n J hJo hJc χ hχ hcusp a b ε ha hb u hu h
  by_contra hcon
  push_neg at hcon
  classical
  borelize k
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  let μ : Measure (Fin a → Fin b → k) := Measure.addHaar
  haveI : μ.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar).IsAddHaarMeasure
  let U : (Fin a → Fin b → k) → GL (Fin n) k := fun X => h⁻¹ * u X * h
  have hUc : Continuous U := (continuous_const.mul (u_cont ε u hu)).mul continuous_const
  have hint : ∀ F : GL (Fin n) k → ℂ, Continuous F → HasCompactSupport F → ∀ z w : GL (Fin n) k,
      Integrable (fun X => F (z * U X * w)) μ := by
    intro F hFc hFs z w
    have hc : Continuous fun X => F (z * U X * w) :=
      hFc.comp ((continuous_const.mul hUc).mul continuous_const)
    obtain ⟨D, hD, hDX⟩ := slice_compact ε u hu h z w (tsupport F) hFs.isCompact
    refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hD fun X hX => ?_)
    exact image_eq_zero_of_notMem_tsupport fun hm => hX (hDX X hm)
  let e : GL (Fin n) k → ℂ := fun g => if hg : g ∈ J then (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ) else 0
  have he1 : ∀ g (hg : g ∈ J), e g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ) := fun g hg => dif_pos hg
  have he0 : ∀ g, g ∉ J → e g = 0 := fun g hg => dif_neg hg
  have hne : ∫ X, e (1 * U X * 1) ∂μ ≠ 0 := by
    let W : Set (Fin a → Fin b → k) := U ⁻¹' (J : Set (GL (Fin n) k))
    have hWo : IsOpen W := hJo.preimage hUc
    have h0 : (0 : Fin a → Fin b → k) ∈ W := by
      show U 0 ∈ J
      simp only [U, u_zero ε u hu, mul_one, inv_mul_cancel]
      exact J.one_mem
    have hpos : 0 < μ W := hWo.measure_pos μ ⟨0, h0⟩
    obtain ⟨D, hD, hDX⟩ := slice_compact ε u hu h 1 1 J hJc
    have hfin : μ W < ⊤ := lt_of_le_of_lt (measure_mono fun X hX => hDX X (by simpa [U, W] using hX)) hD.measure_lt_top
    have heq : (fun X => e (1 * U X * 1)) = W.indicator fun _ => (1 : ℂ) := by
      funext X
      by_cases hX : X ∈ W
      · have hX' : U X ∈ J := hX
        rw [Set.indicator_of_mem hX]
        simp only [one_mul, mul_one]
        rw [he1 _ hX']
        have := hcon X hX'
        show (((χ ⟨h⁻¹ * u X * h, hX'⟩)⁻¹ : ℂˣ) : ℂ) = 1
        rw [this]
        simp
      · have hX' : U X ∉ J := hX
        rw [Set.indicator_of_notMem hX]
        simp only [one_mul, mul_one]
        exact he0 _ hX'
    rw [heq, integral_indicator_const _ hWo.measurableSet]
    have hr : μ.real W ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨hpos.ne', hfin.ne⟩
    simpa using hr
  obtain ⟨σ, v, hv0, hχv, hσ⟩ := core μ U hint J hJo hJc χ hχ e he1 he0 hne
  let σ' : GlobalTheory.CuspRep.SmIrr (GL (Fin n) k) := ⟨σ.V, σ.ρ, σ.smooth, σ.irr⟩
  have hc : GlobalTheory.SmGL.IsCuspidal σ.ρ := hcusp σ' v hv0 hχv
  have hKo : IsOpen ((χ.ker.map J.subtype : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
    rw [Subgroup.coe_map]
    exact hJo.isOpenMap_subtype_val _ hχ
  have hKc : IsCompact ((χ.ker.map J.subtype : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
    refine hJc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) ?_
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hfix : ∀ g ∈ χ.ker.map J.subtype, σ.ρ g v = v := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : χ y = 1 := hy
    have := hχv y
    rw [h1] at this
    simpa using this
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : Module.Dual ℂ σ.V, l₀ v ≠ 0 := by
    by_contra H
    push_neg at H
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 H)
  obtain ⟨l, hl, hlv⟩ := GlobalTheory.SuperCusp.exists_smooth_form_eq (N := ⊥) σ.smooth hKo hKc 1
    ((χ.ker.map J.subtype : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) (fun c hc => hc)
    (fun g hg => ⟨1, Subgroup.one_mem _, g, hg, by simp⟩) (fun c hc => by simpa using hc) hfix l₀
    (fun x hx y => by rw [Subgroup.mem_bot.1 hx]; simp)
  have hl1 : l v ≠ 0 := by
    have := hlv 0
    simp only [pow_zero, map_one, Module.End.one_apply] at this
    rwa [this]
  let c : GL (Fin n) k → ℂ := fun g =>
    if ValuativeRel.valuation k (g : Matrix (Fin n) (Fin n) k).det = 1 then l (σ.ρ g v) else 0
  obtain ⟨hlc, hcs, K0, K0o, -, hbi, hz⟩ := GlobalTheory.CuspCutCoef.isCuspFn_cutCoef k n σ.V σ.ρ hc v l hl c (fun _ => rfl)
  let f : GL (Fin n) k → ℂ := fun g => starRingEnd ℂ (c g)
  have hfc : Continuous f := Complex.continuous_conj.comp hlc.continuous
  have hfs : HasCompactSupport f := hcs.comp_left (map_zero _)
  let K₂ : Subgroup (GL (Fin n) k) := χ.ker.map J.subtype ⊓ K0
  have hK₂o : IsOpen (K₂ : Set (GL (Fin n) k)) := by
    rw [Subgroup.coe_inf]
    exact hKo.inter K0o
  have hcR : ∀ g, ∀ y ∈ K₂, c (g * y) = c g := by
    intro g y hy
    have := hbi 1 K0.one_mem y hy.2 g
    rwa [one_mul] at this
  have hfR : ∀ g, ∀ y ∈ K₂, f (g * y) = f g := fun g y hy => by
    simp only [f, hcR g y hy]
  have hfZ : ∀ z w : GL (Fin n) k, ∫ X, f (z * U X * w) ∂μ = 0 := by
    intro z w
    have h1 : ∀ X, z * U X * w = (z * w) * ((h * w)⁻¹ * u X * (h * w)) := fun X => by
      simp only [U]
      group
    simp only [f, h1]
    rw [integral_conj, hz a b ε ha hb μ inferInstance u hu (z * w) (h * w), map_zero]
  have hfin := finite_cosets K₂ hK₂o f hfs
  let q₁ : GL (Fin n) k ⧸ K₂ := ((1 : GL (Fin n) k) : GL (Fin n) k ⧸ K₂)
  let Sf : Finset (GL (Fin n) k ⧸ K₂) := insert q₁ hfin.toFinset
  have hoff : ∀ q, q ∉ Sf → f q.out = 0 := by
    intro q hq
    by_contra h0
    exact hq (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 h0))
  have hsum := hσ K₂ inf_le_left hK₂o f hfc hfs hfR hfZ l Sf hoff
  have hterm : ∀ q : GL (Fin n) k ⧸ K₂, f q.out * l (σ.ρ q.out v) = ((‖c q.out‖ ^ 2 : ℝ) : ℂ) := by
    intro q
    by_cases hd : ValuativeRel.valuation k ((q.out : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det = 1
    · have hcq : c q.out = l (σ.ρ q.out v) := if_pos hd
      simp only [f]
      rw [hcq, Complex.conj_mul']
      push_cast
      rfl
    · have hcq : c q.out = 0 := if_neg hd
      simp only [f]
      rw [hcq]
      simp
  simp only [hterm] at hsum
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hsum
  have h1 := hsum q₁ (Finset.mem_insert_self _ _)
  have h2 : c q₁.out = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h1
    exact norm_eq_zero.1 this
  have h3 : c q₁.out = c 1 := by
    have hmem : q₁.out ∈ K₂ := by
      have : ((q₁.out : GL (Fin n) k) : GL (Fin n) k ⧸ K₂) = ((1 : GL (Fin n) k) : GL (Fin n) k ⧸ K₂) := QuotientGroup.out_eq' q₁
      have h5 : (q₁.out)⁻¹ * 1 ∈ K₂ := QuotientGroup.eq.1 this
      rw [mul_one] at h5
      exact K₂.inv_mem_iff.1 h5
    have := hcR 1 _ hmem
    rwa [one_mul] at this
  have h4 : c 1 = l v := by
    simp [c]
  exact hl1 (by rw [← h4, ← h3, h2])

end UpperTheory.Gal.Spc
end
end

theorem UpperTheory.Gal.Spc.cuspIrr_kFinite_rep_eq_centralCuspForm :
    UpperTheory.Gal.Spc.AdmCusp := by
  intro X _ k _ _ _ _ _ _ _ n Ty hJo hJc hker hcusp f hf h hh
  have hform : ∀ g, f (Ty.L.loc g * h) = UpperTheory.Gal.W2.Seed.tyFn Ty.J Ty.ψ g * f h := by
    intro g
    unfold UpperTheory.Gal.W2.Seed.tyFn
    split_ifs with hg
    · rw [Ty.L.comm g h hh]
      exact hf.2.2 ⟨g, hg⟩ h
    · rw [zero_mul]
      by_contra hne
      apply hg
      have hmem := hf.2.1 _ hne
      rwa [map_mul, Ty.L.pr_loc, hh, mul_one] at hmem
  have hTC : GlobalTheory.Block5c.TypeCusp := GlobalTheory.typeFunction_constantTerm_eq_zero
  have hT := hTC k (Fin n) Ty.J hJo hJc Ty.ψ hker
    (fun a b e ha hb u hu h₀ =>
      UpperTheory.Gal.Spc.typeSlice k n Ty.J hJo hJc Ty.ψ hker hcusp a b e ha hb u hu h₀)
    (UpperTheory.Gal.W2.Seed.tyFn Ty.J Ty.ψ)
    (fun g hg => by simp [UpperTheory.Gal.W2.Seed.tyFn, hg])
    (fun g hg => by simp [UpperTheory.Gal.W2.Seed.tyFn, hg])
  intro a b ε ha hb μ hμ u hu g₀ h₀
  have hz := hT.2.2.2 a b ε ha hb μ hμ u hu g₀ h₀
  simp_rw [hform]
  rw [MeasureTheory.integral_mul_const, hz, zero_mul]
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem conv_add_r {X : Type} [Group X] {K : Subgroup X} (hK : Formalism.UG.IsCommensurated K) {e : X → ℂ}
    (he : e ∈ Hecke ℂ K) (f f' : X → ℂ) : conv K e (f + f') = conv K e f + conv K e f' := by
  have hs := Formalism.UG.P.finite_support_cosets hK ((Formalism.UG.P.mem_hecke_iff ℂ K e).1 he).2
  funext x
  have hsub : ∀ (φ : X → ℂ), (Function.support fun q : X ⧸ K => e q.out * φ (q.out⁻¹ * x)).Finite := fun φ =>
    hs.subset fun q hq => left_ne_zero_of_mul hq
  simp only [conv, Pi.add_apply, mul_add]
  exact finsum_add_distrib (hsub f) (hsub f')

private theorem conv_smul_r {X : Type} [Group X] (K : Subgroup X) (e : X → ℂ) (c : ℂ) (f : X → ℂ) :
    conv K e (c • f) = c • conv K e f := by
  funext x
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  refine (finsum_congr fun q => mul_left_comm _ _ _).trans ?_
  simpa only [smul_eq_mul] using (smul_finsum c fun q : X ⧸ K => e q.out * f (q.out⁻¹ * x)).symm

private theorem span_fix {X : Type} [Group X] {K : Subgroup X} (hK : Formalism.UG.IsCommensurated K) {e : X → ℂ}
    (he : e ∈ Hecke ℂ K) (s : Set (X → ℂ)) (hs : ∀ f ∈ s, conv K e f = f) :
    ∀ f ∈ Submodule.span ℂ s, conv K e f = f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hs f hf
  | zero => funext x; simp [conv]
  | add f f' _ _ h h' => rw [conv_add_r hK he, h, h']
  | smul c f _ h => rw [conv_smul_r, h]

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.specData :
    UpperTheory.Gal.Int.Geo.Pl.WtOf → UpperTheory.Gal.Spc.SpecData := by
  intro hWt
  unfold UpperTheory.Gal.Spc.SpecData UpperTheory.Gal.Spc.ForData
  intro E _ _ _ A n p _ S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy hEx J g θ hseen
  obtain ⟨⟨Lv, hLv⟩, ⟨Kw, hKwo, hKwc, hKwF⟩, hJo, hJc, hker, hcusp⟩ :=
    UpperTheory.Gal.Spc.tyTop E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  obtain ⟨u, hu, u', hu', heu, hue, hinv, hcomm, hX⟩ :=
    UpperTheory.Gal.Spc.auxFn E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  have hmem := UpperTheory.Gal.Spc.memFn E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  have hmc := UpperTheory.Gal.Spc.memComm E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  obtain ⟨thQ, hthQ, hEig⟩ :=
    UpperTheory.Gal.Spc.eigEx E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  have hLK : Lv.K.toSubgroup = Ty.K₀ := hLv.trans hTy.K₀_eq.symm
  have hid : TfIdem := pTfIdem pTfAdm (pTfCen pAvgK pTfAdm)
  have hAdm1 : Ty.admitted (Ty.tf 1) := (pTfAdm _ _ Ty 1 (map_one _)).1
  have he : Ty.tf 1 ∈ Hecke ℂ Ty.K₀ := hAdm1.1
  have hψ : ∀ j, (g j).fn ∈ Hecke ℂ Ty.K₀ := fun j => (hmem (g j) (θ j) (hseen j)).1
  have hring := pConvRing _ Ty.K₀ Ty.cms
  have hoff : ∀ f ∈ Off2 W L Ty, conv Ty.K₀ (Ty.tf 1) f = f := by
    refine UpperTheory.Gal.Spc.span_fix Ty.cms he _ ?_
    rintro f ⟨h, hh, -, rfl⟩
    exact (hid _ _ Ty h hh).2.2
  have hrel : Rel (conv Ty.K₀) (fun j => (g j).fn) (Ty.tf 1) u u' :=
    { idem := (hid _ _ Ty 1 (map_one _)).2.1
      eT := fun j => hoff _ (hmc (g j) (g j) (θ j) (θ j) (hseen j) (hseen j)).1
      eu := by rw [hue, heu]
      TT := fun j j' => (hmc (g j) (g j') (θ j) (θ j') (hseen j) (hseen j')).2
      uT := fun j => by
        show conv Ty.K₀ u (conv Ty.K₀ (g j).fn (Ty.tf 1)) = conv Ty.K₀ (g j).fn (conv Ty.K₀ u (Ty.tf 1))
        rw [hcomm _ (hmc (g j) (g j) (θ j) (θ j) (hseen j) (hseen j)).1, hue,
          (hring _ (hψ j) _ he).2 u hu, heu]
      inv := by rw [hue]; exact hinv }
  obtain ⟨w₁, hw₁⟩ := hAux.nonempty
  obtain ⟨P₁, hP₁⟩ := hEx.1 w₁.1 w₁.2.2
  obtain ⟨P, hP⟩ := hEx.1 w₀ hw.2
  have hfac₀ : ∀ y, Ty.L.pr (F.j y) = comp w₀ y := by
    intro y
    rw [hTy.L_eq]
    exact (hTy.fac ⟨w₀, hw⟩).1 y
  have hcont : Continuous Ty.L.pr := by
    rw [hTy.L_eq]
    exact UpperTheory.Gal.Spc.facCont E A n p S F ⟨w₀, hw⟩ _ (hTy.fac ⟨w₀, hw⟩)
  have hat : ∀ y, P.at y = (Ty.L.pr y : Matrix (Fin n) (Fin n) (w₀.adicCompletion E)) := by
    intro y
    obtain ⟨y', rfl⟩ := F.surj y
    rw [hP, hfac₀]
  letI : MeasurableSpace (w₀.adicCompletion E) := borel _
  haveI : BorelSpace (w₀.adicCompletion E) := ⟨rfl⟩
  obtain ⟨τ, hτ, hτ2, Sp, hSp⟩ := UpperTheory.Gal.Spc.splitC p S.G Lv (w₀.adicCompletion E) P Ty.L hcont hat Kw hKwo hKwc
    (by rw [hLK]; exact hKwF)
  have hCe : Sp.Cusp (Ty.tf 1) := by
    intro h
    have h0 := UpperTheory.Gal.Spc.cuspIrr_kFinite_rep_eq_centralCuspForm S.G.GAf (w₀.adicCompletion E) n Ty hJo hJc hker hcusp (Ty.tf 1) hAdm1 h.1 h.2
    have h1 : (fun y => Ty.tf 1 (Sp.e.symm (y, h))) = fun y => Ty.tf 1 (Ty.L.loc y * h.1) :=
      funext fun y => by rw [hSp]; rfl
    rw [h1]
    exact h0
  have hA : ∀ m : ℕ, 1 ≤ m → ∃ A' : Set S.G.GAf,
      (∀ y ∈ A', (P₁.at y).charpoly.Separable ∧ GlobalTheory.LKCx.RegAf S.G y) ∧
      (∀ j a, (g j).fn a ≠ 0 → ∀ y ∈ A', a * y ∈ A') ∧
      ∀ y, powFn Lv.K.toSubgroup u (Ty.tf 1) m y ≠ 0 → y ∈ A' := by
    intro m hm
    obtain ⟨X, hX1, hX2⟩ := hX m hm
    refine ⟨{y | ∀ w ∈ W, (L w).pr y ∈ X w}, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨y', rfl⟩ := F.surj y
      have hsep : ∀ w ∈ W, (comp w.1 y').val.charpoly.Separable := fun w hw' => by
        have h := (hX1 w hw' _ (hy w hw')).1
        rwa [(hTy.fac w).1] at h
      refine ⟨?_, hEx.2 r hAux.prime hAux.ne y' ?_⟩
      · rw [hP₁]
        exact hsep w₁ hw₁
      · intro v hv
        obtain ⟨w, hwW, rfl | rfl⟩ := hAux.half.all v hv
        · exact hsep w hwW
        · exact UpperTheory.Gal.Spc.sepConj E n y' w.1 (hsep w hwW)
    · intro j a ha y hy w hw'
      rw [map_mul]
      exact (hX1 w hw' _ (hy w hw')).2 _ ((hmem (g j) (θ j) (hseen j)).2.1 a ha w hw')
    · intro y hy
      rw [hLK] at hy
      exact (hX2 y hy).2
  have hso : UpperTheory.Gal.Spc.SpecOfF := UpperTheory.Gal.Spc.specOfF
  unfold UpperTheory.Gal.Spc.SpecOfF UpperTheory.Gal.Spc.ForPlaces at hso
  have hso' := @hso p _ S.G (pSetupBasic E A n p S).1 Lv (w₀.adicCompletion E) _ _ _ _ _ _ _ P Ty.L.pr.ker _ τ hτ hτ2 Sp
    (w₁.1.adicCompletion E) _ _ P₁ (UpperTheory.Gal.G1.FinCls_holds E A n p S)
  have key := hso'
    S.D S.L V.lam (Module.Dual ℂ V.W.Sp) ((UpperTheory.Gal.CertificateRingHomMap.xi V.W V.jz).comp thQ) (hWt E A n p S x U w₀ Up V thQ hthQ)
    J (fun j => (g j).fn) θ (Ty.tf 1) u u' (by rw [hLK]; exact hψ) (by rw [hLK]; exact he) (by rw [hLK]; exact hu)
    (by rw [hLK]; exact hu') (by rw [hLK]; exact hrel) hCe hA
    (by rw [hLK]; exact hEig J g θ hseen)
  obtain ⟨m, hm, hspec⟩ := key
  have hW := (UpperTheory.Gal.Spc.words p S.G Lv J (fun j => (g j).fn) (Ty.tf 1) u u' (by rw [hLK]; exact hψ)
    (by rw [hLK]; exact he) (by rw [hLK]; exact hu) (by rw [hLK]; exact hrel) m).1
  obtain ⟨X, -, hX2⟩ := hX m hm
  rw [hLv] at hspec hW
  refine ⟨_, ⟨hW, fun y hy => ?_⟩, hspec⟩
  rw [← hTy.K₀_eq] at hy
  exact (hX2 y hy).1

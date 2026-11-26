module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasLevW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsIntegralCoeffCof
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open Formalism.IndefR.Cx
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftTheta

section Core

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {N H : Type} [AddCommGroup N] [Module ℂ N] [AddCommGroup H] [Module ℂ H]

omit [NumberField K] in
theorem semi_expand {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) : w y = ∑ k, σ (y k) • w (Pi.single k 1) := by
  have hz : y = ∑ k, y k • (Pi.single k 1 : Fin d → K) := by
    ext i; simp [Pi.single_apply]
  conv_lhs => rw [hz]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ]

omit [NumberField K] in
theorem semi_injective {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (hli : LinearIndependent ℂ fun k => w (Pi.single k 1)) :
    Function.Injective w := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand] at hy
  funext k
  exact (map_eq_zero σ).1 (Fintype.linearIndependent_iff.1 hli _ hy k)


theorem oLatTie_of_closure {O : Type} [CommRing O] {φ : O →+* ℂ} (hφ : ∀ a, ∃ b : 𝓞 K, φ a = σ (b : K))
    (M : Rows.OLat O φ N) {d : ℕ} (e : N →ₗ[ℂ] H) (he : Function.Injective e) (j : (Fin d → K) →ₛₗ[σ] N)
    (hj : Function.Injective j) (L : Submodule (𝓞 K) (Fin d → K)) (S : Set H) (hS : ∀ y, y ∈ S ↔ ∃ x ∈ L, e (j x) = y)
    (h : AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x}) :
    OLatTie σ M j L := by
  classical
  have hR : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x} ↔ ∃ x ∈ L, e (j x) = y := by
    intro y
    refine ⟨fun hy => ?_, fun hy => AddSubgroup.subset_closure ⟨1, y, (hS y).2 hy, by simp⟩⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, u, hu, rfl⟩ := hy
      obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
      refine ⟨a • x, L.smul_mem a hx, ?_⟩
      rw [← algebraMap_smul K a x, map_smulₛₗ, map_smul]
    | zero => exact ⟨0, L.zero_mem, by simp⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨x, hx, rfl⟩ := h1
      obtain ⟨x', hx', rfl⟩ := h2
      exact ⟨x + x', L.add_mem hx hx', by simp⟩
    | neg _ _ h1 =>
      obtain ⟨x, hx, rfl⟩ := h1
      exact ⟨-x, L.neg_mem hx, by simp⟩
  have hgen : ∀ v ∈ M.gen, v ∈ M.carrier := by
    intro v hv
    refine ⟨fun u => if u = v then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      simp [hu]
    · intro h; exact absurd hv h
  have hL : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} ↔
      ∃ c : N → 𝓞 K, y = e (∑ v ∈ M.gen, σ (c v : K) • v) := by
    intro y
    constructor
    · intro hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, _, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩ := hy
        choose b hb using hφ
        refine ⟨fun v => a * b (c v), ?_⟩
        rw [← map_smul, Finset.smul_sum]
        simp [hb, mul_smul]
      | zero => exact ⟨0, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨c, rfl⟩ := h1
        obtain ⟨c', rfl⟩ := h2
        refine ⟨c + c', ?_⟩
        rw [← map_add (f := _), ← Finset.sum_add_distrib]
        simp [add_smul]
      | neg _ _ h1 =>
        obtain ⟨c, rfl⟩ := h1
        refine ⟨-c, ?_⟩
        rw [← map_neg, ← Finset.sum_neg_distrib]
        simp
    · rintro ⟨c, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine AddSubgroup.sum_mem _ fun v hv => AddSubgroup.subset_closure ⟨c v, e v, ⟨v, hgen v hv, rfl⟩, map_smul _ _ _⟩
  refine ⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : e v ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} :=
      AddSubgroup.subset_closure ⟨1, e v, ⟨v, hgen v hv, rfl⟩, by simp⟩
    rw [h, hR] at h1
    obtain ⟨x, -, hx⟩ := h1
    exact ⟨x, he hx⟩
  · have h1 := (hR _).2 ⟨x, hx, rfl⟩
    rw [← h, hL] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, he hc⟩
  · rintro ⟨c, hc⟩
    have h1 := (hL (e (j x))).2 ⟨c, congrArg e hc⟩
    rw [h, hR] at h1
    obtain ⟨x', hx', hxx⟩ := h1
    rwa [← hj (he hxx)]

omit [NumberField K] in
theorem lin_cpt {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) :
    lin (fun k => w (Pi.single k 1)) (cpt σ y) = w y := (semi_expand w y).symm

end Core

section Lift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem liftMatrix_computes_lift_rational (h5 : X.H5 cr b) (hr : X.RATth cr b) (j : Bs.J) (t : Bs.Tup) (z : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.w0C b j (cpt Bs.v0.embedding (X.liftMat cr b j t *ᵥ z)) = X.θ' j t (X.jL j t (cr.toL X.zs b j t z)) :=
  (X.key_lift cr b h5 hr j t z).trans (lin_cpt (((X.θ' j t).comp (X.jL j t)).comp (cr.toL X.zs b j t)) z)

end Lift

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (R : RealDat D A Ks) (F : Face D A)

def goodForm (b : Bool) (i : Fin D.R.m) :
    (Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] (R.HW i (sg0 D A)).H where
  toFun y := (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k)
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' a y := by
    have h : sg0 D A a = D.what₂.embLL a := by rw [sg0, sgAt_mk _ R.hv0]
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smulₛₗ, h]

theorem goodForm_apply (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    goodForm R F b i y = (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k) := rfl

theorem goodForm_single (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    goodForm R F b i (Pi.single k 1) = (R.FW i).j (sg0 D A) (R.bL F b i k) := by
  rw [goodForm_apply]
  congr 1
  simp [Pi.single_apply]

theorem goodForm_li (hU : R.LUnif) (b : Bool) (i : Fin D.R.m) :
    LinearIndependent ℂ fun k => goodForm R F b i (Pi.single k 1) := by
  simp only [goodForm_single]
  exact (hU i _).1 _ _
    ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))

theorem sqrt_ne (b : Bool) : ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) ≠ 0 := by
  have := Real.sqrt_pos.2 (RealDat.nP_pos (F := F) b)
  exact_mod_cast this.ne'

theorem smul_bC (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) • R.bC F b i (sg0 D A) k = goodForm R F b i (Pi.single k 1) := by
  rw [goodForm_single, RealDat.bC, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

theorem goodForm_span (b : Bool) (i : Fin D.R.m) :
    Submodule.span ℂ (Set.range fun k => goodForm R F b i (Pi.single k 1)) = R.WS F b i (sg0 D A) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    rw [← smul_bC]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [RealDat.WS, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ (sqrt_ne F b), smul_bC]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem mem_image_iff (b : Bool) (i : Fin D.R.m) (y : (R.HW i (sg0 D A)).H) :
    y ∈ (R.FW i).j (sg0 D A) '' ((R.FW i).Mj (F.lvl b).P (F.lvl b).ψ⁻¹ (fun g => (idemOf A.X).coeff g) : Set _) ↔
      ∃ x ∈ (R.toCx F).M b i, goodForm R F b i x = y := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hW : f ∈ R.WL F b i := (R.FW i).Mj_sub_Wgood _ _ _ hf
    have hs : ∑ k, (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k • R.bL F b i k = f := by
      have h := congrArg (R.WL F b i).subtype ((Module.finBasis D.what₂.LL (R.WL F b i)).sum_repr ⟨f, hW⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      exact h
    refine ⟨fun k => (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k, ((R.FW i).mem_Mcoord _ _ _ _ _).2 ?_, ?_⟩
    · rw [hs]; exact hf
    · exact congrArg ((R.FW i).j (sg0 D A)) hs
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ((R.FW i).mem_Mcoord _ _ _ _ _).1 hx, rfl⟩

theorem liftWeight_complexPoint_eq_twist (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    (R.toCx F).w0C b i (cpt A.v0.embedding y) = Tw.mk (twAt D.what₂.embLL A.v0) (goodForm R F b i y) := by
  have h1 : (R.toCx F).w0C b i = lin fun k => Tw.semi _ R.emb0 (goodForm R F b i) (Pi.single k 1) := by
    rw [← lin_basis ((R.toCx F).w0C b i)]
    congr 1
    funext k
    exact (congrArg ((R.toCx F).eW b i) (lin_single _ k)).trans (smul_bC R F b i k)
  rw [h1]
  exact lin_cpt (Tw.semi _ R.emb0 (goodForm R F b i)) y

theorem levelFormCoordinateMap_levelZero {s : ℕ} (hOk : A.fam.Ok s) (Zs : DefSub A.fam.amb) (i : Fin D.R.m) (t : T)
    (z : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) (Zs.Zl i t)) → D.what₂.LL) :
    LiftForms.lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ
      (lZ0 D A F.P0 F.ψ0 Zs i t *ᵥ z) = F.cr.toL Zs false i t z :=
  LiftForms.lvlForm_lE (v0 := A.v0) (s := s) ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ z


end Main

end GlobalTheory.Mem.LiftTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarIsMulRightInvariant
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology Matrix
open scoped ENNReal

namespace GlobalTheory.SmGL.UnipHaar

section Algebra

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)

theorem det_rmat_unip (u : unipRad R e) : (rmat e ((u : GL n R) : Matrix n n R)).det = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 u.2
  rw [← det_transpose, det_of_blocks (rmat e _)ᵀ (fun p => blk e p.1.2) ?_
    (fun a => {j : n // blk e j < a}) (fun _ => 1) (colEquiv e) ?_]
  · simp
  · intro p q h
    have h3 : ((u : GL n R) : Matrix n n R).BlockTriangular (blk e) := h1
    simp [rmat, h3 h]
  · intro a x y
    exact if_congr (eq_comm.trans Subtype.ext_iff.symm) (h2 a x.1 y.1) rfl

theorem unipEquiv_mul_right (u : unipRad R e) (x : Idx e → R) :
    unipEquiv e ((unipEquiv e).symm x * u) =
      unipEquiv e u + (rmat e ((u : GL n R) : Matrix n n R)).mulVec x := by
  rw [← ent_mat_mul]
  show ent e ((1 + mat e x) * ((u : GL n R) : Matrix n n R)) = _
  rw [add_mul, one_mul]
  rfl

end Algebra

section Measure

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem isMulRightInvariant_map :
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν)).IsMulRightInvariant := by
  haveI := secondCountable k
  haveI := t2Space k
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  refine ⟨fun u => ?_⟩
  have hm : Measurable (rmat e ((u : GL n k) : Matrix n n k)).mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have h1 := WeilM.smul_map_mulVec_pi ν _ 1 (det_rmat_unip e u).symm
  rw [map_one, ENNReal.coe_one, one_smul] at h1
  have h2 : (· * u) ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ ((unipEquiv e u + ·) ∘
      (rmat e ((u : GL n k) : Matrix n n k)).mulVec) :=
    funext fun x => (unipEquiv e).eq_symm_apply.2 (unipEquiv_mul_right e u x)
  rw [Measure.map_map (measurable_mul_const u) hΦ, h2,
    ← Measure.map_map hΦ ((measurable_const_add _).comp hm),
    ← Measure.map_map (measurable_const_add _) hm, h1, map_add_left_eq_self]

end Measure

theorem haar_isMulRightInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] (μ : Measure (unipRad k e)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e _ _ μ _
  borelize k
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace (unipRad k e) := (unipHomeo e).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k e) := (unipHomeo e).secondCountableTopology
  haveI := isHaarMeasure_map e (Measure.addHaar : Measure k)
  haveI := isMulRightInvariant_map e (Measure.addHaar : Measure k)
  rw [Measure.isMulLeftInvariant_eq_smul μ
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => (Measure.addHaar : Measure k)))]
  infer_instance

end GlobalTheory.SmGL.UnipHaar
end
end

noncomputable section

open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.LocLanglands.InvInt

section General

variable {G : Type} [Group G] (H : Subgroup G)

def descend : (G → ℂ) →ₗ[ℂ] (G ⧸ H → ℂ) where
  toFun f q := f (q.out)⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {H}

theorem descend_mk {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (g : G) :
    descend H f (g : G ⧸ H) = f g⁻¹ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  show f ((g : G ⧸ H).out)⁻¹ = _
  rw [hh, mul_inv_rev]
  exact hf _ (H.inv_mem h.2) _

theorem descend_mul_right {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (x : G) :
    descend H (fun g => f (g * x)) = fun q => descend H f (x⁻¹ • q) := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk (fun u hu g => by rw [mul_assoc, hf u hu]), MulAction.Quotient.smul_mk, descend_mk hf]
  simp

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_descend {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (hc : Continuous f) :
    Continuous (descend H f) := by
  refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr ?_
  have : descend H f ∘ QuotientGroup.mk = fun g => f g⁻¹ := funext (descend_mk hf)
  rw [this]
  exact hc.comp continuous_inv

theorem hasCompactSupport_descend [T2Space (G ⧸ H)] {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g)
    {C : Set G} (hC : IsCompact C) (hs : ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) :
    HasCompactSupport (descend H f) := by
  refine HasCompactSupport.intro (hC.inv.image QuotientGroup.continuous_mk) fun q hq => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk hf]
  by_contra h
  obtain ⟨u, hu, c, hc, e⟩ := hs _ h
  refine hq ⟨c⁻¹, by simpa using hc, QuotientGroup.eq.2 ?_⟩
  have : g = c⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← e, inv_inv]
  rw [this]
  simpa using hu

end General

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j, Continuous fun g : GL (Fin m) k => g.val i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin m) k | g.val i j = 0}) ∩ ⋂ i, {g : GL (Fin m) k | g.val i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_eq (hc _ _) continuous_const).inter (isClosed_iInter fun _ => isClosed_eq (hc _ _) continuous_const)

end GlobalTheory.LocLanglands.InvInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubst

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex GlobalTheory.Ker.FockAlg

section Generic

variable {ι X : Type} {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {κ : Type} [Fintype κ] (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    (hA' : ∀ i f, P f → P (A' i f)) (hc' : ∀ i j f, P f → A' i (A' j f) = A' j (A' i f))
    (Aadd' : ∀ i f f', P f → P f' → A' i (f + f') = A' i f + A' i f')
    (Asm' : ∀ i (a : ℂ) f, P f → A' i (a • f) = a • A' i f)
    (c : ι → κ → ℂ) (r : ι → κ → ι) (h : ∀ i f, P f → A' i f = ∑ b, c i b • A (r i b) f)
    {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' f Q = pureTensorL A f
      (MvPolynomial.aeval (fun v : ι => ∑ b, c v b • (MvPolynomial.X (r v b) : MvPolynomial ι ℂ)) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), MvPolynomial.C_mul',
      map_smul, map_smul, pure_one, pure_one]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm, pure_X_mul hadd hsm hA' hc' Aadd' Asm' hf, hp, h _ _ (pure_mem hadd hsm hA hf _), map_mul,
      MvPolynomial.aeval_X, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_assoc, map_smul, pure_X_mul hadd hsm hA hc Aadd Asm hf]

end Generic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
  (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) (t : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)

include hψ hθ hf

theorem dRho_csmul (w : ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (w • u) f =
      (w.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ u f + (w.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (I • u) f := by
  have e : w • u = (w.re : ℂ) • u + (w.im : ℂ) • (I • u) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (dRho_laws hψ hθ hf τ _).2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_dir_add (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (z + z') f =
      aPlus (heisO ψ S T) θ τ (cplxO s t) z f + aPlus (heisO ψ S T) θ τ (cplxO s t) z' f := by
  simp only [aPlus_eq, GlobalTheory.OrientedRealForm.cplxO_add, fun z => (dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem aPlus_dir_zero : aPlus (heisO ψ S T) θ τ (cplxO s t) 0 f = 0 := by
  have := aPlus_dir_add hψ hθ τ s t hf 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem aPlus_dir_sum {κ : Type} (F : Finset κ) (z : κ → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (∑ b ∈ F, z b) f = ∑ b ∈ F, aPlus (heisO ψ S T) θ τ (cplxO s t) (z b) f := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using aPlus_dir_zero hψ hθ τ s t hf
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, aPlus_dir_add hψ hθ τ s t hf, ih]

theorem aPlus_dir_smul (e : Bool) (w : ℂ) {u : Matrix (Fin T.rank) (Fin S.rank) ℂ}
    (hu : cplxO s t u = ((if e then 1 else -1 : ℂ) * I) • u) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (w • u) f =
      (if e then w else starRingEnd ℂ w) • aPlus (heisO ψ S T) θ τ (cplxO s t) u f := by
  have h1 : cplxO s t (w • u) = (w * ((if e then 1 else -1 : ℂ) * I)) • u := by
    rw [← smul_smul, ← hu]
    unfold cplxO
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  rw [aPlus_eq, aPlus_eq, h1, hu, dRho_csmul hψ hθ τ hf w, dRho_csmul hψ hθ τ hf (w * _),
    dRho_csmul hψ hθ τ hf (_ * I)]
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, w = x + y * I := ⟨w.re, w.im, (Complex.re_add_im w).symm⟩
  cases e
  · simp only [Bool.false_eq_true, if_false, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
    match_scalars <;> simp <;> ring_nf <;> simp
  · simp only [if_true]
    match_scalars <;> simp <;> ring_nf <;> simp

omit hψ hθ hf

theorem unitMap_mul {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (a : Fin m)
    (j : Fin n) : unitMap B (B' * k) a j = ∑ b, k b a • unitMap B B' b j := by
  have e : k * single a j (1 : ℂ) = ∑ b, k b a • single b j (1 : ℂ) := by
    ext p q
    by_cases h : j = q
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, h]
  unfold unitMap
  rw [Matrix.mul_assoc B', e, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxO_unitMap {S' : D.what₂.Tau → SPar} (M : DSModel T S') {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin T.rank) (j : Fin n) : cplxO 1 (cart M τ) (unitMap B (onb M τ) b j) =
      ((if M.ε τ b then 1 else -1 : ℂ) * I) • unitMap B (onb M τ) b j := by
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have e : Formalism.REAL.Jm (M.ε τ) * single b j (1 : ℂ) = (if M.ε τ b then 1 else -1 : ℂ) • single b j (1 : ℂ) := by
    ext p q
    rw [Formalism.REAL.Jm, diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases h : b = p
    · rw [h]
    · simp [h]
  unfold cplxO unitMap cart onb
  rw [Matrix.mul_one, mul_comm _ I, ← smul_smul]
  congr 1
  calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * single b j (1 : ℂ)) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one, e, Matrix.mul_smul, Matrix.smul_mul]

theorem kset_zero {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) {a b : Fin n}
    (h : ε b ≠ ε a) : k b a = 0 := by
  have e := congrFun (congrFun hk.2 b) a
  rw [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at h e <;> simp at e <;>
    first | linear_combination (1 / 2 : ℂ) * e | linear_combination (-1 / 2 : ℂ) * e

theorem pureTensorO_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (k c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → IsThetaFunO ψ S T f → (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ a b, c τ b a = if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (MvPolynomial.aeval (fun v : FVar D T.rank S.rank => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P) := by
  intro D ψ θ S T S' M BS f k c hψ hθ hS hf hk hc P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hA : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f f', IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T f' → aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (f + f') =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f +
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f' :=
    fun _ _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f :=
    fun _ _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i j f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j f) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ i j _ h => aPlus_comm (sS := fun _ => 1) (sT := cart M) hψ hθ i.1 _ hS hT j.1 _ h
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (fun τ => onb M τ * k τ) i g =
      ∑ b, c i.1 b i.2.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (i.1, b, i.2.2) g := by
    rintro ⟨τ, a, j⟩ g hg
    simp only [aPlusAll]
    rw [unitMap_mul, aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aPlus_dir_smul hψ hθ τ _ _ hg _ _ (cplxO_unitMap τ M _ b j), hc]
    by_cases h : M.ε τ b = M.ε τ a
    · rw [h]
    · rw [kset_zero (hk τ) h]
      simp
  unfold pureTensorO
  exact pure_subst (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (hA _) (Ac _) (Aadd _) (Asm _) (hA _) (Ac _) (Aadd _) (Asm _)
    (fun v b => c v.1 b v.2.1) (fun v b => (v.1, b, v.2.2)) key hf P

end GlobalTheory.FockSubst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitutStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_maximalCompact_basis_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (k c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → IsThetaFunO ψ S T f → (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ a b, c τ b a = if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (MvPolynomial.aeval (fun v : FVar D T.rank S.rank => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P) := by
  first | exact @GlobalTheory.FockSubst.pureTensorO_subst | exact GlobalTheory.FockSubst.pureTensorO_subst | (intros; apply GlobalTheory.FockSubst.pureTensorO_subst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
open scoped Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockIndep

section Mat

variable {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {H t B' : Matrix (Fin m) (Fin m) ℂ} {δ : Fin m → ℂ}

theorem trace_unitMap (hB : Bᴴ * G * B = 1) (hB' : B'ᴴ * H * B' = diagonal δ) (a c : Fin m) (b d : Fin n) :
    (G⁻¹ * (unitMap B B' c d)ᴴ * H * unitMap B B' a b).trace = if (a, b) = (c, d) then δ a else 0 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have hG : G⁻¹ = B * Bᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.mul_assoc]
    exact mul_eq_one_comm.1 (by rw [← Matrix.mul_assoc, hB])
  have h1 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, Matrix.nonsing_inv_mul _ hu, conjTranspose_one]
  have e : G⁻¹ * (unitMap B B' c d)ᴴ * H * unitMap B B' a b =
      B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.single c d (1 : ℂ))ᴴ * (B'ᴴ * H * B') * Matrix.single a b (1 : ℂ) * B⁻¹) := by
    simp only [hG, unitMap, conjTranspose_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hu, h1, hB', Matrix.one_mul,
    Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single, Matrix.diagonal_apply]
  by_cases h : c = a
  · subst h
    by_cases h' : d = b
    · subst h'; simp
    · simp [Matrix.trace_single_eq_of_ne _ _ _ h', Ne.symm h']
  · simp [h, Ne.symm h]

theorem cplxO_unitMap (ht : t * B' = B' * diagonal δ) (a : Fin m) (b : Fin n) :
    cplxO 1 t (unitMap B B' a b) = (Complex.I * δ a) • unitMap B B' a b := by
  have e : diagonal δ * Matrix.single a b (1 : ℂ) = δ a • Matrix.single a b (1 : ℂ) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    split_ifs with h
    · rw [h.1, smul_eq_mul]
    · simp
  rw [cplxO, unitMap, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ht, Matrix.mul_assoc B', e,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]

end Mat

theorem pureTensorO_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → IsThetaFunO ψ S T f → f ≠ 0 → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → Function.Injective (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f) := by
  intro D ψ θ S T S' M BS f hψ hθ hS hBS hf f0 hv
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hB' : ∀ τ, (onb M τ)ᴴ * gramAt D T τ * onb M τ = diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [← M.fr_gram τ, onb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hu τ), conjTranspose_one, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]
    rfl
  have ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]
    rfl
  unfold pureTensorO aPlusAll
  refine pure_injective (P := IsThetaFunO ψ S T)
    (B := fun k => annih (heisO ψ S T) θ k.1 (cplxO 1 (cart M k.1)) (unitMap (BS k.1) (onb M k.1) k.2.1 k.2.2))
    (c := fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * π * Complex.I) *
      (Complex.I * (-2 * (tauE D k.1 D.host.xi0).im : ℝ))))
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun a _ => GlobalTheory.OrientedHeis.theta_smul a)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf f0 ?_
  · exact fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  · exact fun _ _ h => annih_theta hψ hθ _ _ _ h
  · exact fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
  · exact fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  · exact fun _ _ _ h h' => annih_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => annih_smul hψ hθ _ _ _ a h
  · rintro ⟨τ, a, b⟩ ⟨τ', c, d⟩ g hg
    refine (annih_aPlus (sS := fun _ => 1) hψ hθ τ _ hS hT τ' _ hg).trans ?_
    refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
    unfold omDir
    by_cases h : τ = τ'
    · subst h
      simp only [if_true, cplxO_unitMap (ht τ), Matrix.mul_smul, Matrix.trace_smul, trace_unitMap (hB τ) (hB' τ),
        Prod.mk.injEq, true_and]
      have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
      split_ifs <;> simp [Complex.mul_re, hre]
    · simp [h]
  · intro i
    have him := xi_zero_im_pos D i.1
    have hn : 0 < ‖tauE D i.1 D.host.xi0‖ := norm_pos_iff.2 fun h => by simp [h] at him
    have hfs : 0 < fockScale D i.1 := by
      unfold fockScale
      have := Real.pi_pos
      positivity
    simp [hfs.ne', him.ne', Real.pi_ne_zero]
  · exact fun i => hv i.1 _

end GlobalTheory.FockIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVectors_injective_nonzero_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → IsThetaFunO ψ S T f → f ≠ 0 → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → Function.Injective (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f) := by
  first | exact @GlobalTheory.FockIndep.pureTensorO_injective | exact GlobalTheory.FockIndep.pureTensorO_injective | (intros; apply GlobalTheory.FockIndep.pureTensorO_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefMapRecord

open Formalism.L2.NTheta

lemma floor_toNat_cast {x : ℚ} (z : ℤ) (hz : x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  subst hz
  rw [Int.floor_intCast]
  have h : 0 ≤ z := by exact_mod_cast h0
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

lemma lamAt_b {R : Ranks} (h : HCParam R) (n c : ℕ) (hc : c < R.m) (hn : n = R.k - 1 + c) : lamAt h n = -h.b ⟨c, hc⟩ := by
  subst hn
  unfold lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 3
  omega

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

lemma aPl_cast (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) =
      lamAt (D.hc τ) n + (D.hc τ).e i - (((D.R.k + i : ℕ) : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) n
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  rw [aPl, if_pos hn]
  refine floor_toNat_cast (z + e - ((D.R.k + i : ℕ) - (n + 1)) - (s + 1)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hn
    have h1 := lamAt_add_add_le (D.hc τ) d n (by unfold Ranks.r; omega)
    rw [lamAt_b (D.hc τ) (n + d) i hi (by omega)] at h1
    have h2 := (D.hc τ).gap_be i
    rw [hd]
    push_cast
    simp only [Fin.eta] at h1
    linarith

lemma aMi_cast (q n c : ℕ) (hq : i + 1 + q = D.R.m) (hn : n + c + 1 = q) :
    (aMi D i (D.R.k + i) q τ n : ℚ) =
      -((D.hc τ).e i - (D.hc τ).b ⟨i + 1 + c, by omega⟩ + (c + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨i + 1 + c, by omega⟩
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have h0 := lamAt_b (D.hc τ) (D.R.k + i + c) (i + 1 + c) (by omega) (by omega)
  rw [aMi, if_pos (by omega), show q - n = c + 1 by omega, show D.R.k + i + (c + 1) - 1 = D.R.k + i + c by omega, h0,
    ← sub_eq_add_neg, Nat.cast_succ]
  refine floor_toNat_cast (-(e - z + (c + 1) + s)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · have h1 := lamAt_add_add_le (D.hc τ) c (D.R.k + i) (by unfold Ranks.r; omega)
    rw [h0, lamAt_b (D.hc τ) (D.R.k + i) (i + 1) (by omega) (by omega)] at h1
    have h2 := (D.hc τ).gap_eb i (by omega)
    linarith

lemma lamV_eq : ∃ s : ℤ, ∀ n : Fin (Vc D i).rank, (lamV D i τ).w n =
    s + (if (n : ℕ) < D.R.k + i then (aPl D i (D.R.k + i) τ n : ℤ) else 0) -
      (if (Fin.rev n : ℕ) < D.R.m - (i + 1) then (aMi D i (D.R.k + i) (D.R.m - (i + 1)) τ (Fin.rev n) : ℤ) else 0) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hW⟩ :=
    GlobalTheory.ForcedWeights.lamLForced D (i + 1) (Nat.le_add_left _ _) hi τ
  have hWe' : (W.e : ℚ) = (D.hc τ).e i := hWe
  have hr : (Vc D i).rank = D.R.k + D.R.m - 1 + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) hi
  obtain ⟨q, hq⟩ : ∃ q, i + 1 + q = D.R.m := ⟨D.R.m - (i + 1), by omega⟩
  have hp : W.p = D.R.k + i := by unfold IndefiniteWeightData.WeightData.p; omega
  have hq' : W.q = q := by unfold IndefiniteWeightData.WeightData.q; omega
  have hnV : W.nV = D.R.k + i + q + D.R.t := by unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; omega
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have ha' : (D.R.k : ℚ) = a + a := by exact_mod_cast ha
  have hb' : (q : ℚ) = b + b - i - 1 := by
    have : ((i : ℕ) : ℚ) + 1 + q = b + b := by exact_mod_cast hq.trans hb
    linarith
  have hd : W.dTau = ((a + (i : ℕ) - b - W.e : ℤ) : ℚ) := by
    unfold IndefiniteWeightData.WeightData.dTau
    rw [hp, hq']
    push_cast
    rw [ha', hb']
    ring
  generalize (a + (i : ℕ) - b - W.e : ℤ) = s at hd
  rw [show D.R.m - (i + 1) = q by omega]
  refine ⟨s, fun n => ?_⟩
  have hn := n.2
  rw [← Int.cast_inj (α := ℚ), hW n, IndefiniteWeightData.WeightData.lamPrime, hd, IndefiniteWeightData.WeightData.thetaWt, hp, hq', hWt, Fin.val_rev,
    Int.cast_sub, Int.cast_add]
  by_cases h1 : (n : ℕ) < D.R.k + i
  · rw [if_pos (by omega), if_pos h1, if_neg (by omega), Int.cast_natCast, aPl_cast D i τ n h1, IndefiniteWeightData.WeightData.aPlus,
      hp, hq', hnV, hWe']
    have hl : (W.lam (n + 1) : ℚ) = lamAt (D.hc τ) n := by
      unfold IndefiniteWeightData.WeightData.lam
      rw [hWk]
      split_ifs with h2
      · rw [lamAt, dite_eq_left (by omega)]
        exact hWv ⟨n, by omega⟩
      · rw [lamAt_b (D.hc τ) n (n - (D.R.k - 1)) (by omega) (by omega), Int.cast_neg,
          show (n : ℕ) + 1 - (D.R.k - 1) = n - (D.R.k - 1) + 1 by omega]
        exact congrArg _ (hWb ⟨n - (D.R.k - 1), by omega⟩)
    rw [hl]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : (n : ℕ) + 1 ≤ D.R.k + i + D.R.t
    · rw [if_pos h2, if_neg (by omega)]
      push_cast
      ring
    · obtain ⟨c, hc⟩ : ∃ c, (n : ℕ) = D.R.k + i + D.R.t + c := ⟨n - (D.R.k + i + D.R.t), by omega⟩
      rw [if_neg h2, if_pos (by omega), Int.cast_natCast, aMi_cast D i τ q _ c hq (by omega), IndefiniteWeightData.WeightData.aMinus,
        hq', hWj, hWt, hWe', show q + 1 - (q + 1 - (n + 1 - (D.R.k + i) - D.R.t)) = c + 1 by omega,
        show (i : ℕ) + 1 + (c + 1) = i + 1 + c + 1 by omega, hWb ⟨i + 1 + c, by omega⟩]
      push_cast
      ring

theorem exists_io_record : ∀ (D : D7) (Q : Formalism.L2.Pj.Par D), Q.Pins → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff Q.l), ∃ (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VsV D i c'.F), IoLFRec c' (fun τ => embF c' (tauE D τ)) (lamV D i) (wtA (κ i)) io hw := by
  intro D Q hQ κ hκ i c'
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨-, hinj, hΨ, -, hval⟩ := GlobalTheory.WeightExponents.weight_exponents D Q hQ _ (inR i) (κ i)
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 _ (inR i)
  have hp1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := rfl
  have hq1 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1) := rfl
  choose s hs using lamV_eq D i
  refine GlobalTheory.FrameRead.CoefMap.exists_ioLFRec D.host.E Q.H (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank D.what₂.Tau (DV.tauEmb D)
    ⟨hinj, fun τ => (hΨ τ).trans (exists_congr fun _ => eq_comm)⟩ ?_ Q.l c' (wtA (κ i)) s (lamV D i) (dom_wtA (κ i)).1 ?_
  · refine le_trans ?_ (r_le_V i)
    rw [hp, hq, hp1, hq1, Ranks.r]
    omega
  · intro τ n
    have ht := hQ.1.2.2.2 τ
    have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D τ) (Q.H.rt : D.host.E) = Q.H.rt0 :=
      GlobalTheory.WeightExponents.not_inPsi_conj hQ.1 τ
    have hsig : (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
    obtain ⟨h1, h2, -⟩ := hκ i τ
    rw [hsig] at h1 h2
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos ht, if_neg hc, hp, hq, hs τ n,
      (hval τ _).1, (hval τ _).2]
    congr 1
    · congr 1
      refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dite_eq_left (show (n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1 from h), h1]
      rfl
    · refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dite_eq_left (show (Fin.rev n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2 from h), h2]
      rfl

end GlobalTheory.CoefMapRecord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeightsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harmonicCoefficientMap_at_weights : ∀ (D : D7) (Q : Formalism.L2.Pj.Par D), Q.Pins → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff Q.l), ∃ (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VsV D i c'.F), IoLFRec c' (fun τ => embF c' (tauE D τ)) (lamV D i) (wtA (κ i)) io hw := by
  first | exact @GlobalTheory.CoefMapRecord.exists_io_record | exact GlobalTheory.CoefMapRecord.exists_io_record | (intros; apply GlobalTheory.CoefMapRecord.exists_io_record <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel

variable {D : D7}

namespace HypDec

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

section Unip

variable (b : Mx D ρ S₀.rank) (c : skewA D ρ)

theorem nB_mem_GQ {b : Mx D ρ S₀.rank} (h : b ∈ ratMx D ρ S₀.rank) : d.nB b ∈ GQ S := by
  have h' : plus S₀ b ∈ ratMx D _ _ := ratMx_mul (rat_mem _) (ratMx_adj h)
  exact d.ofImages_mem_GQ (d.images_nB b) (rat_mem _) (add_mem (rat_mem _) (ratMx_mul (rat_mem _) h))
    (sub_mem (sub_mem (rat_mem _) (ratMx_mul (rat_mem _) h')) (ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul h h'))))

theorem nC_mem_GQ {c : skewA D ρ} (h : c.1 ∈ ratMx D ρ ρ) : d.nC c ∈ GQ S :=
  d.ofImages_mem_GQ (d.images_nC c) (rat_mem _) (rat_mem _) (add_mem (rat_mem _) (ratMx_mul (rat_mem _) h))

theorem continuous_nB : Continuous d.nB := by
  have := (lattice_Mx D S.rank ρ).1
  have : ContinuousSub (Mx D S.rank ρ) := IsTopologicalAddGroup.to_continuousSub
  have h : Continuous (plus S₀ : Mx D ρ S₀.rank → _) := continuous_const.matrix_mul continuous_adj
  have h1 : Continuous fun b : Mx D ρ S₀.rank => b ⬝ plus S₀ b := continuous_id.matrix_mul h
  have h2 : Continuous fun b : Mx D ρ S₀.rank => half D • (b ⬝ plus S₀ b) := h1.const_smul (half D)
  have h3 : Continuous fun b : Mx D ρ S₀.rank => d.jX ⬝ b := continuous_const.matrix_mul continuous_id
  refine continuous_of_mt S ?_
  simp only [nB, mt_ofImages]
  refine Continuous.add (Continuous.add continuous_const (Continuous.matrix_mul ?_ continuous_const))
    (Continuous.matrix_mul ?_ continuous_const)
  · exact Continuous.add continuous_const h3
  · exact Continuous.sub (Continuous.sub continuous_const (continuous_const.matrix_mul h))
      (continuous_const.matrix_mul h2)

theorem continuous_nC : Continuous d.nC := by
  have h3 : Continuous fun c : skewA D ρ => d.jX ⬝ c.1 := continuous_const.matrix_mul continuous_subtype_val
  refine continuous_of_mt S ?_
  simp only [nC, mt_ofImages]
  exact Continuous.add continuous_const (Continuous.matrix_mul (Continuous.add continuous_const h3) continuous_const)

theorem nB_zero : d.nB 0 = 1 :=
  d.ga_ext (by rw [nB_jX, mt_one, Matrix.one_mul]) (by rw [nB_j0, mt_one, Matrix.one_mul, Matrix.mul_zero, add_zero])
    (by rw [nB_jY, mt_one, Matrix.one_mul, plus_zero, Matrix.mul_zero, Matrix.mul_zero, smul_zero, Matrix.mul_zero,
      sub_zero, sub_zero])

theorem nC_zero : d.nC 0 = 1 :=
  d.ga_ext (by rw [nC_jX, mt_one, Matrix.one_mul]) (by rw [nC_j0, mt_one, Matrix.one_mul])
    (by rw [nC_jY, mt_one, Matrix.one_mul, AddSubgroup.coe_zero, Matrix.mul_zero, add_zero])

theorem nC_add (c c' : skewA D ρ) : d.nC (c + c') = d.nC c * d.nC c' :=
  d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nC_jX]) (by simp only [mt_mul, Matrix.mul_assoc, nC_j0])
    (by simp only [mt_mul, Matrix.mul_assoc, nC_jY, Matrix.mul_add, cancel₂ (d.nC_jX _), AddSubgroup.coe_add, add_assoc])

theorem nB_mul_nB (b₁ b₂ : Mx D ρ S₀.rank) : d.nB b₁ * d.nB b₂ = d.nB (b₁ + b₂) * d.nC (cComm S₀ b₁ b₂) := by
  refine d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nB_jX, nC_jX])
    (by simp only [mt_mul, Matrix.mul_assoc, nB_j0, nC_j0, Matrix.mul_add, cancel₂ (d.nB_jX _), add_assoc]) ?_
  have h := half_smul_add (b₁ ⬝ plus S₀ b₂)
  simp only [mt_mul, Matrix.mul_assoc, nB_jY, nC_jY, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul,
    cancel₂ (d.nB_jX _), cancel₂ (d.nB_j0 _), cComm, plus_add, smul_add, smul_sub]
  generalize half D • (b₁ ⬝ plus S₀ b₂) = u at h ⊢
  rw [← h, Matrix.mul_add]
  abel

theorem nB_inv : (d.nB b)⁻¹ = d.nB (-b) := by
  have h : cComm S₀ b (-b) = 0 := Subtype.ext (by
    simp only [cComm, plus_neg, Matrix.neg_mul, Matrix.mul_neg, sub_self, smul_zero, AddSubgroup.coe_zero])
  rw [inv_eq_iff_mul_eq_one, nB_mul_nB, add_neg_cancel, h, nB_zero, nC_zero, one_mul]

theorem nC_inv : (d.nC c)⁻¹ = d.nC (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← nC_add, add_neg_cancel, nC_zero]

theorem nC_mul_nB : d.nC c * d.nB b = d.nB b * d.nC c :=
  d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nB_jX, nC_jX])
    (by simp only [mt_mul, Matrix.mul_assoc, nB_j0, nC_j0, Matrix.mul_add, cancel₂ (d.nC_jX _)])
    (by
      simp only [mt_mul, Matrix.mul_assoc, nB_jY, nC_jY, Matrix.mul_add, Matrix.mul_sub, cancel₂ (d.nB_jX _),
        cancel₂ (d.nC_jX _), cancel₂ (d.nC_j0 _)]
      abel)

theorem levi_mul_nB (a : GL (Fin ρ) (AE D)) : d.levi a * d.nB b = d.nB (a.1 ⬝ b) * d.levi a := by
  have h : adj a.1 ⬝ adj (a⁻¹).1 = 1 := by rw [← adj_mul, Units.inv_mul, adj_one]
  refine d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nB_jX, levi_jX, cancel₂ (d.nB_jX _)])
    (by simp only [mt_mul, Matrix.mul_assoc, nB_j0, wittDecomp_levi_inclAnisotropic, Matrix.mul_add, cancel₂ (d.levi_jX _)]) ?_
  simp only [mt_mul, Matrix.mul_assoc, nB_jY, levi_jY, Matrix.mul_sub, Matrix.sub_mul, cancel₂ (d.levi_jX _),
    cancel₂ (d.wittDecomp_levi_inclAnisotropic _), cancel₂ (d.nB_jY _), plus_mul_left, Matrix.mul_smul, Matrix.smul_mul, h, Matrix.mul_one]

theorem levi_mul_nC (a : GL (Fin ρ) (AE D)) : d.levi a * d.nC c = d.nC (skewConj a.1 c) * d.levi a := by
  have h : adj a.1 ⬝ adj (a⁻¹).1 = 1 := by rw [← adj_mul, Units.inv_mul, adj_one]
  refine d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nC_jX, levi_jX, cancel₂ (d.nC_jX _)])
    (by simp only [mt_mul, Matrix.mul_assoc, nC_j0, wittDecomp_levi_inclAnisotropic]) ?_
  simp only [mt_mul, Matrix.mul_assoc, nC_jY, levi_jY, Matrix.mul_add, Matrix.add_mul, cancel₂ (d.levi_jX _),
    cancel₂ (d.nC_jY _), skewConj, h, Matrix.mul_one]

theorem wittHyperbolic_anisotropic_conj_nB (g : GA D S₀) : d.emb0 g * d.nB b = d.nB (b ⬝ mt S₀ g⁻¹) * d.emb0 g := by
  refine d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nB_jX, wittDecomp_anisotropicEmbedding_inclX]) ?_ ?_
  · simp only [mt_mul, Matrix.mul_assoc, nB_j0, wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_add, Matrix.add_mul, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX _),
      cancel₂ (d.nB_j0 _), mt_inv_mul, Matrix.mul_one]
  · simp only [mt_mul, Matrix.mul_assoc, nB_jY, wittDecomp_anisotropicEmbedding_inclY, Matrix.mul_sub, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX _), cancel₂ (d.wittDecomp_anisotropicEmbedding_inclAnisotropic _),
      plus_mul_inv, cancel₂ (mt_inv_mul S₀ g), Matrix.one_mul]

theorem wittHyperbolic_anisotropic_commute_nC (g : GA D S₀) : d.emb0 g * d.nC c = d.nC c * d.emb0 g :=
  d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nC_jX, wittDecomp_anisotropicEmbedding_inclX])
    (by simp only [mt_mul, Matrix.mul_assoc, nC_j0, wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ (d.nC_j0 _)])
    (by simp only [mt_mul, Matrix.mul_assoc, nC_jY, wittDecomp_anisotropicEmbedding_inclY, Matrix.mul_add, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX _)])

theorem wittHyperbolic_anisotropic_commute_levi (g : GA D S₀) (a : GL (Fin ρ) (AE D)) : d.emb0 g * d.levi a = d.levi a * d.emb0 g :=
  d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, levi_jX, wittDecomp_anisotropicEmbedding_inclX, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX _)])
    (by simp only [mt_mul, Matrix.mul_assoc, wittDecomp_levi_inclAnisotropic, wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ (d.wittDecomp_levi_inclAnisotropic _)])
    (by simp only [mt_mul, Matrix.mul_assoc, levi_jY, wittDecomp_anisotropicEmbedding_inclY, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclY _)])

end Unip

theorem mulVec_perp {M : Mx D S.rank S.rank} {U : Mx D ρ ρ} {b : Mx D ρ S₀.rank} (h1 : M ⬝ d.jX = d.jX ⬝ U)
    (h2 : M ⬝ d.j0 = d.jX ⬝ b) (v : Fin S.rank → AE D) (h3 : d.pY *ᵥ v = 0) :
    M *ᵥ v = d.jX *ᵥ ((U ⬝ d.pX + b ⬝ d.p0) *ᵥ v) := by
  have h4 : M = d.jX ⬝ (U ⬝ d.pX + b ⬝ d.p0) + (M ⬝ d.jY) ⬝ d.pY :=
    d.mat_ext (by simp only [h1, Matrix.add_mul, Matrix.mul_assoc, pX_jX, p0_jX, pY_jX, Matrix.mul_one,
        Matrix.mul_zero, add_zero])
      (by simp only [h2, Matrix.add_mul, Matrix.mul_assoc, pX_j0, p0_j0, pY_j0, Matrix.mul_one, Matrix.mul_zero,
        add_zero, zero_add])
      (by simp only [Matrix.add_mul, Matrix.mul_assoc, pX_jY, p0_jY, pY_jY, Matrix.mul_one, Matrix.mul_zero,
        add_zero, zero_add])
  exact (congrArg (· *ᵥ v) h4).trans (mulVec_of_kill _ _ _ _ _ h3)

theorem pY_ratV {x : Fin S.rank → D.host.E} (hx : d.qY *ᵥ x = 0) : d.pY *ᵥ ratV x = 0 := by
  funext i
  have := RingHom.map_mulVec (incA D) d.qY x i
  rw [hx, Pi.zero_apply, map_zero] at this
  exact this.symm

theorem subOne_mul {k : ℕ} (g : GA D S) (y : Mx D S.rank k) : subOne S g ⬝ y = mt S g ⬝ y - y :=
  (Matrix.sub_mul _ _ _).trans (by rw [Matrix.one_mul]; rfl)

theorem mem_NFlag {g : GA D S} {u : GL (Fin ρ) (AE D)} (hu : u ∈ upperUni ρ (AE D)) {b : Mx D ρ S₀.rank}
    (hX : mt S g ⬝ d.jX = d.jX ⬝ u.1) (h0 : mt S g ⬝ d.j0 = d.j0 + d.jX ⬝ b) : g ∈ NFlag S d.e := by
  have h1 : subOne S g ⬝ d.jX = d.jX ⬝ (u.1 - 1) := by rw [subOne_mul, hX, Matrix.mul_sub, Matrix.mul_one]
  have h2 : subOne S g ⬝ d.j0 = d.jX ⬝ b := by rw [subOne_mul, h0, add_sub_cancel_left]
  refine Subgroup.subset_closure ⟨fun i => ⟨fun j => (u.1 - 1) j i, fun j hj => ?_, ?_⟩,
    fun x hx => ⟨_, d.mulVec_perp h1 h2 _ (d.pY_ratV hx)⟩⟩
  · beta_reduce
    rcases hj.eq_or_lt with rfl | hj
    · rw [Matrix.sub_apply, (hu i i).2, Matrix.one_apply_eq, sub_self]
    · rw [Matrix.sub_apply, (hu j i).1 hj, Matrix.one_apply_ne hj.ne', sub_self]
  · funext k
    exact congrFun (congrFun h1 k) i

theorem one_mem_upperUni : (1 : GL (Fin ρ) (AE D)) ∈ upperUni ρ (AE D) :=
  fun i j => by
    rw [Units.val_one]
    exact ⟨fun h => Matrix.one_apply_ne h.ne', Matrix.one_apply_eq i⟩

theorem levi_mem_NFlag {u : GL (Fin ρ) (AE D)} (hu : u ∈ upperUni ρ (AE D)) : d.levi u ∈ NFlag S d.e :=
  d.mem_NFlag hu (b := 0) (d.levi_jX u) (by rw [wittDecomp_levi_inclAnisotropic, Matrix.mul_zero, add_zero])

theorem nB_mem_NFlag (b : Mx D ρ S₀.rank) : d.nB b ∈ NFlag S d.e :=
  d.mem_NFlag one_mem_upperUni (by rw [nB_jX, Units.val_one, Matrix.mul_one]) (d.nB_j0 b)

theorem nC_mem_NFlag (c : skewA D ρ) : d.nC c ∈ NFlag S d.e :=
  d.mem_NFlag one_mem_upperUni (b := 0) (by rw [nC_jX, Units.val_one, Matrix.mul_one])
    (by rw [nC_j0, Matrix.mul_zero, add_zero])

end HypDec

end GlobalTheory.MixModel

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel

variable {D : D7}

def pairS (T : HSp D) {ρ : ℕ} (x x' : Mx D T.rank ρ) : AE D := (adj x' * (gA T * x)).trace

def pairT (S : HSp D) {ρ : ℕ} (ξ η : Mx D ρ S.rank) : AE D := (giA S * (adj η * ξ)).trace

theorem pairT_adj (S : HSp D) {ρ : ℕ} (c : AE D) (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ) :
    pairT S ξ (c • (adj y * gA S)) = (cA D c • (y * ξ)).trace := by
  rw [pairT, adj_smul, adj_mul, adj_adj, adj_gA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, giA_gA_cancel]

namespace HypDec

section Source

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)

def extX : Mx D T.rank ρ →+ WO S T where
  toFun x := x * d.pX
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

def extY : Mx D T.rank ρ →+ WO S T where
  toFun x := x * d.pY
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

def ext0 : WO S₀ T →+ WO S T where
  toFun w := w * d.p0
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

theorem extX_apply (x : Mx D T.rank ρ) : d.extX T x = x * d.pX := rfl

theorem extY_apply (x : Mx D T.rank ρ) : d.extY T x = x * d.pY := rfl

theorem matrixExtendByZero_apply (w : WO S₀ T) : d.ext0 T w = w * d.p0 := rfl

def coordS : WO S T ≃+ Mx D T.rank ρ × WO S₀ T × Mx D T.rank ρ where
  toFun w := (w * d.jX, w * d.j0, w * d.jY)
  invFun p := d.extX T p.1 + d.ext0 T p.2.1 + d.extY T p.2.2
  left_inv w := by
    simp only [extX_apply, extY_apply, matrixExtendByZero_apply, Matrix.mul_assoc]
    rw [← Matrix.mul_add, ← Matrix.mul_add, sum_eq_one, Matrix.mul_one]
  right_inv p := by
    simp only [extX_apply, extY_apply, matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, pX_jX, pX_j0, pX_jY, pY_jX, pY_j0,
      pY_jY, p0_jX, p0_j0, p0_jY, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
  map_add' x y := Prod.ext (Matrix.add_mul _ _ _) (Prod.ext (Matrix.add_mul _ _ _) (Matrix.add_mul _ _ _))

theorem hO_coordS (w w' : WO S T) : hO S T w w' =
    pairS T (w * d.jX) (w' * d.jY) + hO S₀ T (w * d.j0) (w' * d.j0) + pairS T (w * d.jY) (w' * d.jX) := by
  simp only [hO_eq_trace, pairS, adj_mul]
  rw [d.giA_eq, Matrix.add_mul, Matrix.add_mul, trace_add, trace_add, Matrix.mul_assoc, trace_mul_comm,
    Matrix.mul_assoc d.j0, trace_mul_comm d.j0, Matrix.mul_assoc d.jY, trace_mul_comm d.jY]
  simp only [Matrix.mul_assoc]

theorem hO_ext (x x' y y' : Mx D T.rank ρ) (w w' : WO S₀ T) :
    hO S T (d.extX T x + d.ext0 T w + d.extY T y) (d.extX T x' + d.ext0 T w' + d.extY T y') =
      pairS T x y' + hO S₀ T w w' + pairS T y x' := by
  rw [d.hO_coordS]
  simp only [extX_apply, extY_apply, matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, pX_jX, pX_j0, pX_jY, pY_jX, pY_j0,
    pY_jY, p0_jX, p0_j0, p0_jY, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]

theorem symplOH_extY_extY (y y' : Mx D T.rank ρ) : symplOH S T (d.extY T y) (d.extY T y') = 0 := by
  have h := d.hO_ext T 0 0 y y' 0 0
  simp only [map_zero, zero_add, pairS, hO_eq_trace S₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul, trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem symplOH_extX_extX (x x' : Mx D T.rank ρ) : symplOH S T (d.extX T x) (d.extX T x') = 0 := by
  have h := d.hO_ext T x x' 0 0 0 0
  simp only [map_zero, add_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul, trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_extDual_extAnisotropic (y : Mx D T.rank ρ) (w : WO S₀ T) : symplOH S T (d.extY T y) (d.ext0 T w) = 0 := by
  have h := d.hO_ext T 0 0 y 0 0 w
  simp only [map_zero, zero_add, add_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_extIsotropic_extAnisotropic (x : Mx D T.rank ρ) (w : WO S₀ T) : symplOH S T (d.extX T x) (d.ext0 T w) = 0 := by
  have h := d.hO_ext T x 0 0 0 0 w
  simp only [map_zero, zero_add, add_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_extAnisotropic_extAnisotropic (w w' : WO S₀ T) : symplOH S T (d.ext0 T w) (d.ext0 T w') = symplOH S₀ T w w' := by
  have h := d.hO_ext T 0 0 0 0 w w'
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  rw [symplOH_eq, h, symplOH_eq]

theorem symplOH_extX_extY (x y : Mx D T.rank ρ) : symplOH S T (d.extX T x) (d.extY T y) = trHalf D (pairS T x y) := by
  have h := d.hO_ext T x 0 0 y 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplOH_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]

def qS (c : skewA D ρ) (x : Mx D T.rank ρ) : AF D.host.F := symplOH S T (d.extX T x) (d.extY T (x * c.1))

theorem extX_levi (a : GL (Fin ρ) (AE D)) (x : Mx D T.rank ρ) : d.extX T x * mt S (d.levi a) = d.extX T (x * a.1) := by
  rw [extX_apply, extX_apply, Matrix.mul_assoc, pX_levi, Matrix.mul_assoc]

theorem extX_nC (c : skewA D ρ) (x : Mx D T.rank ρ) :
    d.extX T x * mt S (d.nC c) = d.extX T x + d.extY T (x * c.1) := by
  rw [extX_apply, extY_apply, Matrix.mul_assoc, pX_nC, Matrix.mul_add, Matrix.mul_assoc]

theorem extX_nB (b : Mx D ρ S₀.rank) (x : Mx D T.rank ρ) :
    d.extX T x * mt S (d.nB b) =
      d.extX T x + d.ext0 T (x * b) - d.extY T (x * (half D • (b * plus S₀ b))) := by
  rw [extX_apply, extY_apply, matrixExtendByZero_apply, Matrix.mul_assoc, pX_nB, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc,
    Matrix.mul_assoc]

theorem wittDecomp_homAction_extAnisotropic_equivariant (g : GA D S₀) (h : GA D T) (w : WO S₀ T) :
    actO S T (d.emb0 g) h (d.ext0 T w) = d.ext0 T (actO S₀ T g h w) := by
  simp only [actO_eq, matrixExtendByZero_apply, ← map_inv, Matrix.mul_assoc, wittDecomp_projAnisotropic_anisotropicEmbedding]

def mixS (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ)
    (x : Mx D T.rank ρ) : WO S₀ T → ℂ := fun w₀ =>
  ∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 ∂μ

variable {T} {ψ : AddChar (AF D.host.F) ℂ}

theorem integrandS_eq (f : WO S T → ℂ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 =
      ψ (symplOH S T (d.extY T a) (d.extX T x)) * f (d.extY T a + d.extX T x + d.ext0 T w₀) := by
  simp only [heisO, zero_add, symplOH_zero_left, GlobalTheory.OrientedHeis.symplOH_add_left, wittDecomp_sympl_extDual_extAnisotropic,
    wittDecomp_sympl_extIsotropic_extAnisotropic, add_zero, AddChar.map_zero_eq_one, one_mul]

theorem integrandS_periodic {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) (w₀ : WO S₀ T)
    (γ : Mx D T.rank ρ) (hγ : γ ∈ ratMx D T.rank ρ) (a : Mx D T.rank ρ) :
    heisO ψ S T (d.extY T (γ + a)) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 =
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 := by
  obtain ⟨δ, hδ⟩ : d.extY T γ ∈ ratMx D _ _ := ratMx_mul hγ (rat_mem _)
  have h := hf.quasi δ (d.extY T a + d.extX T x + d.ext0 T w₀)
  rw [show ratW T S δ = d.extY T γ from hδ] at h
  rw [integrandS_eq, integrandS_eq, map_add (d.extY T), add_assoc (d.extY T γ), add_assoc (d.extY T γ), h, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, symplOH_extY_extY,
    wittDecomp_sympl_extDual_extAnisotropic, zero_add, add_zero]
  rw [add_comm (symplOH S T (d.extY T γ) _), add_neg_cancel_right]

theorem integrableOn_mixS (hψ : Continuous ψ) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ)
    (w₀ : WO S₀ T) : IntegrableOn
      (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0) 𝓕 μ := by
  refine covolOne_integrableOn hμ _ ?_ (d.integrandS_periodic hf x w₀)
  have hc : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  simp only [integrandS_eq]
  exact (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH hc continuous_const)).mul
    (hf.cont.comp ((hc.add continuous_const).add continuous_const))

theorem mixS_indep {μ μ' : Measure (Mx D T.rank ρ)} {𝓕 𝓕' : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) (hμ' : IsCovolOne (ratMx D T.rank ρ) μ' 𝓕') {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : d.mixS T ψ μ' 𝓕' f = d.mixS T ψ μ 𝓕 f := by
  funext x w₀
  exact covolOne_integral_eq hμ hμ' _ (d.integrandS_periodic hf x w₀)

end Source

section Target

variable {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)

def incX : Mx D ρ S.rank →+ WO S T where
  toFun ξ := d.jX * ξ
  map_zero' := Matrix.mul_zero _
  map_add' _ _ := Matrix.mul_add _ _ _

def incY : Mx D ρ S.rank →+ WO S T where
  toFun η := d.jY * η
  map_zero' := Matrix.mul_zero _
  map_add' _ _ := Matrix.mul_add _ _ _

def inc0 : WO S T₀ →+ WO S T where
  toFun w := d.j0 * w
  map_zero' := Matrix.mul_zero _
  map_add' _ _ := Matrix.mul_add _ _ _

def incAdj : Mx D S.rank ρ →+ WO S T where
  toFun y := d.incY S (incA D (-D.host.xi0⁻¹) • (adj y * gA S))
  map_zero' := by rw [adj_zero, Matrix.zero_mul, smul_zero, map_zero]
  map_add' _ _ := by rw [adj_add, Matrix.add_mul, smul_add, map_add (f := _)]

theorem incX_apply (ξ : Mx D ρ S.rank) : d.incX S ξ = d.jX * ξ := rfl

theorem incY_apply (η : Mx D ρ S.rank) : d.incY S η = d.jY * η := rfl

theorem wittDecomp_inclAnisotropicHom_apply (w : WO S T₀) : d.inc0 S w = d.j0 * w := rfl

theorem incAdj_apply (y : Mx D S.rank ρ) :
    d.incAdj S y = d.incY S (incA D (-D.host.xi0⁻¹) • (adj y * gA S)) := rfl

theorem wittDecomp_trace0Unit_mul_conj_neg_inv : incA D D.host.xi0 * cA D (incA D (-D.host.xi0⁻¹)) = 1 := by
  rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]

def coordT : WO S T ≃+ Mx D ρ S.rank × WO S T₀ × Mx D ρ S.rank where
  toFun w := (d.pX * w, d.p0 * w, d.pY * w)
  invFun p := d.incX S p.1 + d.inc0 S p.2.1 + d.incY S p.2.2
  left_inv w := by
    simp only [incX_apply, incY_apply, wittDecomp_inclAnisotropicHom_apply, ← Matrix.mul_assoc]
    rw [← Matrix.add_mul, ← Matrix.add_mul, sum_eq_one, Matrix.one_mul]
  right_inv p := by
    simp only [incX_apply, incY_apply, wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc, pX_jX, pX_j0, pX_jY, pY_jX, pY_j0,
      pY_jY, p0_jX, p0_j0, p0_jY, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  map_add' x y := Prod.ext (Matrix.mul_add _ _ _) (Prod.ext (Matrix.mul_add _ _ _) (Matrix.mul_add _ _ _))

theorem hO_coordT (w w' : WO S T) : hO S T w w' =
    pairT S (d.pX * w) (d.pY * w') + hO S T₀ (d.p0 * w) (d.p0 * w') + pairT S (d.pY * w) (d.pX * w') := by
  simp only [hO_eq_trace, pairT, adj_mul]
  rw [d.gA_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, trace_add, Matrix.mul_assoc]

theorem hO_inc (ξ ξ' η η' : Mx D ρ S.rank) (w w' : WO S T₀) :
    hO S T (d.incX S ξ + d.inc0 S w + d.incY S η) (d.incX S ξ' + d.inc0 S w' + d.incY S η') =
      pairT S ξ η' + hO S T₀ w w' + pairT S η ξ' := by
  rw [d.hO_coordT]
  simp only [incX_apply, incY_apply, wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc, pX_jX, pX_j0, pX_jY, pY_jX, pY_j0,
    pY_jY, p0_jX, p0_j0, p0_jY, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]

theorem symplOH_incX_incX (ξ ξ' : Mx D ρ S.rank) : symplOH S T (d.incX S ξ) (d.incX S ξ') = 0 := by
  have h := d.hO_inc S ξ ξ' 0 0 0 0
  simp only [map_zero, add_zero, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul, trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem symplOH_incY_incY (η η' : Mx D ρ S.rank) : symplOH S T (d.incY S η) (d.incY S η') = 0 := by
  have h := d.hO_inc S 0 0 η η' 0 0
  simp only [map_zero, zero_add, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul, trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_inclIsotropic_inclAnisotropic (ξ : Mx D ρ S.rank) (w : WO S T₀) : symplOH S T (d.incX S ξ) (d.inc0 S w) = 0 := by
  have h := d.hO_inc S ξ 0 0 0 0 w
  simp only [map_zero, zero_add, add_zero, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_inclDual_inclAnisotropic (η : Mx D ρ S.rank) (w : WO S T₀) : symplOH S T (d.incY S η) (d.inc0 S w) = 0 := by
  have h := d.hO_inc S 0 0 η 0 0 w
  simp only [map_zero, zero_add, add_zero, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_inclAnisotropic_inclAnisotropic (w w' : WO S T₀) : symplOH S T (d.inc0 S w) (d.inc0 S w') = symplOH S T₀ w w' := by
  have h := d.hO_inc S 0 0 0 0 w w'
  simp only [map_zero, zero_add, add_zero, pairT, Matrix.mul_zero, trace_zero] at h
  rw [symplOH_eq, h, symplOH_eq]

theorem hO_incX_incY (ξ η : Mx D ρ S.rank) : hO S T (d.incX S ξ) (d.incY S η) = pairT S ξ η := by
  have h := d.hO_inc S ξ 0 0 η 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S T₀, Matrix.mul_zero, trace_zero] at h
  rw [h, show pairT S (0 : Mx D ρ S.rank) 0 = 0 by simp [pairT], add_zero]

theorem symplO_incX_incAdj (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ) :
    symplO S T (d.incX S ξ) (d.incAdj S y) = Algebra.trace (AF D.host.F) (AE D) (y * ξ).trace := by
  rw [symplO_eq, incAdj_apply, hO_incX_incY, pairT_adj]
  exact congrArg _ (mul_trace_smul wittDecomp_trace0Unit_mul_conj_neg_inv _)

def qT (c : skewA D ρ) (y : Mx D S.rank ρ) : AF D.host.F :=
  symplOH S T (d.incAdj S y) (mt T (d.nC c)⁻¹ * d.incAdj S y - d.incAdj S y)

theorem actO_incAdj (g : GA D S) (a : GL (Fin ρ) (AE D)) (y : Mx D S.rank ρ) :
    actO S T g (d.levi a)⁻¹ (d.incAdj S y) = d.incAdj S (mt S g * y * a.1) := by
  simp only [actO_eq, incAdj_apply, incY_apply, ← map_inv, cancel₂ (d.levi_jY _), inv_inv, adj_mul, mt_inv S g,
    Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul, gA_giA_cancel]

def mixT (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ)
    (y : Mx D S.rank ρ) : WO S T₀ → ℂ := fun w₀ =>
  ∫ ξ in 𝓕, heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 ∂μ

variable {S} {ψ : AddChar (AF D.host.F) ℂ}

theorem integrandT_eq (f : WO S T → ℂ) (y : Mx D S.rank ρ) (ξ : Mx D ρ S.rank) (w₀ : WO S T₀) :
    heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 =
      ψ (symplOH S T (d.incX S ξ) (d.incAdj S y)) * f (d.incX S ξ + d.incAdj S y + d.inc0 S w₀) := by
  have h : symplOH S T (d.incAdj S y) (d.inc0 S w₀) = 0 := d.wittDecomp_sympl_inclDual_inclAnisotropic S _ w₀
  simp only [heisO, zero_add, symplOH_zero_left, GlobalTheory.OrientedHeis.symplOH_add_left, h,
    wittDecomp_sympl_inclIsotropic_inclAnisotropic, add_zero, AddChar.map_zero_eq_one, one_mul]

theorem integrandT_periodic {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (y : Mx D S.rank ρ) (w₀ : WO S T₀)
    (γ : Mx D ρ S.rank) (hγ : γ ∈ ratMx D ρ S.rank) (ξ : Mx D ρ S.rank) :
    heisO ψ S T (d.incX S (γ + ξ)) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 =
      heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 := by
  obtain ⟨δ, hδ⟩ : d.incX S γ ∈ ratMx D _ _ := ratMx_mul (rat_mem _) hγ
  have h := hf.quasi δ (d.incX S ξ + d.incAdj S y + d.inc0 S w₀)
  rw [show ratW T S δ = d.incX S γ from hδ] at h
  rw [integrandT_eq, integrandT_eq, map_add (d.incX S), add_assoc (d.incX S γ), add_assoc (d.incX S γ), h, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, symplOH_incX_incX,
    wittDecomp_sympl_inclIsotropic_inclAnisotropic, zero_add, add_zero]
  rw [add_comm (symplOH S T (d.incX S γ) _), add_neg_cancel_right]

end Target

end HypDec

section Examples

abbrev diagSp (D : D7) (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) : HSp D :=
  Examples₂.stdSpace Examples₂.star_isIntegral N neg p q

theorem diagSp_gram (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) :
    (diagSp D N neg p q).gram = (Matrix.diagonal fun i => Examples₂.sgn (neg i) : Matrix (Fin N) (Fin N) D.host.E) := by
  funext i j
  exact Examples₂.stdSpace_gram_apply _ N neg p q i j

theorem gram_check {N k l : ℕ} {neg : Fin N → Bool} {p q : ℕ} (a : Matrix (Fin N) (Fin k) D.host.E)
    (b : Matrix (Fin N) (Fin l) D.host.E) (c : Matrix (Fin k) (Fin l) D.host.E)
    (h : aᴴ * (Matrix.diagonal fun i => Examples₂.sgn (neg i) : Matrix (Fin N) (Fin N) D.host.E) * b = c) :
    aᴴ * (show Matrix (Fin N) (Fin N) D.host.E from (diagSp D N neg p q).gram) * b = c := by
  rw [← h]; congr 2; exact diagSp_gram N neg p q

section Field

variable (E : Type) [Field E] [CharZero E] [StarRing E]

abbrev sgnM {N : ℕ} (neg : Fin N → Bool) : Matrix (Fin N) (Fin N) E := Matrix.diagonal fun i => Examples₂.sgn (neg i)

omit [CharZero E] in
theorem col_gram {N : ℕ} (neg : Fin N → Bool) (a b : Matrix (Fin N) (Fin 1) E) (c : Matrix (Fin 1) (Fin 1) E)
    (h : ∑ k, star (a k 0) * Examples₂.sgn (neg k) * b k 0 = c 0 0) : aᴴ * sgnM E neg * b = c := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, ← h, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]


theorem three_gram (e e' i : Matrix (Fin 3) (Fin 1) E) (he : e = !![0; 1; 1]) (he' : e' = !![0; 1 / 2; -(1 / 2)])
    (hi : i = !![1; 0; 0]) :
    eᴴ * sgnM E ![false, false, true] * e = 0 ∧ e'ᴴ * sgnM E ![false, false, true] * e' = 0 ∧
    e'ᴴ * sgnM E ![false, false, true] * e = 1 ∧ iᴴ * sgnM E ![false, false, true] * i = sgnM E ![false] ∧
    iᴴ * sgnM E ![false, false, true] * e = 0 ∧ iᴴ * sgnM E ![false, false, true] * e' = 0 := by
  subst he he' hi
  refine ⟨col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_,
    col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_⟩ <;> simp [Fin.sum_univ_three, Examples₂.sgn]
  norm_num

end Field

def hypDecThree (D : D7) : HypDec (diagSp D 3 ![false, false, true] 2 1) (diagSp D 1 ![false] 1 0) 1 where
  e := (!![0; 1; 1] : Matrix (Fin 3) (Fin 1) D.host.E)
  e' := (!![0; 1 / 2; -(1 / 2)] : Matrix (Fin 3) (Fin 1) D.host.E)
  i₀ := (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) D.host.E)
  ee := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).1
  e'e' := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.1
  e'e := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.2.1
  iso := (gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.1).trans (diagSp_gram 1 _ 1 0).symm
  i₀e := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.1
  i₀e' := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.2
  rank_add := rfl

theorem pairS_plus (S₀ T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (b b' : Mx D ρ S₀.rank) :
    pairS T x (x * (b' * plus S₀ b)) = hO S₀ T (x * b) (x * b') := by
  rw [pairS, hO_eq_trace, adj_mul, adj_mul_plus, plus, adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem trHalf_half (z : AE D) : trHalf D (half D * z) + trHalf D (half D * z) = trHalf D z := by
  rw [← map_add (f := _), ← add_mul, half_add_half, one_mul]

end Examples

end GlobalTheory.MixModel

end

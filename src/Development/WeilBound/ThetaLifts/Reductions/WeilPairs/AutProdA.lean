module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFPreservesIsThetaFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFPreservesIsThetaFunction
noncomputable section

open scoped TensorProduct Matrix Topology ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory

namespace GlobalTheory.HeisKeepF

theorem contDiff_real_char (g : ℝ → ℂ) (hc : Continuous g) (hm : ∀ s t, g (s + t) = g s * g t) (h0 : g 0 = 1) :
    ContDiff ℝ ∞ g := by
  set c := deriv g 0
  have hd : ∀ s, HasDerivAt g (c * g s) s := GlobalTheory.hasDerivAt_of_continuous_additive_to_mul g hc hm h0
  have he : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(c * (s : ℂ)))) (Complex.exp (-(c * (s : ℂ))) * -c) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-(c * ((1 : ℝ) : ℂ))) s :=
      (((hasDerivAt_id s).ofReal_comp).const_mul c).neg
    replace h1 : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-c) s := h1.congr_deriv (by simp)
    exact h1.cexp
  have hk : ∀ s, HasDerivAt (fun s : ℝ => g s * Complex.exp (-(c * (s : ℂ)))) 0 s := by
    intro s
    have := (hd s).mul (he s)
    exact this.congr_deriv (by ring)
  have hconst : ∀ s, g s * Complex.exp (-(c * (s : ℂ))) = 1 := by
    intro s
    have := is_const_of_deriv_eq_zero (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) s 0
    simpa [h0] using this
  have hg : g = fun s : ℝ => Complex.exp (c * (s : ℂ)) := by
    funext s
    have h := hconst s
    rw [Complex.exp_neg] at h
    field_simp at h
    exact h
  rw [hg]
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem contDiff_char {k : ℕ} (χ : (Fin k → ℝ) → ℂ) (hc : Continuous χ) (hm : ∀ s t, χ (s + t) = χ s * χ t)
    (h0 : χ 0 = 1) : ContDiff ℝ ∞ χ := by
  have hsum : ∀ (s : Finset (Fin k)) (x : Fin k → Fin k → ℝ), χ (∑ i ∈ s, x i) = ∏ i ∈ s, χ (x i) := by
    intro s x
    refine Finset.induction_on s ?_ ?_
    · simp [h0]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.prod_insert ha, hm, ih]
  have hsplit : χ = fun t => ∏ i, χ (Pi.single i (t i)) := by
    funext t
    conv_lhs => rw [← Finset.univ_sum_single t]
    exact hsum _ _
  rw [hsplit]
  refine contDiff_prod fun i _ => ?_
  have hsc : Continuous fun s : ℝ => (Pi.single i s : Fin k → ℝ) := by
    first | fun_prop | exact continuous_single i | exact (LinearMap.single ℝ (fun _ : Fin k => ℝ) i).continuous_of_finiteDimensional
  have hi : ContDiff ℝ ∞ fun s : ℝ => χ (Pi.single i s) :=
    contDiff_real_char _ (hc.comp hsc) (fun s t => by rw [Pi.single_add, hm])
      (by rw [Pi.single_zero, h0])
  exact hi.comp (contDiff_apply ℝ (fun _ => ℝ) i)

theorem ker_fin_mem_nhds {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ) :
    {a : Af F | ψ (pairA F 0 a) = 1} ∈ 𝓝 (0 : Af F) := by
  have hcont : Continuous fun a : Af F => ψ (pairA F 0 a) := hc.comp (continuous_const.prodMk continuous_id)
  have hV : (fun a : Af F => ψ (pairA F 0 a)) ⁻¹' {z : ℂ | ‖z - 1‖ < 1 / 2} ∈ 𝓝 (0 : Af F) := by
    refine ((isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).preimage hcont).mem_nhds ?_
    show ‖ψ (pairA F 0 0) - 1‖ < 1 / 2
    rw [show pairA F 0 (0 : Af F) = 0 from rfl, ψ.map_zero_eq_one]
    norm_num
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  refine GroundTheory.Global.eq_one_of_sq_mem
    (s := {z | ∃ b : Af F, (∀ v, b v ∈ v.adicCompletionIntegers F) ∧ z = ψ (pairA F 0 (N • b))}) ?_ ?_ ⟨a, ha, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨b + b, fun v => add_mem (hb v) (hb v), ?_⟩
    rw [pow_two, ← AddChar.map_add_eq_mul]
    congr 1
    exact Prod.ext (add_zero 0) (smul_add N b b).symm
  · rintro _ ⟨b, hb, rfl⟩
    exact hNV b hb

section Form

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance modTopAEF : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
local instance topRingAEF : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _


variable (F) in
def eInfF : AF F := pairA F 1 0

theorem smul_eq_zero_of_infF {a : AEF F E} (h : infPartF F E a = 0) : eInfF F • a = 0 := by
  let s : Ainf F ⊗[F] E →ₗ[F] AEF F E := TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id
  have key : ∀ a : AEF F E, eInfF F • a = s (infPartF F E a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add a b ha hb => rw [smul_add, ha, hb, RingHom.map_add (f := _), map_add (f := _)]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      have : eInfF F • a = LinearMap.inl F (Ainf F) (Af F) (fstA F a) := Prod.ext (one_mul _) (zero_mul _)
      rw [this]
      rfl
  rw [key, h, map_zero]

theorem cAF_smul (σ : E →ₐ[F] E) (c : AF F) (a : AEF F E) : cAF σ (c • a) = c • cAF σ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add a b ha hb => rw [smul_add, RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, smul_add]
  | tmul a x => rfl

theorem continuous_cAF (σ : E →ₐ[F] E) : Continuous (cAF σ : AEF F E → AEF F E) := by
  let l : AEF F E →ₗ[AF F] AEF F E := { toFun := cAF σ, map_add' := map_add _, map_smul' := cAF_smul σ }
  exact IsModuleTopology.continuous_of_linearMap l

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E)

theorem symplOHF_add_left (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (x + x') y = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_right (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (y + y') = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_smul_left (c : AF F) (x y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (c • x) y = c * symplOHF σ JS JT xi0 x y := by
  have h : hOF σ JS JT (c • x) y = c • hOF σ JS JT x y := by
    unfold hOF
    simp only [Matrix.smul_apply, Finset.smul_sum, mul_smul_comm]
  unfold symplOHF symplOF
  rw [h, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm]

theorem symplOHF_smul_right (c : AF F) (x y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (c • y) = c * symplOHF σ JS JT xi0 x y := by
  have h : hOF σ JS JT x (c • y) = c • hOF σ JS JT x y := by
    unfold hOF
    simp only [Matrix.smul_apply, Finset.smul_sum, cAF_smul, mul_smul_comm, smul_mul_assoc]
  unfold symplOHF symplOF
  rw [h, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm]

theorem symplOHF_zero_left (y : WOF F E nS nT) : symplOHF σ JS JT xi0 0 y = 0 := by
  have := symplOHF_smul_left σ JS JT xi0 0 0 y
  rwa [zero_smul, zero_mul] at this

theorem symplOHF_zero_right (y : WOF F E nS nT) : symplOHF σ JS JT xi0 y 0 = 0 := by
  have := symplOHF_smul_right σ JS JT xi0 0 y 0
  rwa [zero_smul, zero_mul] at this

theorem continuous_symplOHF_left (u : WOF F E nS nT) : Continuous fun w : WOF F E nS nT => symplOHF σ JS JT xi0 w u := by
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  unfold symplOHF symplOF hOF
  refine continuous_const.mul (ht.comp (continuous_const.mul ?_))
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ =>
    continuous_finsetSum _ fun d _ => continuous_const.mul ?_
  exact (continuous_apply a).comp (continuous_apply d)

theorem continuous_symplOHF_right (u : WOF F E nS nT) : Continuous fun w : WOF F E nS nT => symplOHF σ JS JT xi0 u w := by
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  unfold symplOHF symplOF hOF
  refine continuous_const.mul (ht.comp (continuous_const.mul ?_))
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ =>
    continuous_finsetSum _ fun d _ => ((continuous_const.mul ?_).mul continuous_const).mul continuous_const
  exact (continuous_cAF σ).comp ((continuous_apply b).comp (continuous_apply c))

variable {σ JS JT xi0}

theorem smul_finF {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : eInfF F • u = 0 := by
  ext i j; exact smul_eq_zero_of_infF (congrFun (congrFun hu i) j)

end Form

section Main

local instance modTopAEF' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

local instance topRingAEF' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem isThetaFunOF_heisOF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ),
    Continuous ψ → ∀ (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ ψ f →
      IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w₀ f) := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hc w₀ f hf
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL hLf w => ?_⟩
  · simp only [heisOF]
    rw [add_assoc, hf.quasi, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul]
    congr 2
    ring
  · obtain ⟨U, hU, hUf⟩ := hf.level
    let c : WOF F E nS nT →+ AF F :=
      AddMonoidHom.mk' (fun u => symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)
        (fun a b => by simp only [symplOHF_add_left, symplOHF_add_right]; ring)
    let g : WOF F E nS nT →+ AF F :=
      AddMonoidHom.mk' (fun u => pairA F 0 (c u).2) (fun a b => by rw [map_add (f := _)]; exact Prod.ext (add_zero 0).symm rfl)
    let Kψ : AddSubgroup (AF F) :=
      { carrier := {x | ψ x = 1}
        zero_mem' := ψ.map_zero_eq_one
        add_mem' := fun {a b} ha hb => by
          have ha' : ψ a = 1 := ha
          have hb' : ψ b = 1 := hb
          show ψ (a + b) = 1
          rw [AddChar.map_add_eq_mul, ha', hb', one_mul]
        neg_mem' := fun {a} ha => by
          have ha' : ψ a = 1 := ha
          show ψ (-a) = 1
          have := AddChar.map_add_eq_mul ψ (-a) a
          rw [neg_add_cancel, ψ.map_zero_eq_one, ha', mul_one] at this
          exact this.symm }
    let K : AddSubgroup (WOF F E nS nT) := Kψ.comap g
    have hK : IsOpen (K : Set (WOF F E nS nT)) := by
      refine K.isOpen_of_mem_nhds (g := 0) ?_
      have h1 : Continuous fun u : WOF F E nS nT => (c u).2 :=
        continuous_snd.comp ((continuous_symplOHF_left σ JS JT ξ₀ w₀).sub (continuous_symplOHF_right σ JS JT ξ₀ w₀))
      have h2 : (fun u : WOF F E nS nT => (c u).2) ⁻¹' {a | ψ (pairA F 0 a) = 1} ∈ 𝓝 (0 : WOF F E nS nT) := by
        refine h1.continuousAt.preimage_mem_nhds ?_
        rw [map_zero]
        exact ker_fin_mem_nhds hc
      exact Filter.mem_of_superset h2 fun u hu => hu
    refine ⟨U ⊓ K, hU.inter hK, fun u hu hu0 => ?_⟩
    have hfin : c u = pairA F 0 (c u).2 := by
      have h3 : eInfF F * c u = 0 := by
        show eInfF F * (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) = 0
        rw [mul_sub, ← symplOHF_smul_left, ← symplOHF_smul_right, smul_finF hu0, symplOHF_zero_left,
          symplOHF_zero_right, sub_self]
      exact Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl
    have hψc : ψ (c u) = 1 := by
      rw [hfin]
      exact hu.2
    funext w
    have h := congrFun (hUf u hu.1 hu0) (w + w₀)
    simp only [heisOF] at h ⊢
    rw [← h, add_right_comm w u w₀]
    have key : symplOHF σ JS JT ξ₀ w u + symplOHF σ JS JT ξ₀ (w + u) w₀ =
        (symplOHF σ JS JT ξ₀ w w₀ + symplOHF σ JS JT ξ₀ (w + w₀) u) + c u := by
      show _ = _ + (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)
      rw [symplOHF_add_left, symplOHF_add_left]
      ring
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, AddChar.map_add_eq_mul ψ _ (c u),
      hψc, mul_one]
  · exact (hc.comp (continuous_symplOHF_left σ JS JT ξ₀ w₀)).mul (hf.cont.comp (continuous_id.add continuous_const))
  · have hχ : ContDiff ℝ ∞ fun t => ψ (symplOHF σ JS JT ξ₀ (L t) w₀) := by
      refine contDiff_char _ (hc.comp ((continuous_symplOHF_left σ JS JT ξ₀ w₀).comp hL)) (fun s t => ?_) ?_
      · rw [map_add (f := _), symplOHF_add_left, AddChar.map_add_eq_mul]
      · rw [map_zero, symplOHF_zero_left, ψ.map_zero_eq_one]
    have : (fun t => heisOF σ JS JT ξ₀ ψ w₀ f (w + L t)) =
        fun t => ψ (symplOHF σ JS JT ξ₀ w w₀) * (ψ (symplOHF σ JS JT ξ₀ (L t) w₀) * f (w + w₀ + L t)) := by
      funext t
      simp only [heisOF]
      rw [symplOHF_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]
    rw [this]
    exact contDiff_const.mul (hχ.mul (hf.smooth k L hL hLf (w + w₀)))

end Main

end GlobalTheory.HeisKeepF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFPreservesIsThetaFunctionStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ),
    Continuous ψ → ∀ (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ ψ f →
      IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w₀ f) := by
  first | exact @GlobalTheory.HeisKeepF.isThetaFunOF_heisOF | exact GlobalTheory.HeisKeepF.isThetaFunOF_heisOF | (intros; apply GlobalTheory.HeisKeepF.isThetaFunOF_heisOF <;> assumption)
end
end

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}

variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

theorem cut_char (hB : B.IsGood σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {χ : (AEF F E)ˣ →* Circle} {m : ℕ} (hres : ResEtaF χ m) (hε : IsHalfF σ ε) {e : AEF F E} (he : IsSplitIdemF σ e)
    {g : GAF σ J} {x : (AEF F E)ˣ} (hg : SuppAtF σ e J g) (hx : IsDetAtF σ e J g x) :
    χ (GlobalTheory.SplitDetCharF.cutDet σ J ε hε.idem g) = χ x := by
  rcases hε.split e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rw [GlobalTheory.SplitDetCharF.cutDet_same ε hε.idem a1 a2 hg hx]
  · exact GlobalTheory.SplitDetCharF.char_eq_of_mul_conj hB.cm hres _ x
      (GlobalTheory.SplitDetCharF.cutDet_conj hJ ε hε.idem he.1 a1 a2 hg hx)

theorem exists_fin_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (h1 : IsHeckeCharF η)
    (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) : ∃ of, IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of ∧
      ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε hε.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ) := by
  have hB := C.good
  have hreal := GlobalTheory.T.latticeIntertwinerRep_trivial_realPoints F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hheis := GlobalTheory.T.latticeIntertwinerRep_normalizes_heisenberg_finite F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hcont := GlobalTheory.T.latticeIntertwinerRep_continuous_group F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hunit := GlobalTheory.T.lintegral_sq_latticeModelRep_fundamentalDomain F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hsplit := GlobalTheory.T.latticeIntertwinerRep_splitPlace_positive_scalar F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  let z : GAF σ JS × GAF σ JT → Circle := zF σ JS JT η ε hε.idem
  have z1 : z 1 = 1 := by simp [z, zF]
  have z2 : ∀ p q, z (p * q) = z p * z q := fun p q => by
    simp only [z, zF, Prod.fst_mul, Prod.snd_mul, map_mul, _root_.mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have z3 : Continuous z := by
    show Continuous fun p : GAF σ JS × GAF σ JT =>
      ((η ^ nT) (GlobalTheory.SplitDetCharF.cutDet σ JS ε hε.idem p.1))⁻¹ * (η ^ nS) (GlobalTheory.SplitDetCharF.cutDet σ JT ε hε.idem p.2)
    exact ((isHeckeCharF_pow h1 nT).1.comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_fst)).inv.mul
      ((isHeckeCharF_pow h1 nS).1.comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_snd))
  obtain ⟨om, hom⟩ := exists_extend (thetaSubF σ JS JT ξ₀ B.ψ)
    ({ toFun := fun p => (z p : ℂ) • Om p
       map_one' := by rw [z1, Circle.coe_one, one_smul, map_one]
       map_mul' := fun p q => by rw [z2, map_mul, Circle.coe_mul, smul_mul_smul_comm] } :
      GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ))
  have ho : ∀ p f (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f),
      om p f = (z p : ℂ) • (Om p ⟨f, hf⟩ : WOF F E nS nT → ℂ) :=
    fun p f hf => hom p ⟨f, hf⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf u => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk u f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩, fun p f => hom p f⟩
  · rw [ho p f hf]
    exact (thetaSubF σ JS JT ξ₀ B.ψ).smul_mem _ (Om p ⟨f, hf⟩).2
  · simp only [ho _ f hf, Pi.smul_apply, smul_eq_mul]
    exact (continuous_subtype_val.comp z3).mul (hcont ⟨f, hf⟩ u)
  · rw [← hunit μ 𝓕 hμ h𝓕 p ⟨f, hf⟩, ho p f hf]
    refine lintegral_congr fun u => ?_
    rw [Pi.smul_apply, enorm_smul, ← ofReal_norm_eq_enorm (z p : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]
  · rw [ho _ f hf, hreal g hg k hk, show z (g, k) = 1 by
      simp [z, zF, GlobalTheory.SplitDetCharF.cutDet_real ε hε.idem hε.fin g hg, GlobalTheory.SplitDetCharF.cutDet_real ε hε.idem hε.fin k hk],
      Circle.coe_one, one_smul]
  · have hf' := GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction F E σ nS nT JS JT ξ₀ B.ψ hB.std.1 u f hf
    rw [ho _ f hf, ho _ _ hf', heisOF_smul, hheis g hg k hk u ⟨f, hf⟩ ⟨_, hf'⟩ rfl]
  · obtain ⟨r, hr, h1⟩ := hsplit e he g k hg hk
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [ho _ f hf, map_smul, h1 ℓ hℓ, smul_eq_mul,
      show z (g, k) = splitFacOF (η ^ nS) (η ^ nT) x y by
        simp only [z, zF, splitFacOF, cut_char hB C.hS (resEtaF_pow h2 nT) hε he hg hx,
          cut_char hB C.hT (resEtaF_pow h2 nS) hε he hk hy]]
    ring

theorem fin_inf_comm_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ)
    (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨z, hz⟩ := hof p
  have hσ : ∀ x, σ (σ x) = x := LatA.sig_sig C.good
  obtain ⟨a, ha, k, hk, e1, -⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nS JS q.1
  obtain ⟨b, hb, l, hl, e2, -⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nT JT q.2
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi q f = oi (a, b) f := fun f h => by
    rw [show q = (a, b) * (k, l) from Prod.ext e1 e2, map_mul, Module.End.mul_apply, hi.triv k hk l hl f h]
  let L : thetaSubF σ JS JT ξ₀ B.ψ →ₗ[ℂ] thetaSubF σ JS JT ξ₀ B.ψ := (oi q).restrict fun f hf => hi.pres q f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = oi q m := fun _ => rfl
  have := congrArg Subtype.val ((LatA.rep hO).comm (LatA.sys hσ C.hS C.hT C.hξ hO) L (fun x v => Subtype.ext (by
    have e3 : actOF σ JS JT a b x = x := by
      have := congrArg (fun y : XFF F E nS nT => (y : WOF F E nS nT)) (LatA.rhoFF_real ha hb x)
      rwa [coe_rhoFF] at this
    rw [hL, coe_opFF, coe_opFF, hL, map_smul, hoi _ (hc _ _ v.2), hi.Heisenberg₂ a ha b hb _ _ v.2, e3, ← hoi _ v.2])) p ⟨f, hf⟩)
  rw [hz ⟨f, hf⟩, map_smul, ← hL, ← this]
  exact hz (L ⟨f, hf⟩)

theorem eventually_smul_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f) :
    ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∃ c : ℂ, of p f = c • f := by
  filter_upwards [LatA.eventually_fix (LatA.sig_sig C.good) C.hS C.hT C.hξ hO ⟨f, h1⟩] with p hp
  obtain ⟨c, hc'⟩ := hof p
  exact ⟨c, by rw [hc' ⟨f, h1⟩, hp]⟩

theorem continuous_product_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f)
    (u : WOF F E nS nT) : Continuous fun p : GAF σ JS × GAF σ JT => of p (oi p f) u := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : IsTopologicalGroup (GAF σ JS) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JS))
  haveI : IsTopologicalGroup (GAF σ JT) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JT))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (eventually_smul_A C hO hof h3)] with p hp
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    rw [fin_inf_comm_A C hO hof hi p p f h1, hc', h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [fin_inf_comm_A C hO hof hi p p f h1, hc', map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']

theorem datum_of_aut_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hη : IsHeckeCharF η) (hres : ResEtaF η 1) (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (haut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of (γ, γ') (oi (γ, γ') f) 0 = f 0) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω := by
  have hB := C.good
  have hψ := GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB
  have hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f) :=
    fun p q f h => fin_inf_comm_A C hO hof hi p q f h
  have hth : ∀ (w₀ : WOF F E nS nT) f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
      IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) :=
    fun w₀ f h => GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction F E σ nS nT JS JT ξ₀ B.ψ hB.std.1 w₀ f h
  let Th := thetaSubF σ JS JT ξ₀ B.ψ
  let Om2 : GAF σ JS × GAF σ JT →* Module.End ℂ Th :=
    { toFun := fun p => (of p * oi p).restrict (p := Th) (q := Th) fun f h1 => hf.pres p _ (hi.pres p f h1)
      map_one' := LinearMap.ext fun f => Subtype.ext (by
        show of 1 (oi 1 f) = f
        simp only [map_one, Module.End.one_apply])
      map_mul' := fun p q => LinearMap.ext fun f => Subtype.ext (by
        show of (p * q) (oi (p * q) f) = of p (oi p (of q (oi q (f : WOF F E nS nT → ℂ))))
        simp only [map_mul, Module.End.mul_apply]
        rw [hcomm q p _ (hi.pres q _ f.2)]) }
  obtain ⟨om, hom⟩ := exists_extend Th Om2
  have ho : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → om p f = of p (oi p f) := fun p f h1 => hom p ⟨f, h1⟩
  have hp : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (om p f) := fun p f h1 => by
    rw [ho p f h1]
    exact hf.pres p _ (hi.pres p f h1)
  refine ⟨om, hψ, isHeckeCharF_pow hη _, isHeckeCharF_pow hη _, resEtaF_pow hres _, resEtaF_pow hres _, hp,
    fun g h w₀ f h1 => ?_, fun γ hγ γ' hγ' f h1 => ?_, fun f h1 w => ?_, fun μ 𝓕 hμ h𝓕 p f h1 => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩
  · obtain ⟨a, ha, k, hk, e1, e1'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nS JS g
    obtain ⟨b, hb, l, hl, e2, e2'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nT JT h
    have key : ∀ x, IsThetaFunOF σ JS JT ξ₀ B.ψ x → om (g, h) x = of (k, l) (oi (a, b) x) := fun x hx => by
      rw [ho _ x hx]
      have E1 : ((g, h) : GAF σ JS × GAF σ JT) = (a, b) * (k, l) := Prod.ext e1 e2
      have E2 : ((g, h) : GAF σ JS × GAF σ JT) = (k, l) * (a, b) := Prod.ext e1' e2'
      have E3 : oi (g, h) x = oi (a, b) x := by rw [E1, map_mul, Module.End.mul_apply, hi.triv k hk l hl x hx]
      rw [E3, E2, map_mul, Module.End.mul_apply, hf.triv a ha b hb _ (hi.pres _ x hx)]
    rw [key _ (hth w₀ f h1), key f h1, hi.Heisenberg₂ a ha b hb w₀ f h1, hf.Heisenberg₂ k hk l hl _ _ (hi.pres _ f h1),
      ← actOF_mul, ← e1', ← e2']
  · rw [ho _ f h1]
    exact haut γ hγ γ' hγ' f h1
  · have e : (fun p => om p f w) = fun p => of p (oi p f) w := funext fun p => by rw [ho p f h1]
    rw [e]
    exact continuous_product_A C hO hf hof hi h1 w
  · rw [ho p f h1, hf.unit μ 𝓕 hμ h𝓕 p _ (hi.pres p f h1), hi.unit μ 𝓕 hμ h𝓕 p f h1]
  · obtain ⟨r, hr, h2⟩ := hf.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f h1 => ?_⟩
    rw [ho _ f h1, hi.triv g (mem_GfCF_of_suppAt he hg) h (mem_GfCF_of_suppAt he hh) f h1]
    exact h2 ℓ hℓ f h1

end PositivityTheory.ThKW

end

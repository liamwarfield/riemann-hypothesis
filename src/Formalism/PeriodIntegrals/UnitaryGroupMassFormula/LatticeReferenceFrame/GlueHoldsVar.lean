module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Development

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HGNsmulRight
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HypsNonvacuous
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.UnitaryGroupMassFormula

variable (I : Formalism.MainNotions.S.AutInst)

theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by
  simp [hA, Formalism.UG.hform]

theorem zmod_one_of_mem {c : I.E ⊗[I.F] Af I.F} (h : c ∈ IntAf I.F I.E) : ZMod' I 1 c := by
  unfold ZMod'
  exact ⟨c, h, by simp⟩

theorem mL_one : mL I 1 = I.Lf := by
  unfold mL
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  · intro x hx
    exact Submodule.subset_span ⟨x, hx, by simp⟩

theorem ite_mem_int {p : Prop} [Decidable p] (x : I.E ⊗[I.F] Af I.F) (hx : x ∈ IntAf I.F I.E) :
    (if p then x else 0) ∈ IntAf I.F I.E := by
  split_ifs
  · exact hx
  · exact zero_mem _

def frameOne (r k : ℕ) (e f : Fin r → Fin I.n → I.E)
    (he : ∀ a, InAt I 1 1 (incl I (e a)) ∧ InAt I 1 1 (incl I (f a))) : RefData I 1 r k e f where
  e0 := fun _ => 0
  f0 := fun _ => 0
  z0 := 0
  bw := fun _ => 0
  bwd := fun _ => 0
  ew := 0
  vectorsInLattice := ⟨fun _ => ⟨zero_mem _, zero_mem _⟩, zero_mem _, fun _ => ⟨zero_mem _, zero_mem _⟩⟩
  basisApprox := by
    intro a
    constructor
    · obtain ⟨c, hc, hm⟩ := (he a).1
      exact ⟨c, hc, by rw [zero_sub, smul_neg]; exact neg_mem hm⟩
    · obtain ⟨c, hc, hm⟩ := (he a).2
      exact ⟨c, hc, by rw [zero_sub, smul_neg]; exact neg_mem hm⟩
  gramIntegral := by
    intro a b
    refine ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left, zero_sub]; exact neg_mem (ite_mem_int I 1 (one_mem _))
  formsAtZero := by
    refine ⟨zmod_one_of_mem I ?_, fun a => ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩⟩
    · rw [hA_zero_left, zero_add]; exact one_mem _
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left]; exact zero_mem _
  weightVectorsIntegral := by
    intro i
    refine ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, fun a => ⟨zmod_one_of_mem I ?_,
      zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩⟩ <;>
      (rw [hA_zero_left]; exact zero_mem _)
  ew_idem := by simp
  ew_orth := by simp
  ew_int := zero_mem _
  ew_full := by
    intro y hy
    rw [map_zero, sub_zero, sub_zero, one_smul, mL_one]
    exact hy
  bw_w := fun _ => by simp
  bwd_w := fun _ => by simp
  bw_dual := by
    intro i j
    apply zmod_one_of_mem
    rw [hA_zero_left, zero_sub]
    exact neg_mem (ite_mem_int I 0 (zero_mem _))
  latticeSpan := by
    intro y hy
    apply Submodule.mem_sup_right
    rw [mL_one]
    exact hy

theorem refData_one (r k : ℕ) (e f : Fin r → Fin I.n → I.E)
    (he : ∀ a, InAt I 1 1 (incl I (e a)) ∧ InAt I 1 1 (incl I (f a))) :
    Nonempty (RefData I 1 r k e f) := ⟨frameOne I r k e f he⟩

def TargetTwo : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E), 2 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    Nonempty (RefData I g r k e f)

theorem target_of_two (h : TargetTwo) : Target := by
  unfold TargetTwo at h
  unfold Target
  intro J g r k e f hg hs hn he hf hef hin
  rcases Nat.lt_or_ge g 2 with hlt | hge
  · obtain rfl : g = 1 := by omega
    exact refData_one J r k e f hin
  · exact h J g r k e f hge hs hn he hf hef hin

end PI.ScRefExists.UnitaryGroupMassFormula

end
end

noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.GlueB

open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.Sk

section Lemmas

variable (I : Formalism.MainNotions.S.AutInst) (g : ℕ)

theorem zmod_zero : ZMod' I g 0 := ⟨0, zero_mem _, by simp⟩

theorem zmod_of_GE {x : I.E} (h : GE I g x) : ZMod' I g (Formalism.UG.inclE (F := I.F) (Af I.F) x) := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E), inclE_mem' I t, by rw [map_mul, map_natCast]⟩

theorem zmod_add {x y : I.E ⊗[I.F] Af I.F} (h1 : ZMod' I g x) (h2 : ZMod' I g y) :
    ZMod' I g (x + y) := by
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, rfl⟩ := h2
  exact ⟨a + b, add_mem ha hb, (mul_add _ _ _).symm⟩

theorem zmod_mul_int {x y : I.E ⊗[I.F] Af I.F} (h : ZMod' I g x) (hy : y ∈ IntAf I.F I.E) :
    ZMod' I g (x * y) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a * y, mul_mem ha hy, mul_assoc _ _ _⟩

theorem zmod_eps {ε : I.E ⊗[I.F] Af I.F} {θ : I.E}
    (hε : ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) θ)) {x : I.E}
    (hx : x ∈ (algebraMap (𝓞 I.E) I.E).range) (h : GE I g (θ * x)) :
    ZMod' I g (ε * Formalism.UG.inclE (F := I.F) (Af I.F) x) := by
  obtain ⟨s, rfl⟩ := hx
  have h1 := zmod_mul_int I g hε (inclE_mem' I s)
  have h2 := zmod_add I g h1 (zmod_of_GE I g h)
  convert h2 using 1
  rw [map_mul]
  have e : algebraMap (𝓞 I.E) I.E s = (s : I.E) := rfl
  rw [e]
  ring

theorem zmod_sig {ε : I.E ⊗[I.F] Af I.F} {θ : I.E}
    (hε : ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) θ)) :
    ZMod' I g (sigA I ε - Formalism.UG.inclE (F := I.F) (Af I.F) (star θ)) := by
  obtain ⟨t, ht, he⟩ := hε
  have hinc : ∀ a : I.E, sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) (a ⊗ₜ[I.F] (1 : Af I.F)) =
      (star a) ⊗ₜ[I.F] (1 : Af I.F)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hcl : Subring.closure (Set.range (fun x : Formalism.UG.intOE I.E => (x : I.E) ⊗ₜ[I.F] (1 : Af I.F)) ∪
      Set.range (fun y : Formalism.UG.intAd I.F => (1 : I.E) ⊗ₜ[I.F] (y : Af I.F))) ≤
      (IntAf I.F I.E).comap (sigA I) := by
    rw [Subring.closure_le]
    rintro _ (⟨⟨s, hs⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨s', rfl⟩ := hs
      show sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E s')) ∈ IntAf I.F I.E
      rw [hinc]
      have hi : IsIntegral ℤ (star (algebraMap (𝓞 I.E) I.E s')) :=
        IsIntegral.map (starRingEnd I.E).toIntAlgHom (NumberField.RingOfIntegers.isIntegral_coe s')
      exact inclE_mem' I ⟨_, hi⟩
    · show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) ((1 : I.E) ⊗ₜ[I.F] (y : Af I.F)) ∈
        IntAf I.F I.E
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  refine ⟨sigA I t, hcl ht, ?_⟩
  rw [← hinc, ← map_sub, he, map_mul, map_natCast]

theorem hG_nsmul_left (m : ℕ) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J (m • x) y = (m : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_nsmul_right (m : ℕ) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x (m • y) = (m : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_mL {x : VA I} (hx : x ∈ I.Lf) : ((g : ℕ) : I.E ⊗[I.F] Af I.F) • x ∈ mL I g :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem incl_osmul (c : 𝓞 I.E) (x : Fin I.n → I.E) :
    incl I (c • x) = (⟨Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E), inclE_mem' I c⟩ : IntAf I.F I.E) •
      incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
  rfl

theorem mem_L_of (h3 : LocGlob) {x : Fin I.n → I.E} (hx : incl I x ∈ I.Lf) : x ∈ I.L := by
  refine (I.L_dual x).mpr fun y hy => ?_
  let H : VA I → I.E ⊗[I.F] Af I.F := fun v =>
    ∑ i, ∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E (y i) * I.J i j) * v j
  have hinc : ∀ z : Fin I.n → I.E, H (incl I z) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J y z) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, incl, Formalism.UG.hform, map_sum, map_mul]
  have key : ∀ v ∈ I.Lf, H v ∈ IntAf I.F I.E := by
    intro v hv
    change v ∈ Submodule.span _ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      change H (incl I (z : Fin I.n → I.E)) ∈ IntAf I.F I.E
      obtain ⟨s, hs⟩ := (I.L_dual z).mp z.2 y hy
      rw [hinc, ← hs]
      exact inclE_mem' I s
    | zero => simp [H]
    | add a b _ _ ha hb =>
      have e : H (a + b) = H a + H b := by
        simp only [H, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [e]
      exact add_mem ha hb
    | smul a v _ hv =>
      have e : H (a • v) = (a : I.E ⊗[I.F] Af I.F) * H v := by
        simp only [H, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]
      exact mul_mem a.2 hv
  have hm := key _ hx
  rw [hinc x] at hm
  obtain ⟨s, hs⟩ := h3 I _ hm
  exact ⟨s, hs⟩

theorem incl_nsmul' (m : ℕ) (x : Fin I.n → I.E) : incl I (m • x) = m • incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, map_nsmul]

theorem ge_of_nat {x : I.E} (m : ℕ) (h : x = (g : I.E) * (m : I.E)) : GE I g x :=
  ⟨(m : 𝓞 I.E), by rw [h]; exact congrArg _ (map_natCast (algebraMap (𝓞 I.E) I.E) m).symm⟩

end Lemmas

end PI.ScRefExists.GlueB

end
end

noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.GlueC

open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.GlueB PI.ScRefExists.Sk

theorem glue_holds_var : Glue := by
  intro h1 h2 h3 h4
  apply PI.ScRefExists.UnitaryGroupMassFormula.target_of_two
  intro I g r k e f hg hs hn he hf hef hi
  have hg1 : 1 ≤ g := by omega
  have hc : ∀ x : Fin I.n → I.E, InAt I g 1 (incl I x) → ∃ c : ℕ, Nat.Coprime c g ∧ c • x ∈ I.L := by
    rintro x ⟨c, hcg, hm⟩
    refine ⟨c, hcg, mem_L_of I h3 ?_⟩
    rw [incl_nsmul, ← PI.ScRefExists.UnitaryGroupMassFormula.mL_one]
    exact hm
  choose ce hce hceL using fun a => hc (e a) (hi a).1
  choose cf hcf hcfL using fun a => hc (f a) (hi a).2
  obtain ⟨M, hM, hMef⟩ : ∃ M : ℕ, Nat.Coprime M g ∧ ∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L := by
    refine ⟨∏ a, ce a * cf a, Nat.coprime_prod_left_iff.2 (fun a _ => Nat.Coprime.mul_left (hce a) (hcf a)),
      fun a => ?_⟩
    obtain ⟨d, hd⟩ : ce a * cf a ∣ ∏ a, ce a * cf a := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
    constructor
    · rw [hd, show ce a * cf a * d = (cf a * d) * ce a by ring, mul_smul]
      exact nsmul_mem (hceL a) _
    · rw [hd, show ce a * cf a * d = (ce a * d) * cf a by ring, mul_smul]
      exact nsmul_mem (hcfL a) _
  obtain ⟨Q, -, hQ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hM (by omega : 1 < g)
  obtain ⟨s, hN⟩ : ∃ s : ℕ, M * Q = 1 + g * s :=
    ⟨M * Q / g, by have := Nat.div_add_mod (M * Q) g; rw [hQ] at this; linarith⟩
  have hNE : (M : I.E) * (Q : I.E) = 1 + (g : I.E) * (s : I.E) := by exact_mod_cast hN
  obtain ⟨θ, hθ⟩ := h1 I g hg1 hs
  obtain ⟨ε, hεi, hεe, hεo, hεθ⟩ := h2 I g θ hg1 hs hθ
  obtain ⟨z, b, bd, hz, hb, hez, heb, hzz, hzb, hbb, hspan⟩ :=
    h4 I g r k θ e f M hg1 hs hθ hn he hf hef hM hMef
  simp only [Sk.hG] at hez heb hzz hzb hbb
  obtain ⟨t, ht, hεt⟩ := id hεθ
  obtain ⟨t', ht', hσt⟩ := zmod_sig I g hεθ
  refine ⟨{
    e0 := fun a => incl I (Q • M • e a)
    f0 := fun a => incl I (Q • M • f a)
    z0 := incl I z
    bw := fun i => ε • incl I (b i)
    bwd := fun i => sigA I ε • incl I (bd i)
    ew := ε
    vectorsInLattice := ?_
    basisApprox := ?_
    gramIntegral := ?_
    formsAtZero := ?_
    weightVectorsIntegral := ?_
    ew_idem := hεe
    ew_orth := hεo
    ew_int := hεi
    ew_full := ?_
    bw_w := ?_
    bwd_w := ?_
    bw_dual := ?_
    latticeSpan := ?_ }⟩
  · exact ⟨fun a => ⟨incl_mem_Lf I (nsmul_mem (hMef a).1 Q), incl_mem_Lf I (nsmul_mem (hMef a).2 Q)⟩,
      incl_mem_Lf I hz, fun i => ⟨smul_mem_Lf I hεi (incl_mem_Lf I (hb i).1),
        smul_mem_Lf I (sigA_mem I hεi) (incl_mem_Lf I (hb i).2)⟩⟩
  · intro a
    have key : ∀ x : Fin I.n → I.E, M • x ∈ I.L → InAt I g g (incl I (Q • M • x) - incl I x) := by
      intro x hx
      refine ⟨M, hM, ?_⟩
      have h' : ((M : ℕ) : I.E ⊗[I.F] Af I.F) • (incl I (Q • M • x) - incl I x) =
          ((g : ℕ) : I.E ⊗[I.F] Af I.F) • incl I (s • M • x) := by
        rw [← incl_sub, ← incl_nsmul, ← incl_nsmul]
        congr 1
        funext i
        simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
        linear_combination ((M : I.E) * x i) * hNE
      rw [h']
      exact mem_mL I g (incl_mem_Lf I (nsmul_mem hx s))
    exact ⟨key _ (hMef a).1, key _ (hMef a).2⟩
  · intro a b'
    refine ⟨?_, ?_, ?_⟩
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (incl I (Q • M • e b')))
      rw [hA_incl]
      simp only [hG_nsmul_left, hG_nsmul_right, he a b', mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • f a)) (incl I (Q • M • f b')))
      rw [hA_incl]
      simp only [hG_nsmul_left, hG_nsmul_right, hf a b', mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (incl I (Q • M • f b')) - if a = b' then 1 else 0)
      rw [hA_incl]
      simp only [hG_nsmul_left, hG_nsmul_right, hef a b']
      split_ifs with hab
      · rw [mul_one, ← map_one (Formalism.UG.inclE (F := I.F) (Af I.F)), ← map_sub]
        apply zmod_of_GE
        apply ge_of_nat I g (s * (M * Q + 1))
        push_cast
        linear_combination ((M : I.E) * (Q : I.E) + 1) * hNE
      · simp only [mul_zero, map_zero, sub_zero]
        exact zmod_zero I g
  · refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
    · show ZMod' I g (hA I (incl I z) (incl I z) + 1)
      rw [hA_incl, ← map_one (Formalism.UG.inclE (F := I.F) (Af I.F)), ← map_add (f := _)]
      exact zmod_of_GE I g hzz
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (incl I z))
      rw [hA_incl]
      simp only [hG_nsmul_left, (hez a).1, mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • f a)) (incl I z))
      rw [hA_incl]
      simp only [hG_nsmul_left, (hez a).2, mul_zero, map_zero]
      exact zmod_zero I g
  · intro i
    refine ⟨?_, ?_, fun a => ⟨?_, ?_, ?_, ?_⟩⟩
    · show ZMod' I g (hA I (incl I z) (ε • incl I (b i)))
      rw [hA_smul_right, hA_incl]
      exact zmod_eps I g hεθ (hG_int I hz (hb i).1) (hzb i).1
    · show ZMod' I g (hA I (incl I z) (sigA I ε • incl I (bd i)))
      rw [hA_smul_right, hA_incl]
      exact zmod_eps I g (zmod_sig I g hεθ) (hG_int I hz (hb i).2) (hzb i).2
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (ε • incl I (b i)))
      rw [hA_smul_right, hA_incl]
      simp only [hG_nsmul_left, (heb a i).1, mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • f a)) (ε • incl I (b i)))
      rw [hA_smul_right, hA_incl]
      simp only [hG_nsmul_left, (heb a i).2.1, mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (sigA I ε • incl I (bd i)))
      rw [hA_smul_right, hA_incl]
      simp only [hG_nsmul_left, (heb a i).2.2.1, mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • f a)) (sigA I ε • incl I (bd i)))
      rw [hA_smul_right, hA_incl]
      simp only [hG_nsmul_left, (heb a i).2.2.2, mul_zero, map_zero]
      exact zmod_zero I g
  · intro y hy
    obtain ⟨u, hu⟩ := hθ.2.2
    have e1 : 1 - ε - sigA I ε = ((g : ℕ) : I.E ⊗[I.F] Af I.F) *
        (Formalism.UG.inclE (F := I.F) (Af I.F) (u : I.E) - t - t') := by
      have hu' := congrArg (Formalism.UG.inclE (F := I.F) (Af I.F)) hu
      rw [map_sub, map_sub, map_one, map_mul, map_natCast] at hu'
      linear_combination hu' - hεt - hσt
    rw [e1, mul_smul]
    exact mem_mL I g (smul_mem_Lf I (sub_mem (sub_mem (inclE_mem' I u) ht) ht') hy)
  · intro i
    show ε • incl I (b i) = ε • ε • incl I (b i)
    rw [smul_smul, hεe]
  · intro i
    show sigA I ε • incl I (bd i) = sigA I ε • sigA I ε • incl I (bd i)
    rw [smul_smul, ← map_mul, hεe]
  · intro i j
    show ZMod' I g (hA I (sigA I ε • incl I (bd i)) (ε • incl I (b j)) - if i = j then ε else 0)
    rw [hA_smul_left, hA_smul_right, sigA_sigA, hA_incl]
    have e2 : ε * (ε * Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J (bd i) (b j))) -
        (if i = j then ε else 0) = ε * Formalism.UG.inclE (F := I.F) (Af I.F)
          (Formalism.UG.hform (starRingEnd I.E) I.J (bd i) (b j) - if i = j then 1 else 0) := by
      split_ifs
      · rw [map_sub, map_one, ← mul_assoc, hεe]; ring
      · rw [sub_zero, sub_zero, ← mul_assoc, hεe]
    rw [e2]
    refine zmod_eps I g hεθ (sub_mem (hG_int I (hb i).2 (hb j).1) ?_) (hbb i j)
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro y hy
    let S : Set (VA I) := Set.range (fun a => incl I (Q • M • e a)) ∪
      Set.range (fun a => incl I (Q • M • f a)) ∪ {incl I z} ∪ Set.range (fun i => ε • incl I (b i)) ∪
      Set.range (fun i => sigA I ε • incl I (bd i))
    show y ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g
    have hSe : ∀ a, incl I (Q • M • e a) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := fun a =>
      Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩)))))
    have hSf : ∀ a, incl I (Q • M • f a) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := fun a =>
      Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))))
    have hSz : incl I z ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g :=
      Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inl (Or.inr rfl))))
    have hSb : ∀ i, ε • incl I (b i) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := fun i =>
      Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))
    have hSbd : ∀ i, sigA I ε • incl I (bd i) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := fun i =>
      Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
    let T : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
      { carrier := {x | incl I x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g}
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_ofPred_eq, incl_add] at *
          exact add_mem hx hy
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, incl_zero]
          exact zero_mem _
        smul_mem' := fun c x hx => by
          simp only [Set.mem_ofPred_eq] at *
          rw [incl_osmul]
          exact Submodule.smul_mem _ _ hx }
    have memT : ∀ x, incl I x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g → x ∈ T := fun x h => h
    have hgT : gL I g ≤ T := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      refine memT _ ?_
      rw [incl_smul, ← natCast_eq]
      exact Submodule.mem_sup_right (mem_mL I g (incl_mem_Lf I hx))
    have hST : Submodule.span (𝓞 I.E) (Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪
        {z} ∪ Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)) ≤ T := by
      refine Submodule.span_le.2 ?_
      rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · refine memT _ ?_
        have h' : incl I (M • e a) = M • incl I (Q • M • e a) -
            ((g : ℕ) : I.E ⊗[I.F] Af I.F) • incl I (s • M • e a) := by
          rw [← incl_nsmul', ← incl_nsmul, ← incl_sub]
          congr 1
          funext i
          simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
          linear_combination (-(M : I.E) * e a i) * hNE
        rw [h']
        exact sub_mem (nsmul_mem (hSe a) M)
          (Submodule.mem_sup_right (mem_mL I g (incl_mem_Lf I (nsmul_mem (hMef a).1 s))))
      · refine memT _ ?_
        have h' : incl I (M • f a) = M • incl I (Q • M • f a) -
            ((g : ℕ) : I.E ⊗[I.F] Af I.F) • incl I (s • M • f a) := by
          rw [← incl_nsmul', ← incl_nsmul, ← incl_sub]
          congr 1
          funext i
          simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
          linear_combination (-(M : I.E) * f a i) * hNE
        rw [h']
        exact sub_mem (nsmul_mem (hSf a) M)
          (Submodule.mem_sup_right (mem_mL I g (incl_mem_Lf I (nsmul_mem (hMef a).2 s))))
      · exact memT _ hSz
      · refine memT _ ?_
        have h' : incl I ((θ : I.E) • b i) = ε • incl I (b i) -
            ((g : ℕ) : I.E ⊗[I.F] Af I.F) • (t • incl I (b i)) := by
          rw [incl_smul, smul_smul, ← sub_smul]
          congr 1
          linear_combination -hεt
        rw [h']
        exact sub_mem (hSb i)
          (Submodule.mem_sup_right (mem_mL I g (smul_mem_Lf I ht (incl_mem_Lf I (hb i).1))))
      · refine memT _ ?_
        have h' : incl I (star (θ : I.E) • bd i) = sigA I ε • incl I (bd i) -
            ((g : ℕ) : I.E ⊗[I.F] Af I.F) • (t' • incl I (bd i)) := by
          rw [incl_smul, smul_smul, ← sub_smul]
          congr 1
          linear_combination -hσt
        rw [h']
        exact sub_mem (hSbd i)
          (Submodule.mem_sup_right (mem_mL I g (smul_mem_Lf I ht' (incl_mem_Lf I (hb i).2))))
    have hLT : I.Lf ≤ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      show incl I x ∈ _
      exact (sup_le hST hgT) (hspan x hx)
    exact hLT hy

end PI.ScRefExists.GlueC

end

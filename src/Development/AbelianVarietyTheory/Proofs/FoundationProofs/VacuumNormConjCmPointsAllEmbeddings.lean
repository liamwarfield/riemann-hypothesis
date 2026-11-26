module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSelfDualPairGaloisConjugateHomLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHermSesqOf
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OfDualFamilies
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ConjNorm.Line

variable {D : D7} {N N' : ℕ}

def sq (z w : VC D N N') : ℂ := ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)

theorem Hf_eq (T : Tor D) (z w : VC D N N') : Hf D T z w = sq z w / (area T.abelian₂ : ℂ) := rfl

theorem im_Hf (T : Tor D) (z w : VC D N N') : (Hf D T z w).im = (sq z w).im / area T.abelian₂ := by
  rw [Hf_eq, Complex.div_ofReal_im]

theorem sq_smul_left (c : ℂ) (z w : VC D N N') : sq (c • z) w = c * sq z w := by
  simp [sq, Finset.mul_sum, mul_assoc]

theorem sq_smul_right (c : ℂ) (z w : VC D N N') : sq z (c • w) = sq z w * (starRingEnd ℂ) c := by
  simp only [sq, Finset.sum_mul, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem sq_add_left (z z' w : VC D N N') : sq (z + z') w = sq z w + sq z' w := by
  simp [sq, add_mul, Finset.sum_add_distrib]

theorem sq_add_right (z w w' : VC D N N') : sq z (w + w') = sq z w + sq z w' := by
  simp [sq, mul_add, Finset.sum_add_distrib]

theorem sq_neg_left (z w : VC D N N') : sq (-z) w = -sq z w := by simp [sq]

theorem sq_neg_right (z w : VC D N N') : sq z (-w) = -sq z w := by simp [sq]

theorem sq_zero_left (w : VC D N N') : sq 0 w = 0 := by simp [sq]

theorem sq_zero_right (w : VC D N N') : sq w 0 = 0 := by simp [sq]

theorem sq_self_im (z : VC D N N') : (sq z z).im = 0 := by
  simp [sq, Complex.im_sum, Complex.mul_conj]

theorem continuous_sq (w : VC D N N') : Continuous fun z : VC D N N' => sq z w := by
  unfold sq; fun_prop

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem embV_apply (x : Matrix (Fin N') (Fin N) D.host.E) (τ i j) :
    embV D (tor0 D cc δ) x τ i j = embT D τ (x i j) := rfl

theorem sq_embV (hG : admG1 D) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    sq (embV D (tor0 D cc δ) x) (embV D (tor0 D cc δ) y) =
      D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) := by
  rw [hYY, ← hG.2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, embV_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [D.host.toHostAx.conjE_apply]

theorem embV_smul (hG : admG1 D) (a : D.host.K) (x : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (a • x) = D.host.φ₀ (a : D.host.E) • embV D (tor0 D cc δ) x := by
  funext τ i j
  simp only [embV_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, ← hG.1 τ a, ← map_mul]
  rfl

theorem embV_sum {ι : Type} (s : Finset ι) (x : ι → Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (∑ i ∈ s, x i) = ∑ i ∈ s, embV D (tor0 D cc δ) (x i) := by
  funext τ i j
  simp [embV_apply, Matrix.sum_apply, Finset.sum_apply]

theorem span_embT (D : D7) :
    Submodule.span ℂ (Set.range fun (t : D.host.E) (τ : D.what₂.Tau) => embT D τ t) = ⊤ := by
  have hinj : Function.Injective fun τ : D.what₂.Tau => (embT D τ : D.host.E →* ℂ) := by
    intro τ τ' h
    have h1 : embT D τ = embT D τ' := RingHom.ext fun x => DFunLike.congr_fun h x
    exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h1))
  have hli := (linearIndependent_monoidHom D.host.E ℂ).comp _ hinj
  exact span_flip_eq_top_iff_linearIndependent.2 hli

theorem expand (hG : admG1 D) {r : ℕ} (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (h : ∀ x, x = ∑ i, hYY D x (y' i) • y i) (z : VC D N N') :
    z = ∑ i, sq z (embV D (tor0 D cc δ) (y' i)) • embV D (tor0 D cc δ) (y i) := by
  let P : Submodule ℂ (VC D N N') :=
    { carrier := {z | z = ∑ i, sq z (embV D (tor0 D cc δ) (y' i)) • embV D (tor0 D cc δ) (y i)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, sq_add_left, add_smul, Finset.sum_add_distrib] at *
        rw [← ha, ← hb]
      zero_mem' := by simp [sq_zero_left]
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, sq_smul_left, mul_smul, ← Finset.smul_sum] at *
        rw [← ha] }
  have hP : ∀ x, embV D (tor0 D cc δ) x ∈ P := fun x => by
    change _ = _
    conv_lhs => rw [h x]
    simp only [embV_sum, embV_smul cc δ hG, sq_embV cc δ hG]
  have hc : ∀ a b (c : D.what₂.Tau → ℂ),
      (fun τ i j => if a = i ∧ b = j then c τ else 0 : VC D N N') ∈ P := by
    intro a b c
    have hc : c ∈ Submodule.span ℂ
      (Set.range fun (t : D.host.E) (τ : D.what₂.Tau) => embT D τ t) := span_embT D ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      convert hP (Matrix.single a b t) using 1
      funext τ i j
      rw [embV_apply, Matrix.single_apply]
      split_ifs <;> simp
    | zero => convert P.zero_mem using 1; funext τ i j; simp
    | add x x' _ _ hx hx' =>
      convert P.add_mem hx hx' using 1; funext τ i j
      simp only [Pi.add_apply]; split_ifs <;> simp
    | smul t x _ hx =>
      convert P.smul_mem t hx using 1; funext τ i j
      simp only [Pi.smul_apply]; split_ifs <;> simp
  have hz : z = ∑ a, ∑ b, (fun τ i j => if a = i ∧ b = j then z τ a b else 0 : VC D N N') := by
    funext τ i j
    simp [Finset.sum_apply, ite_and]
  change z ∈ P
  rw [hz]
  exact P.sum_mem fun a _ => P.sum_mem fun b _ => hc a b _

theorem lam_mul (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ ((a : D.host.K) : D.host.E) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast [map_mul]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem of_dual_families (hG : admG1 D) (hC : Crv D cc δ)
    (S : Set (Matrix (Fin N') (Fin N) D.host.E))
    (hS : ∀ x ∈ S, ∀ y ∈ S, hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range)
    {r : ℕ} (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hy : ∀ i, y i ∈ S)
    (hy' : ∀ i, y' i ∈ S) (h : ∀ x, x = ∑ i, hYY D x (y' i) • y i) (A : AddSubgroup (VC D N N'))
    (hA : A = AddSubgroup.closure
      {z | ∃ w ∈ lamOf D cc δ, ∃ x ∈ S, z = w • embV D (tor0 D cc δ) x}) :
    (∀ F ∈ ThSp D (tor0 D cc δ) A, ∀ G ∈ ThSp D (tor0 D cc δ) A, G ≠ 0 → ∃ c : ℂ, F = c • G) ∧ (∀ x ∈ A, ∀ F, Wd D (tor0 D cc δ) x F = fun z => al D (tor0 D cc δ) x * U D (tor0 D cc δ) x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) ∧ (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) → x ∈ A) ∧ A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ ∀ x ∈ A, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  obtain ⟨L, hL, -⟩ := GlobalTheory.CurveAlgebraic.exists_periodPair D hG cc δ hC
  obtain ⟨hpos, hdual⟩ := GlobalTheory.T.latticeCovolume_pos_and_selfDual L _ hL
  have hLam : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  have hgen : ∀ w ∈ lamOf D cc δ, ∀ x ∈ S, w • embV D (tor0 D cc δ) x ∈ A := fun w hw x hx =>
    hA ▸ AddSubgroup.subset_closure ⟨w, hw, x, hx, rfl⟩
  have hsq : ∀ z ∈ A, ∀ x ∈ S, sq z (embV D (tor0 D cc δ) x) ∈ lamOf D cc δ := by
    intro z hz x hx
    rw [hA] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨w, hw, x', hx', rfl⟩ := hz
      obtain ⟨a, ha⟩ := hS x' hx' x hx
      rw [sq_smul_left, sq_embV cc δ hG, ← ha, mul_comm]
      exact lam_mul cc δ a hw
    | zero => rw [sq_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [sq_add_left]; exact add_mem ha hb
    | neg a _ ha => rw [sq_neg_left]; exact neg_mem ha
  have hint : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m := by
    intro z hz u hu
    rw [hA] at hu
    simp only [im_Hf, hLam]
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨w, hw, x, hx, rfl⟩ := hu
      rw [sq_smul_right]
      exact (hdual _).1 (hsq z hz x hx) w hw
    | zero => exact ⟨0, by simp [sq_zero_right]⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [sq_add_right, Complex.add_im, add_div, hm, hn, Int.cast_add]⟩
    | neg a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨-m, by rw [sq_neg_right, Complex.neg_im, neg_div, hm, Int.cast_neg]⟩
  have hexp := expand cc δ hG y y' h
  have hmem : ∀ z, (∀ i, sq z (embV D (tor0 D cc δ) (y' i)) ∈ lamOf D cc δ) → z ∈ A :=
    fun z hz => by
      rw [hexp z]
      exact sum_mem fun i _ => hgen _ (hz i) _ (hy i)
  have hsd : ∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) → x ∈ A := fun z hz =>
    hmem z fun i => (hdual _).2 fun w hw => by
      have := hz _ (hgen w hw _ (hy' i))
      rwa [im_Hf, hLam, sq_smul_right] at this
  have hq : ∀ x ∈ A, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
    intro x hx
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_integer_map_eq_halfOneAddSqrt D
    have hx' : w0 D • x ∈ A := hmem _ fun i => by
      rw [sq_smul_left, ← ha]
      exact lam_mul cc δ a (hsq x hx _ (hy' i))
    obtain ⟨m, hm⟩ := hint _ hx' x hx
    refine ⟨m, ?_⟩
    rw [← hm, im_Hf, sq_smul_left, qH, Hf_eq, Complex.div_ofReal_re, Complex.mul_im, sq_self_im]
    simp [w0]
    ring
  have hdisc : DiscreteTopology A := by
    haveI : DiscreteTopology L.lattice := inferInstance
    let f : A → Fin r → L.lattice := fun z i =>
      ⟨sq z.1 (embV D (tor0 D cc δ) (y' i)), (hL _).1 (hsq z.1 z.2 _ (hy' i))⟩
    have hf : Continuous f := continuous_pi fun i =>
      Continuous.subtype_mk ((continuous_sq _).comp continuous_subtype_val) _
    refine DiscreteTopology.of_continuous_injective hf fun z u hzu => Subtype.ext ?_
    rw [hexp z.1, hexp u.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show sq z.1 _ = sq u.1 _ from congrArg Subtype.val (congrFun hzu i)]
  have h1 : L.ω₁ ∈ lamOf D cc δ := (hL _).2 L.ω₁_mem_lattice
  have h2 : L.ω₂ ∈ lamOf D cc δ := (hL _).2 L.ω₂_mem_lattice
  refine ⟨GlobalTheory.T.thetaFunction_selfDual_exists_eq_smul D _ N N' A hpos hdisc fun x => ⟨hint x, hsd x⟩, fun x hx F => ?_, hint, hsd,
    ?_, ?_, hq⟩
  · obtain ⟨m, hm⟩ := hq x hx
    funext z
    have hm' : Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = m := hm
    rw [Wd, wdPh, hm, al, hm', round_intCast, ee, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 2
    push_cast
    ring
  · rw [AddSubgroup.fg_iff]
    refine ⟨Set.range (fun i => L.ω₁ • embV D (tor0 D cc δ) (y i)) ∪
      Set.range (fun i => L.ω₂ • embV D (tor0 D cc δ) (y i)), le_antisymm ?_ fun z hz => ?_,
      (Set.finite_range _).union (Set.finite_range _)⟩
    · rw [AddSubgroup.closure_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact hgen _ h1 _ (hy i)
      · exact hgen _ h2 _ (hy i)
    · rw [hexp z]
      refine sum_mem fun i _ => ?_
      obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 ((hL _).1 (hsq z hz _ (hy' i)))
      rw [← hmn, add_smul, mul_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      refine add_mem (zsmul_mem (AddSubgroup.subset_closure ?_) m)
        (zsmul_mem (AddSubgroup.subset_closure ?_) n)
      exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩]
  · rw [eq_top_iff]
    intro z _
    rw [hexp z]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← L.basis.sum_repr (sq z _), Fin.sum_univ_two, add_smul, smul_assoc, smul_assoc,
      L.basis_zero, L.basis_one]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (hgen _ h1 _ (hy i))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (hgen _ h2 _ (hy i))))

theorem hYY_smul (a : D.host.K) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (a • x) y = a * hYY D x y := by
  rw [hYY, hYY, ← smul_eq_mul, ← map_smul]
  simp [Finset.smul_sum]

theorem hYY_add (x x' y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (x + x') y = hYY D x y + hYY D x' y := by
  simp [hYY, add_mul, Finset.sum_add_distrib]

theorem onB_expand {r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b)
    (x : Matrix (Fin N') (Fin N) D.host.E) : x = ∑ i, hYY D x (b i) • b i := by
  have hx : x ∈ Submodule.span D.host.K (Set.range b) := hb.2 ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    simp [hb.1 j, ite_smul]
  | zero => simp [hYY]
  | add x x' _ _ hx hx' =>
    simp only [hYY_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hx']
  | smul a x _ hx =>
    simp only [hYY_smul, mul_smul, ← Finset.smul_sum]
    rw [← hx]

theorem theta_line : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → (∀ F ∈ ThSp D (tor0 D cc δ) A, ∀ G ∈ ThSp D (tor0 D cc δ) A, G ≠ 0 → ∃ c : ℂ, F = c • G) ∧ (∀ x ∈ A, ∀ F, Wd D (tor0 D cc δ) x F = fun z => al D (tor0 D cc δ) x * U D (tor0 D cc δ) x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) ∧ (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) → x ∈ A) ∧ A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ ∀ x ∈ A, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  intro D hG cc δ hC N N' A hA
  rcases hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩
  · refine of_dual_families cc δ hG hC (Set.range b) ?_ b b (fun i => ⟨i, rfl⟩)
      (fun i => ⟨i, rfl⟩) (onB_expand hb) _ ?_
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rw [hb.1 i j]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · unfold LaB
      congr 1
      ext z
      simp [tor0]
  · obtain ⟨r, y, y', hy, hy', h⟩ := GlobalTheory.T.exists_traceDual_family_homLattice D (GlobalTheory.T.exists_traceDual_family_inverseHalfDifferent D) N N' L L' hL hL'
    have hint := GlobalTheory.T.hermitian_pairing_integral_values D N N' L L' hL hL'
    have hA : La D (tor0 D cc δ) L L' = AddSubgroup.closure
        {z | ∃ w ∈ lamOf D cc δ, ∃ x ∈ {x | x ∈ YYl D L L'}, z = w • embV D (tor0 D cc δ) x} := rfl
    exact of_dual_families cc δ hG hC {x | x ∈ YYl D L L'} (fun x hx y hy => hint x hx y hy) y y'
      hy hy' h _ hA

end GlobalTheory.ConjNorm.Line
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ConjNorm.Inter

open GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

def sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (by intro a b c; simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum, mul_div_assoc])
    (by intro a b c; simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c), ← Finset.mul_sum,
        mul_div_assoc])

theorem isHerm_sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : IsHerm (sesqOf D T N N') := by
  intro x y
  change Hf D T y x = starRingEnd ℂ (Hf D T x y)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem lam_mul_mem (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem klat_gen {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    ∃ S : Set (Matrix (Fin N') (Fin N) D.host.E), Submodule.span D.host.K S = ⊤ ∧
      A = AddSubgroup.closure {z | ∃ w ∈ lamOf D cc δ, ∃ B ∈ S, z = w • embV D (tor0 D cc δ) B} := by
  rcases hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩
  · refine ⟨Set.range b, hb.2, ?_⟩
    unfold LaB
    congr 1
    ext z
    simp [tor0]
  · refine ⟨YYl D L L', ?_, rfl⟩
    obtain ⟨r, y, y', hy, -, h⟩ := GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
    rw [eq_top_iff]
    intro x _
    rw [h x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hy i))

theorem klat_smul_mem {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) (a : 𝓞 D.host.K)
    {x : VC D N N'} (hx : x ∈ A) : D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ A := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, lam_mul_mem a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem embV_smul (h : GL3Theta.InducedCMType D) (k : D.host.K) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (k • B) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) B := by
  funext τ i j
  change embT D τ ((k : D.host.E) * B i j) = D.host.φ₀ (k : D.host.E) * embT D τ (B i j)
  rw [map_mul, h τ k]

theorem embV_add (B B' : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (B + B') = embV D (tor0 D cc δ) B + embV D (tor0 D cc δ) B' := by
  funext τ i j
  exact map_add (embT D τ) _ _

theorem embV_zero : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  exact map_zero (embT D τ)

theorem klat_rat (h : GL3Theta.InducedCMType D) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A)
    {x : VC D N N'} (hx : x ∈ A) : ∃ B, x = δ • embV D (tor0 D cc δ) B := _root_.GlobalTheory.ThetaInter.klat_rat (A := A) (x := x) h hA hx

theorem klat_mul_mem (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A : AddSubgroup (VC D N N')}
    (hA : KLat D (tor0 D cc δ) A) (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ m • (δ • embV D (tor0 D cc δ) B) ∈ A := _root_.GlobalTheory.ThetaInter.klat_mul_mem (A := A) h hcc hA B

theorem klat_finite (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A₁ A₂ : AddSubgroup (VC D N N')}
    (h₁ : KLat D (tor0 D cc δ) A₁) (h₂ : KLat D (tor0 D cc δ) A₂) (hfg : A₂.FG) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) :=
  finite_quot hfg fun x hx => by
    obtain ⟨B, rfl⟩ := klat_rat h h₂ hx
    exact klat_mul_mem h hcc h₁ B

theorem klat_facts (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ IsSelfDual (sesqOf D (tor0 D cc δ) N N') A ∧
      IsSemiChar (sesqOf D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := GlobalTheory.ConjNorm.Line.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h3, h4, le_antisymm h2 h1, ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine isSemiChar_round (isHerm_sesqOf D _ N N') (Real.sqrt D.host.d) h1 (fun x hx => ?_) h5
  have := klat_smul_mem hA a hx
  rwa [ha] at this

end GlobalTheory.ConjNorm.Inter


open GlobalTheory.ThetaInter GlobalTheory.ConjNorm.Inter in
theorem GlobalTheory.ConjNorm.unitary_all : ∀ D : D7, IntertwinerUnitary D := by
  intro D cc δ hc N N' A₁ A₂ h₁ h₂ th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := Inter.klat_facts hc h₁
  obtain ⟨f₂, s₂, d₂, c₂⟩ := Inter.klat_facts hc h₂
  have hH := Inter.isHerm_sesqOf D (tor0 D cc δ) N N'
  have hψ := (GlobalTheory.InducedType.induced_type D).1.1
  have := Inter.klat_finite hψ hc.1.1 h₁ h₂ f₂
  have := Inter.klat_finite hψ hc.1.1 h₂ h₁ f₁
  have : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have t₂ := discrete_of_selfDual hH d₂ f₂
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (Inter.sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A₁ := hth.2
  exact ⟨fun x => mean_opU MeasureTheory.volume hH t₁ s₁ c₁ hth.1.continuous hF x,
    ⟨differentiable_inter (H := Inter.sesqOf D (tor0 D cc δ) N N') (α := al D (tor0 D cc δ)) A₁ A₂ hth.1,
      inter_mem_fixedBy hH c₁ d₂ c₂ hF⟩,
    mean_inter MeasureTheory.volume hH t₁ s₁ t₂ s₂ d₁ c₁ d₂ c₂ hth.1 hF,
    inter_inter hH d₁ d₂ c₁ hF⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalBasisGaloisMap
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalBasisGaloisMap
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem aut_conj_comm (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (x : D.host.E) :
    σ (D.host.conj x) = D.host.conj (σ x) := by
  have h : σ * D.host.conj = D.host.conj * σ :=
    (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg (fun f : D.host.E ≃ₐ[ℚ] D.host.E => f x) h

theorem hYY_map_aut (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : ∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E))
    {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (x.map σ) (y.map σ) = hYY D x y := by
  let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
  unfold hYY
  rw [← Algebra.trace_eq_of_algEquiv e (∑ i, ∑ j, x i j * D.host.conj (y i j))]
  congr 1
  show _ = σ _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Matrix.map_apply, aut_conj_comm]

theorem onB_map_aut : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) →
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D (fun j => (b j).map σ) := by
  intro D σ hσ N N' r b hb
  refine ⟨?_, ?_⟩
  · intro i j
    rw [hYY_map_aut D σ hσ]
    exact hb.1 i j
  · let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
    let L : Matrix (Fin N') (Fin N) D.host.E ≃ₗ[D.host.K] Matrix (Fin N') (Fin N) D.host.E :=
      e.toLinearEquiv.mapMatrix
    have h : (fun j => (b j).map σ) = L.toLinearMap ∘ b := rfl
    rw [h, Set.range_comp, ← Submodule.map_span, hb.2, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.NormSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalBasisGaloisMapStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalBasis_galois_map : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D (fun j => (b j).map σ) := by
  first | exact @GlobalTheory.NormSum.onB_map_aut | exact GlobalTheory.NormSum.onB_map_aut | (intros; apply GlobalTheory.NormSum.onB_map_aut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalProductThetaMemThetaSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalProductThetaMemThetaSpace
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OrthoProdTheta

variable {D : D7}

theorem coordB_add (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coordB_sum (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : ∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) (i : Fin r) (c : Fin r → ℂ) :
    coordB D T b i (∑ k, c k • embV D T (b k)) = c i := by
  let L : VC D N N' →ₗ[ℂ] ℂ :=
    { toFun := coordB D T b i
      map_add' := coordB_add T b i
      map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc] }
  have hL : ∀ z, coordB D T b i z = L z := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, map_sum]
  have h2 : ∀ k, L (c k • embV D T (b k)) = if i = k then c k else 0 := by
    intro k
    rw [map_smul, ← hL, hb]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun k _ => h2 k]
  simp

theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) :
    (-1 : ℂ) ^ (∑ k ∈ s, m k) = ∏ k ∈ s, (-1 : ℂ) ^ m k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

theorem exists_coord (T : Tor D) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} {x : VC D a d} (hx : x ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, w j ∈ T.abelian₂) ∧ x = ∑ j, w j • embV D T (b j) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, j, rfl⟩ := hx
    refine ⟨Pi.single j w, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hw
      · simp [h]
    · rw [Finset.sum_eq_single j] <;> simp +contextual
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    exact ⟨w + w', fun j => add_mem (hw j) (hw' j), by simp [add_smul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨-w, fun j => neg_mem (hw j), by simp⟩

theorem hf_sum (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (c : Fin r → ℂ)
    (z : VC D a d) :
    Hf D T z (∑ k, c k • embV D T (b k)) = (∑ k, coordB D T b k z * (starRingEnd ℂ) (c k)) / (area T.abelian₂ : ℂ) := by
  unfold Hf coordB
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, embV]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pullB_mem_ThSp : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  intro D T N N' r b hb g hg hq
  refine ⟨?_, ?_⟩
  · unfold pullB coordB
    fun_prop
  · intro x hx z
    obtain ⟨w, hw, rfl⟩ := exists_coord T hx
    choose m hm hU using fun k => hq _ (hw k)
    have hre : Real.sqrt D.host.d / 2 *
        (Hf D T (∑ k, w k • embV D T (b k)) (∑ k, w k • embV D T (b k))).re = ((∑ k, m k : ℤ) : ℝ) := by
      rw [hf_sum, Complex.div_ofReal_re, Complex.re_sum, Int.cast_sum, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coordB_sum T b hb, ← hm k, q1, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hal : al D T (∑ k, w k • embV D T (b k)) = ∏ k, (-1 : ℂ) ^ m k := by
      unfold al
      rw [hre, round_intCast, neg_one_zpow_sum]
    have hUU : U D T (∑ k, w k • embV D T (b k)) (pullB D T b g) z = ∏ k, U1 T.abelian₂ (w k) g (coordB D T b k z) := by
      unfold U U1 pullB
      rw [hf_sum, hf_sum, Finset.prod_mul_distrib, ← Complex.exp_sum]
      simp only [coordB_add, coordB_sum T b hb]
      congr 2
      rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hal, hUU, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => hU k _

end GlobalTheory.OrthoProdTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalProductThetaMemThetaSpaceStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalProductTheta_mem_thetaSpace : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  first | exact @GlobalTheory.OrthoProdTheta.pullB_mem_ThSp | exact GlobalTheory.OrthoProdTheta.pullB_mem_ThSp | (intros; apply GlobalTheory.OrthoProdTheta.pullB_mem_ThSp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ConjNorm

noncomputable def torTw (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Tor D :=
  ⟨fun τ x => embT D τ (σ x), lamOf D cc δ⟩

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf]

theorem norm_core (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E)
    (hσ : ∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hL : SD D L) (hL' : SD D L')
    (G : VC D N N' → ℂ) (hG : ThetaVectorUpToUnits D (torTw D σ cc δ) t0 L L' G) :
    G ∈ Th D (torTw D σ cc δ) L L' ∧ ∀ x, normSq D (torTw D σ cc δ) (La D (torTw D σ cc δ) L L')
      (U D (torTw D σ cc δ) x G) = nrm1Sq (lamOf D cc δ) (GL3Theta.th0 (lamOf D cc δ) t0) ^ (fF D * N * N') := by
  have g1 := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨b, κ, hb, ⟨hκQ, hκ⟩, rfl⟩ := hG
  have hκ1 : ‖κ‖ = 1 := hκ (algebraMap Qbar ℂ)
  obtain ⟨L₁, L₁', h₁, h₁', hY⟩ := GlobalTheory.T.exists_selfDual_pair_galoisConjugate_homLattice D σ hσ N N' L L' hL hL'
  have hb' := GlobalTheory.T.orthonormalBasis_galois_map D σ hσ N N' _ b hb
  have eLa : La D (torTw D σ cc δ) L L' = La D (tor0 D cc δ) L₁ L₁' := by
    unfold La
    congr 1
    ext z
    constructor
    · rintro ⟨w, hw, A, hA, rfl⟩
      exact ⟨w, hw, A.map σ, (hY A).1 hA, rfl⟩
    · rintro ⟨w, hw, A, hA, rfl⟩
      have e : (A.map σ.symm).map σ = A := by ext i j; simp
      refine ⟨w, hw, A.map σ.symm, (hY _).2 (by rw [e]; exact hA), ?_⟩
      congr 1
      funext τ i j
      simp [embV, tor0, torTw]
  obtain ⟨hd, hinv⟩ := GlobalTheory.T.halfPeriodTheta_differentiable_and_signedTranslate_invariant D g1 cc δ hc t0 ht
  obtain ⟨o1, o2⟩ := GlobalTheory.T.orthonormal_realBasis_complex_coordinates D g1 cc δ N N' _ _ hb'
  have hth := GlobalTheory.T.orthonormalProductTheta_mem_thetaSpace D (tor0 D cc δ) N N' _ _ o1 _ hd hinv
  have hn := GlobalTheory.T.meanSquare_orthoProductTheta_eq_prod D (tor0 D cc δ) N N' _ _ (GlobalTheory.T.idealPeriodLattice_of_curveDatum D g1 cc δ hc).1 o1 o2 _ hd.continuous (by
    intro ω hω z
    obtain ⟨m, -, hm⟩ := hinv ω hω
    have := congrArg norm (hm z)
    rwa [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul] at this)
  have kB : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) (fun j => (b j).map σ)) := Or.inl ⟨_, _, hb', rfl⟩
  have kL : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') := Or.inr ⟨_, _, h₁, h₁', rfl⟩
  obtain ⟨-, u2, u3, -⟩ := GlobalTheory.ConjNorm.unitary_all D cc δ hc N N' _ _ kB kL _ hth
  have u4 := (GlobalTheory.ConjNorm.unitary_all D cc δ hc N N' _ _ kL kL _ u2).1
  unfold Th
  rw [eLa]
  set F := Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) (fun j => (b j).map σ)) (La D (tor0 D cc δ) L₁ L₁')
    (pullB D (tor0 D cc δ) (fun j => (b j).map σ) (GL3Theta.th0 (lamOf D cc δ) t0)) with hF
  change (fun z => κ * F z) ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') ∧
    ∀ x, normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (U D (tor0 D cc δ) x (fun z => κ * F z)) = _
  refine ⟨⟨u2.1.const_mul κ, fun x hx z => ?_⟩, fun x => ?_⟩
  · have := u2.2 x hx z
    simp only [U] at this ⊢
    linear_combination κ * this
  · refine Eq.trans ?_ hn
    rw [← u3, ← u4 x]
    unfold normSq
    simp only [U, norm_mul, hκ1, one_mul]

theorem exists_aut (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hK : FixK D M ρ)
    (hM : ∀ τ x, embT D τ x ∈ M) :
    ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) ∧
      ∀ τ x, cj M ρ (embT D τ x) = embT D τ (σ x) := by
  obtain ⟨⟨hPsi, -⟩, hperm⟩ := GlobalTheory.T.inducedType_thetaGenusOne_permutes D
  obtain ⟨π, hπ⟩ := hperm M ρ hK hM
  rcases isEmpty_or_nonempty D.what₂.Tau with h | ⟨⟨τ₀⟩⟩
  · exact ⟨AlgEquiv.refl, fun _ => rfl, fun τ => h.elim τ⟩
  have hmul : ∀ g h : D.R.GG, D.host.sigmaOf (g * h) = D.host.sigmaOf g * D.host.sigmaOf h :=
    fun g h => map_mul _ g h
  have hone : D.host.sigmaOf 1 = 1 := map_one _
  have key : ∀ (τ : D.what₂.Tau) (g : D.R.GG) (x : D.host.E),
      embT D τ (D.host.sigmaOf g x) = D.host.φ₀ (D.host.sigmaOf ((D.eTau τ : D.R.GG) * g) x) := by
    intro τ g x
    rw [hmul]; rfl
  have key1 : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      embT D τ x = D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) x) := fun _ _ => rfl
  have main : ∀ τ x, cj M ρ (embT D τ x) = embT D τ (D.host.sigmaOf
      ((D.eTau τ₀ : D.R.GG)⁻¹ * (D.eTau (π τ₀) : D.R.GG)) x) := by
    intro τ x
    have e1 : embT D τ x = embT D τ₀ (D.host.sigmaOf
        ((D.eTau τ₀ : D.R.GG)⁻¹ * (D.eTau τ : D.R.GG)) x) := by
      rw [key, mul_inv_cancel_left, key1]
    rw [e1, hπ, key, key]
    congr 3
    rw [mul_left_comm, mul_comm (D.eTau (π τ₀) : D.R.GG), mul_left_comm]
  refine ⟨_, fun a => ?_, main⟩
  apply (embT D τ₀).injective
  rw [← main, hPsi, (hK a).2]

theorem exists_ext (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ (M' : IntermediateField ℚ ℂ) (ρ' : M' →ₐ[ℚ] ℂ), M ≤ M' ∧ Qbar ≤ M' ∧
      ∀ x ∈ M, ρ' (TaylorLogMetric.liftM M' x) = ρ (TaylorLogMetric.liftM M x) := by
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := ℚ) (L := M) (M := ℂ) (E := algebraicClosure M ℂ) ρ
  have hle : M ≤ (algebraicClosure M ℂ).restrictScalars ℚ := fun x hx =>
    (algebraicClosure M ℂ).algebraMap_mem ⟨x, hx⟩
  refine ⟨(algebraicClosure M ℂ).restrictScalars ℚ, φ, hle, fun x hx => ?_, fun x hx => ?_⟩
  · rw [IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]
    exact (mem_algebraicClosure_iff.1 hx).extendScalars (algebraMap ℚ M).injective
  · rw [← hφ]
    simp only [TaylorLogMetric.liftM, dif_pos hx, dif_pos (hle hx)]
    rfl

theorem norm_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hL : SD D L) (hL' : SD D L') (hN : Even (N * N'))
    (G : VC D N N' → ℂ) (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hK : FixK D M ρ) (hQ : Qbar ≤ M)
    (hD : DataIn D (tor0 D cc δ) M) (hC : CoefIn D G M)
    (t0' : ℂ) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0')
    (x : VC D N N') (hx : LaQ D (tor0 D cc δ) L L' x) (hCx : CoefIn D (U D (tor0 D cc δ) x G) M) :
    (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamConj M ρ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧
    ∃ x', fnConj D M ρ (U D (tor0 D cc δ) x G) = U D (torConj D (tor0 D cc δ) M ρ) x' (fnConj D M ρ G) ∧
      normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
          (U D (torConj D (tor0 D cc δ) M ρ) x' (fnConj D M ρ G)) =
        nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') := by
  have g1 := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨cc', δ', hc', -, hlam⟩ := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc M ρ hK hD.2.1 hD.2.2 1 one_pos
  obtain ⟨σ, hσ, hσ'⟩ := exists_aut D M ρ hK hD.1
  have hT : torConj D (tor0 D cc δ) M ρ = torTw D σ cc' δ' := by
    unfold torConj torTw
    congr 1
    funext τ y
    exact hσ' τ y
  have hGTh : G ∈ Th D (tor0 D cc δ) L L' :=
    (norm_core D AlgEquiv.refl (fun _ => rfl) cc δ hc t0 ht L L' hL hL' G hG).1
  have hE := (GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht N N' L L' hL hL' hN G hG M ρ hD hC).2.1 t0' ht'
  obtain ⟨m, hm, hmx⟩ := hx
  have htors := ((GlobalTheory.T.admJ_and_torsion_data_algebraic D g1).2 cc δ hc).2
  obtain ⟨x', hx', -⟩ := GlobalTheory.T.galois_data_exists D cc δ hc M ρ hK hD
    (fun t h1 h2 => ⟨hQ (htors t h1 h2).1, hQ (htors t h1 h2).2⟩) N N' L L' hL hL' x (2 * m) ⟨m, hm, hmx⟩ (by omega)
  have hcomb : comb D (tor0 D cc δ) (fun _ : Fin 1 => (1 : ℂ)) (fun _ => 0) G = G := by
    funext z; simp [comb, U_zero]
  have hg := GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints D cc δ hc M ρ hK hD N N' L L' hL hL' 1 (fun _ => 1) (fun _ => 0) G x x' m hGTh hm hmx
    (fun _ => by rw [smul_zero]; exact zero_mem _) hx'
  rw [hcomb] at hg
  refine ⟨hlam ▸ (GlobalTheory.T.idealPeriodLattice_of_curveDatum D g1 cc' δ' hc').1, x', (hg hC hCx).1, ?_⟩
  rw [hT] at hE ⊢
  rw [hlam] at ht' ⊢
  exact (norm_core D σ hσ cc' δ' hc' t0' ht' L L' hL hL' _ hE).2 x'

theorem norm_big (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hL : SD D L) (hL' : SD D L') (hN : Even (N * N'))
    (G : VC D N N' → ℂ) (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hQ : Qbar ≤ M)
    (hD : DataIn D (tor0 D cc δ) M) (hC : CoefIn D G M)
    (t0' : ℂ) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0')
    (x : VC D N N') (hx : LaQ D (tor0 D cc δ) L L' x) (hCx : CoefIn D (U D (tor0 D cc δ) x G) M) :
    normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
        (fnConj D M ρ (U D (tor0 D cc δ) x G)) =
      nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') := by
  rcases (GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc M ρ hD).1 with hK | hK
  · obtain ⟨-, x', e1, e2⟩ := norm_fix D cc δ hc t0 ht L L' hL hL' hN G hG M ρ hK hQ hD hC t0' ht' x hx hCx
    rw [e1, e2]
  · obtain ⟨-, hT, hb⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc M (rhoBar M ρ) hD
    have hbb : rhoBar M (rhoBar M ρ) = ρ := by
      ext y; simp [rhoBar]
    rw [hbb] at hT hb
    have hl : lamConj M ρ (lamOf D cc δ) =
        (lamConj M (rhoBar M ρ) (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    have hmem : ∀ z, z ∈ lamConj M ρ (lamOf D cc δ) ↔
        (starRingEnd ℂ) z ∈ lamConj M (rhoBar M ρ) (lamOf D cc δ) := by
      intro z
      rw [hl, AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨_, h, by simp⟩
    have ht'' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M (rhoBar M ρ) (lamOf D cc δ)) ((starRingEnd ℂ) t0') := by
      obtain ⟨a1, a2, a3⟩ := ht'
      rw [hmem] at a1 a2 a3
      refine ⟨by simpa [map_ofNat] using a1, ?_, ?_⟩
      · simpa [map_ofNat] using a3
      · simpa [map_ofNat, sub_eq_add_neg] using a2
    obtain ⟨hlat, x', e1, e2⟩ :=
      norm_fix D cc δ hc t0 ht L L' hL hL' hN G hG M (rhoBar M ρ) hK hQ hD hC _ ht'' x hx hCx
    have hTh := (GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht N N' L L' hL hL' hN G hG M (rhoBar M ρ) hD hC).1
    have e3 := ((hb N N' L L' (fnConj D M (rhoBar M ρ) G)).2.2 hTh).2 hL hL' x'
    have e4 := GlobalTheory.T.meanSquare_evenTheta_conjugateLattice _ hlat ((starRingEnd ℂ) t0')
    rw [Complex.conj_conj, ← hl] at e4
    rw [(hb N N' L L' (U D (tor0 D cc δ) x G)).1, e1, hT, e3, e2, e4]

theorem useNorm_all : ∀ D : D7, useNorm D := by
  intro D cc δ hc t0 ht N N' L L' hL hL' hN G hG M ρ hD hC t0' ht'
  obtain ⟨M', ρ', hle, hQ, he⟩ := exists_ext M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [he (g2 (lamOf D cc δ)) hD.2.1, he (g3 (lamOf D cc δ)) hD.2.2]
  have hT : torConj D (tor0 D cc δ) M ρ = torConj D (tor0 D cc δ) M' ρ' := by
    unfold torConj
    congr 1
    funext τ y
    exact (he _ (hD.1 τ y)).symm
  have hf : ∀ F : VC D N N' → ℂ, CoefIn D F M → fnConj D M ρ F = fnConj D M' ρ' F := by
    intro F hF
    funext z
    unfold fnConj
    exact tsum_congr fun α => by rw [he _ (hF α)]
  have hD' : DataIn D (tor0 D cc δ) M' := ⟨fun τ y => hle (hD.1 τ y), hle hD.2.1, hle hD.2.2⟩
  have main : ∀ x, LaQ D (tor0 D cc δ) L L' x → CoefIn D (U D (tor0 D cc δ) x G) M →
      normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
          (fnConj D M ρ (U D (tor0 D cc δ) x G)) =
        nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') := by
    intro x hx hCx
    rw [hf _ hCx, hT, hl]
    exact norm_big D cc δ hc t0 ht L L' hL hL' hN G hG M' ρ' hQ hD' (fun α => hle (hC α)) t0' (hl ▸ ht') x hx
      (fun α => hle (hCx α))
  refine ⟨?_, main⟩
  have := main 0 ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩ (by rw [U_zero]; exact hC)
  rwa [U_zero] at this

end GlobalTheory.ConjNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddingsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings : ∀ D : D7, useNorm D := by
  first | exact @GlobalTheory.ConjNorm.useNorm_all | exact GlobalTheory.ConjNorm.useNorm_all | (intros; apply GlobalTheory.ConjNorm.useNorm_all <;> assumption)
end

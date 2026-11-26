module

public import Mathlib

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TorsionTotientBound
noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

theorem le_mul_totient_sq (n : ℕ) : n ≤ (if Even n then 2 else 1) * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.totient_prime_pow hp hk]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · have he : Even (2 ^ (m + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      rw [if_pos he]
      have h1 : 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.le_mul_of_pos_right _ (by positivity)
      rw [pow_succ]
      nlinarith
    · have hne : ¬ Even (p ^ (m + 1)) := by
        rw [Nat.not_even_iff_odd]
        exact hodd.pow
      rw [if_neg hne, one_mul]
      have h3 : 3 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨j, hj⟩
        omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hP : 1 ≤ (q + 1) ^ m := Nat.one_le_pow _ _ (by omega)
      have hq : q + 1 ≤ q ^ 2 := by nlinarith
      calc (q + 1) ^ (m + 1) = (q + 1) ^ m * (q + 1) := pow_succ _ _
        _ ≤ (q + 1) ^ m * q ^ 2 := Nat.mul_le_mul_left _ hq
        _ ≤ ((q + 1) ^ m) ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
        _ = ((q + 1) ^ m * q) ^ 2 := by ring
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, mul_pow]
    have hce : (if Even (a * b) then 2 else 1) =
        (if Even a then 2 else 1) * (if Even b then 2 else 1) := by
      by_cases ea : Even a <;> by_cases eb : Even b <;> simp [ea, eb, Nat.even_mul]
      have h2 : 2 ∣ Nat.gcd a b := Nat.dvd_gcd (even_iff_two_dvd.mp ea) (even_iff_two_dvd.mp eb)
      rw [hab.gcd_eq_one] at h2
      norm_num at h2
    calc a * b ≤ ((if Even a then 2 else 1) * a.totient ^ 2) *
          ((if Even b then 2 else 1) * b.totient ^ 2) := Nat.mul_le_mul iha ihb
      _ = _ := by rw [hce]; ring

theorem le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  have := le_mul_totient_sq n
  split_ifs at this <;> nlinarith [Nat.zero_le (n.totient ^ 2)]

theorem torsionOrder_le (E : Type) [Field E] [NumberField E] :
    Units.torsionOrder E ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion E)
  have hord : orderOf g = Units.torsionOrder E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    rfl
  have hpos : 0 < Units.torsionOrder E := hord ▸ orderOf_pos g
  let f : NumberField.Units.torsion E →* E :=
    ((algebraMap (𝓞 E) E : 𝓞 E →+* E) : 𝓞 E →* E).comp
      ((Units.coeHom (𝓞 E)).comp (NumberField.Units.torsion E).subtype)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    exact (FaithfulSMul.algebraMap_injective (𝓞 E) E) hxy
  have hζ : IsPrimitiveRoot (f g) (Units.torsionOrder E) :=
    hord ▸ (IsPrimitiveRoot.orderOf g).map_of_injective hf
  have hdeg : (Units.torsionOrder E).totient ≤ Module.finrank ℚ E := by
    rw [← Polynomial.natDegree_cyclotomic (Units.torsionOrder E) ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζ hpos]
    exact minpoly.natDegree_le _
  calc Units.torsionOrder E ≤ 2 * (Units.torsionOrder E).totient ^ 2 := le_two_totient_sq _
    _ ≤ 2 * (Module.finrank ℚ E) ^ 2 := by gcongr

end Formalism.L2.SG.NGCut.TorsionTotientBound
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ShearMp
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

private theorem measurePreserving_pi_shear_of_indep {P : Type} [Fintype P]
    {α : P → Type} [∀ p, AddGroup (α p)] [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
    (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
    (S : P → Prop) [DecidablePred S] (d : ∀ p, (∀ q, α q) → α p) (hd : ∀ p, Measurable (d p))
    (hind : ∀ p, S p → ∀ x x' : ∀ q, α q, (∀ q, ¬ S q → x q = x' q) → d p x = d p x') :
    MeasurePreserving (fun g q => if S q then g q + d q g else g q)
      (Measure.pi μ) (Measure.pi μ) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd μ (fun q => ¬ S q)
  set e := MeasurableEquiv.piEquivPiSubtypeProd α (fun q => ¬ S q) with he
  have hfwd : ∀ g : ∀ q, α q, e g = (fun i : {q // ¬ S q} => g i.1, fun i : {q // ¬ ¬ S q} => g i.1) :=
    fun _ => rfl
  have hsymm : ∀ (x : ∀ i : {q // ¬ S q}, α i) (y : ∀ i : {q // ¬ ¬ S q}, α i) (q : P),
      e.symm (x, y) q = if h : ¬ S q then x ⟨q, h⟩ else y ⟨q, h⟩ := fun _ _ _ => rfl
  let v : (∀ i : {q // ¬ S q}, α i) → ∀ i : {q // ¬ ¬ S q}, α i :=
    fun x i => d i.1 (e.symm (x, 0))
  have hvdef : ∀ x i, v x i = d i.1 (e.symm (x, 0)) := fun _ _ => rfl
  have hv : Measurable v := by
    refine Measurable.of_eval (fun i => ?_)
    exact (hd i.1).comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hgm : Measurable (Function.uncurry fun (x : ∀ i : {q // ¬ S q}, α i)
      (y : ∀ i : {q // ¬ ¬ S q}, α i) => fun i => y i + v x i) := by
    refine Measurable.of_eval (fun i => ?_)
    exact Measurable.add ((measurable_pi_apply i).comp measurable_snd)
      ((measurable_pi_apply i).comp (hv.comp measurable_fst))
  have hgae : ∀ᵐ x ∂(Measure.pi fun i : {q // ¬ S q} => μ i),
      Measure.map (fun y : ∀ i : {q // ¬ ¬ S q}, α i => fun i => y i + v x i)
        (Measure.pi fun i : {q // ¬ ¬ S q} => μ i) = Measure.pi fun i : {q // ¬ ¬ S q} => μ i :=
    ae_of_all _ fun x =>
      (measurePreserving_pi (hf := fun i => measurePreserving_add_right (μ i.1) (v x i))).map_eq
  have h2 := MeasurePreserving.skew_product (MeasurePreserving.id _) hgm hgae
  have h3 := MeasurePreserving.symm _ h1
  have key : (fun g q => if S q then g q + d q g else g q) =
      (⇑e.symm ∘ (fun z : (∀ i : {q // ¬ S q}, α i) × (∀ i : {q // ¬ ¬ S q}, α i) =>
        (id z.1, fun i => z.2 i + v z.1 i))) ∘ ⇑e := by
    funext g q
    by_cases hq : S q
    · have hd' : d q (e.symm ((fun i : {q // ¬ S q} => g i.1), 0)) = d q g :=
        hind q hq _ _ (fun q' hq' => by simp [hsymm, hq'])
      simp [hfwd, hsymm, hq, hvdef, hd']
    · simp [hfwd, hsymm, hq]
  rw [key]
  exact (h3.comp h2).comp h1

theorem shear_mp : ∀ (n : ℕ) (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = n →
    ∀ (α : P → Type) [∀ p, AddGroup (α p)] [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
      (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
      (h : P → ℕ) (c : ∀ p, (∀ q, α q) → α p), (∀ p, Measurable (c p)) →
      (∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → c p x = c p x') →
      MeasurePreserving (fun g p => g p + c p g) (Measure.pi μ) (Measure.pi μ) := by
  intro n P _ _ _ α _ _ _ μ _ _ h c hc hdep
  have hstep : ∀ k : ℕ, MeasurePreserving (fun (g : ∀ q, α q) p => if h p < k then g p + c p g else g p)
      (Measure.pi μ) (Measure.pi μ) := by
    intro k
    induction k with
    | zero =>
      have h0 : (fun (g : ∀ q, α q) p => if h p < 0 then g p + c p g else g p) = id := by
        funext g p
        simp
      rw [h0]
      exact MeasurePreserving.id _
    | succ k ih =>
      have hL := measurePreserving_pi_shear_of_indep μ (fun q => h q = k) c hc
        (fun p hp x x' hx => hdep p x x' (fun q hq => hx q (by omega)))
      have heq : (fun (g : ∀ q, α q) p => if h p < k + 1 then g p + c p g else g p) =
          (fun (g : ∀ q, α q) p => if h p < k then g p + c p g else g p) ∘
            (fun (g : ∀ q, α q) q => if h q = k then g q + c q g else g q) := by
        funext g p
        simp only [Function.comp_apply]
        rcases lt_trichotomy (h p) k with hp | hp | hp
        · have hc' : c p (fun q => if h q = k then g q + c q g else g q) = c p g :=
            hdep p _ _ (fun q hq => by simp [show h q ≠ k by omega])
          simp [hp, show h p < k + 1 by omega, show h p ≠ k by omega, hc']
        · simp [hp]
        · simp [show ¬ h p < k + 1 by omega, show ¬ h p < k by omega, show h p ≠ k by omega]
      rw [heq]
      exact ih.comp hL
  have hfull : (fun (g : ∀ q, α q) p => g p + c p g) =
      (fun (g : ∀ q, α q) p => if h p < Finset.univ.sup h + 1 then g p + c p g else g p) := by
    funext g p
    have hle : h p ≤ Finset.univ.sup h := Finset.le_sup (Finset.mem_univ p)
    simp [show h p < Finset.univ.sup h + 1 by omega]
  rw [hfull]
  exact hstep _

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerMassQuotient
noncomputable section

open scoped ENNReal Classical

namespace Formalism.L2.SG.Pf.StabilizerMassQuotient

variable (Γ : Type*) [Group Γ]

variable {Γ}

theorem card_stab_smul {A : Type*} [MulAction Γ A] (g : Γ) (a : A) :
    Nat.card (MulAction.stabilizer Γ (g • a)) = Nat.card (MulAction.stabilizer Γ a) := by
  refine Nat.card_congr
    { toFun := fun s => ⟨g⁻¹ * (s : Γ) * g, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 s.2,
          inv_smul_smul]⟩
      invFun := fun t => ⟨g * (t : Γ) * g⁻¹, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul,
          MulAction.mem_stabilizer_iff.1 t.2]⟩
      left_inv := fun s => Subtype.ext (by first | simp [mul_assoc] | group)
      right_inv := fun t => Subtype.ext (by first | simp [mul_assoc] | group) }

theorem card_stab_of_orbitRel {A : Type*} [MulAction Γ A] {a a' : A} (h : MulAction.orbitRel Γ A a' a) :
    Nat.card (MulAction.stabilizer Γ a') = Nat.card (MulAction.stabilizer Γ a) := by
  obtain ⟨g, rfl⟩ := h; exact card_stab_smul g a

section Fibre

variable {A B : Type*} [MulAction Γ A] [MulAction Γ B] (f : A → B)
  (hf : ∀ (g : Γ) (a : A), f (g • a) = g • f a)


include hf in
@[reducible] def fibAct (b : B) : MulAction (MulAction.stabilizer Γ b) {a : A // f a = b} where
  smul s a := ⟨(s : Γ) • a.1, by rw [hf, a.2]; exact s.2⟩
  one_smul a := Subtype.ext (one_smul Γ a.1)
  mul_smul s t a := Subtype.ext (mul_smul (s : Γ) (t : Γ) a.1)


include hf in
def qmap : Quotient (MulAction.orbitRel Γ A) → Quotient (MulAction.orbitRel Γ B) :=
  Quotient.map' f fun a a' ⟨g, hg⟩ => ⟨g, by
    have hg' : g • a' = a := hg
    show g • f a' = f a
    rw [← hf, hg']⟩

theorem qmap_mk (a : A) : qmap f hf (Quotient.mk _ a) = Quotient.mk (MulAction.orbitRel Γ B) (f a) := rfl


include hf in
def stabEquiv (b : B) (x : {a : A // f a = b}) :
    (letI := fibAct f hf b; MulAction.stabilizer (MulAction.stabilizer Γ b) x) ≃ MulAction.stabilizer Γ x.1 := by
  letI := fibAct f hf b
  exact
    { toFun := fun s => ⟨(s.1 : Γ), by
        have h := s.2
        rw [MulAction.mem_stabilizer_iff] at h ⊢
        exact congrArg Subtype.val h⟩
      invFun := fun g => ⟨⟨g.1, by
        rw [MulAction.mem_stabilizer_iff]
        have h := MulAction.mem_stabilizer_iff.1 g.2
        have h2 := congrArg f h
        rw [hf, x.2] at h2
        exact h2⟩, by
          rw [MulAction.mem_stabilizer_iff]
          apply Subtype.ext
          exact (MulAction.mem_stabilizer_iff.1 g.2)⟩
      left_inv := fun s => rfl
      right_inv := fun g => rfl }


include hf in
def orbEquiv (oB : Quotient (MulAction.orbitRel Γ B)) :
    (letI := fibAct f hf oB.out; Quotient (MulAction.orbitRel (MulAction.stabilizer Γ oB.out) {a : A // f a = oB.out})) ≃
      ↥(qmap f hf ⁻¹' {oB}) := by
  letI := fibAct f hf oB.out
  refine Equiv.ofBijective (Quotient.lift (fun x => ⟨Quotient.mk _ x.1, ?_⟩) ?_) ⟨?_, ?_⟩
  · show Quotient.mk _ (f x.1) = oB
    rw [x.2]; exact Quotient.out_eq oB
  · rintro x y ⟨s, hs⟩
    apply Subtype.ext
    exact Quotient.sound ⟨(s : Γ), congrArg Subtype.val hs⟩
  · intro X Y hXY
    induction X using Quotient.inductionOn with | h x => ?_
    induction Y using Quotient.inductionOn with | h y => ?_
    have h := congrArg Subtype.val hXY
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hg' : g • y.1 = x.1 := hg
    have hgb : g • oB.out = oB.out := by
      have h2 := congrArg f hg'
      rw [hf, y.2, x.2] at h2
      exact h2
    exact Quotient.sound ⟨⟨g, hgb⟩, Subtype.ext hg'⟩
  · rintro ⟨oA, hoA⟩
    have hoA' : qmap f hf oA = oB := hoA
    have h1 : Quotient.mk (MulAction.orbitRel Γ B) (f oA.out) = Quotient.mk _ oB.out := by
      rw [← qmap_mk f hf, Quotient.out_eq, hoA', Quotient.out_eq]
    obtain ⟨g, hg⟩ := Quotient.exact h1
    have hg' : g • oB.out = f oA.out := hg
    refine ⟨Quotient.mk _ ⟨g⁻¹ • oA.out, by rw [hf, ← hg', inv_smul_smul]⟩, ?_⟩
    apply Subtype.ext
    show Quotient.mk _ (g⁻¹ • oA.out) = oA
    exact (Quotient.sound ⟨g⁻¹, rfl⟩ : Quotient.mk (MulAction.orbitRel Γ A) (g⁻¹ • oA.out) =
      Quotient.mk _ oA.out).trans (Quotient.out_eq oA)

end Fibre

section Sub

variable {Y : Type*} [MulAction Γ Y]

end Sub

section Pair

variable {Y : Type*} [MulAction Γ Y]

end Pair

section Local

variable {T : Type*} [MulAction Γ T]

end Local

end Formalism.L2.SG.Pf.StabilizerMassQuotient
end
end

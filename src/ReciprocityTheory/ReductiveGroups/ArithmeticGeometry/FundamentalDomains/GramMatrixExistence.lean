module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsUnitaryBasisSameFlag

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpComponentCombination
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpLatticeTransfer
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpBasisExistence
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalComplementLines
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma hermC_sub_left_of_ringHom (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma ppos_sub (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u - v) = X.ppos x τ u - X.ppos x τ v := by
  simp only [Data.ppos, hermC_sub_left_of_ringHom, sub_mul, Finset.sum_sub_distrib, sub_smul]

variable {X : Data E r}

end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines
end

namespace ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma herm_add_right' (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, Pi.add_apply, HermitianPairingAlgebra.cc_add, mul_add, Finset.sum_add_distrib]

lemma herm_sum_left' (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (y : Fin r → E) : herm G (∑ i ∈ s, f i) y = ∑ i ∈ s, herm G (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianPairingAlgebra.herm_add_left, ih]

lemma herm_sum_right' (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (x : Fin r → E) : herm G x (∑ i ∈ s, f i) = ∑ i ∈ s, herm G x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm, cc]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right', ih]

def hxi (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : (Fin r → E) →ₗ[E] E where
  toFun x := herm G x ξ
  map_add' x y := HermitianTraceFormVanishing.herm_add_left G x y ξ
  map_smul' a x := HermitianTraceFormVanishing.herm_smul_left G a x ξ

theorem exists_beta (X : Data E r) {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0) :
    ∃ β : Fin (r - 2) → Fin r → E, (∀ k, herm X.Gm (β k) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ x : Fin r → E, herm X.Gm x ξ = 0 →
        ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) := by
  classical
  set f := hxi X.Gm ξ with hf
  have hfx : ∀ x, f x = herm X.Gm x ξ := fun _ => rfl

  have hw : (fun b => cc (ξ b)) ≠ 0 := by
    intro h
    apply hξ0
    funext b
    have hb := congrFun h b
    simp only [Pi.zero_apply, cc] at hb
    simpa using hb
  obtain ⟨a, ha⟩ : ∃ a, (X.Gm *ᵥ fun b => cc (ξ b)) a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det (funext h))
  have hfa : f (Pi.single a 1) ≠ 0 := by
    rw [hfx]
    convert ha using 1
    simp [herm, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsurj : Function.Surjective f := fun y =>
    ⟨(y / f (Pi.single a 1)) • Pi.single a 1, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfa]⟩
  set K := LinearMap.ker f with hK
  have hξK : ξ ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hξξ
  have hrange : Module.finrank E (LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hKr : Module.finrank E K = r - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, Module.finrank_fin_fun] at this
    have h2 : 1 + Module.finrank E K = r := this
    omega
  have hKpos : 0 < Module.finrank E K := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    apply hξ0
    have : ξ ∈ (⊥ : Submodule E (Fin r → E)) := h ▸ hξK
    simpa using this
  have hr2 : 2 ≤ r := by omega
  set ξK : K := ⟨ξ, hξK⟩ with hξKdef
  have hξK0 : ξK ≠ 0 := fun h => hξ0 (congrArg Subtype.val h)
  set S : Submodule E K := E ∙ ξK with hS
  have hQ : Module.finrank E (K ⧸ S) = r - 2 := by
    have h0 := Submodule.finrank_quotient_add_finrank S
    have h1 : Module.finrank E S = 1 := by rw [hS]; exact finrank_span_singleton hξK0
    rw [h1, hKr] at h0
    have h2 : Module.finrank E (K ⧸ S) + 1 = r - 1 := h0
    omega
  let bQ := Module.finBasisOfFinrankEq E (K ⧸ S) hQ
  let βK : Fin (r - 2) → K := fun k => (Submodule.Quotient.mk_surjective S (bQ k)).choose
  have hβK : ∀ k, Submodule.Quotient.mk (p := S) (βK k) = bQ k := fun k =>
    (Submodule.Quotient.mk_surjective S (bQ k)).choose_spec
  have hdecK : ∀ y : K, ∃ (c : Fin (r - 2) → E) (e : E), y = ∑ k, c k • βK k + e • ξK := by
    intro y
    set c := bQ.repr (Submodule.Quotient.mk y) with hc
    refine ⟨c, ?_⟩
    have hmk : Submodule.Quotient.mk (p := S) (∑ k, c k • βK k) = ∑ k, c k • bQ k := by
      have h := map_sum S.mkQ (fun k => c k • βK k) Finset.univ
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hβK] at h
      exact h
    have hq : Submodule.Quotient.mk (p := S) y = Submodule.Quotient.mk (∑ k, c k • βK k) := by
      rw [hmk, hc, bQ.sum_repr]
    rw [Submodule.Quotient.eq] at hq
    have hq' : y - ∑ k, c k • βK k ∈ E ∙ ξK := hq
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hq'
    exact ⟨e, by rw [he]; abel⟩
  refine ⟨fun k => (βK k : Fin r → E), fun k => (βK k).2, ?_, ?_⟩
  · have hspan : ⊤ ≤ Submodule.span E (Set.range (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) := by
      intro y _
      obtain ⟨c, e, rfl⟩ := hdecK y
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)
      · exact Submodule.subset_span ⟨k.succ, by simp⟩
      · exact Submodule.subset_span ⟨0, by simp⟩
    have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan
      (by rw [Fintype.card_fin, hKr]; omega)
    have hmap := hli.map' K.subtype (Submodule.ker_subtype K)
    have heq : (K.subtype ∘ (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) =
        (Fin.cons ξ (fun k => (βK k : Fin r → E)) : Fin (r - 2 + 1) → Fin r → E) := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp [ξK]
    exact heq ▸ hmap
  · intro x hx
    have hxK : x ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hx
    obtain ⟨c, e, he⟩ := hdecK ⟨x, hxK⟩
    refine ⟨c, e, ?_⟩
    have := congrArg Subtype.val he
    simpa [ξK] using this

variable (X : DataX E r)

def LBsub {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {c | ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L'}
  add_mem' := by
    rintro c c' ⟨e, he⟩ ⟨e', he'⟩
    refine ⟨e + e', ?_⟩
    have h : ∑ k, (c + c') k • β k + (e + e') • ξ =
        (∑ k, c k • β k + e • ξ) + (∑ k, c' k • β k + e' • ξ) := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      abel
    rw [h]
    exact X.L'.add_mem he he'
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a c ⟨e, he⟩
    refine ⟨(a : E) * e, ?_⟩
    have h : ∑ k, (a • c) k • β k + ((a : E) * e) • ξ = a • (∑ k, c k • β k + e • ξ) := by
      rw [integer_smul_eq_coe_smul a c, integer_smul_eq_coe_smul a (∑ k, c k • β k + e • ξ)]
      simp only [Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, mul_smul]
    rw [h]
    exact X.L'.smul_mem a he

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
end

namespace ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)

lemma span_L' : Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro x hx
  have h1 : (X.NA : E) • x ∈ Submodule.span E (X.L' : Set (Fin r → E)) :=
    Submodule.subset_span (X.NA_sub x hx)
  have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
  have h2 := Submodule.smul_mem _ ((X.NA : E)⁻¹) h1
  rwa [smul_smul, inv_mul_cancel₀ hNA, one_smul] at h2

variable {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E)

lemma smul_O_E (a : 𝓞 E) (x : E) : a • x = (a : E) * x := by
  rw [Algebra.smul_def]

def Tmap : ((Fin n → E) × E) →ₗ[𝓞 E] (Fin r → E) where
  toFun p := ∑ k, p.1 k • β k + p.2 • ξ
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' a p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    rw [integer_smul_eq_coe_smul a p.1, integer_smul_eq_coe_smul a (∑ k, p.1 k • β k + p.2 • ξ), smul_O_E]
    simp only [Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, mul_smul]

lemma LB_eq : LBsub X β ξ = (X.L'.comap (Tmap β ξ)).map (LinearMap.fst (𝓞 E) (Fin n → E) E) := by
  ext c
  change (∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L') ↔
    c ∈ (X.L'.comap (Tmap β ξ)).map (LinearMap.fst (𝓞 E) (Fin n → E) E)
  simp only [Submodule.mem_map, Submodule.mem_comap, LinearMap.fst_apply, Prod.exists]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨c, e, he, rfl⟩
  · rintro ⟨c', e, hp, rfl⟩
    exact ⟨e, hp⟩

lemma Tmap_inj (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E)) :
    Function.Injective (Tmap β ξ) := by
  intro p q hpq
  have e1 : ∑ k, p.1 k • β k + p.2 • ξ = ∑ k, q.1 k • β k + q.2 • ξ := hpq
  rw [← sub_eq_zero] at e1
  have h := Fintype.linearIndependent_iff.mp hli
    (Fin.cons (p.2 - q.2) (p.1 - q.1) : Fin (n + 1) → E) (by
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.sub_apply, sub_smul,
        Finset.sum_sub_distrib]
      rw [← e1]
      abel)
  refine Prod.ext (funext fun k => ?_) ?_
  · have h' := h k.succ
    simp only [Fin.cons_succ, Pi.sub_apply] at h'
    exact sub_eq_zero.mp h'
  · have h' := h 0
    simp only [Fin.cons_zero] at h'
    exact sub_eq_zero.mp h'

lemma LB_lattice (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E)) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (LBsub X β ξ) := by
  refine ⟨?_, ?_⟩
  · rw [LB_eq]
    apply Submodule.FG.map
    apply Submodule.fg_of_fg_map_injective (Tmap β ξ) (Tmap_inj β ξ hli)
    rw [Submodule.map_comap_eq]
    have : IsNoetherian (𝓞 E) X.L' := isNoetherian_of_fg_of_noetherian _ X.L'_fg
    have h1 := IsNoetherian.noetherian ((LinearMap.range (Tmap β ξ) ⊓ X.L').comap X.L'.subtype)
    have h2 := h1.map X.L'.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr inf_le_right] at h2
  · rw [Submodule.eq_top_iff']
    intro c
    have hc : (∑ k, c k • β k) ∈ Submodule.span E (X.L' : Set (Fin r → E)) := by
      rw [span_L' X]
      simp
    have hdenom (v : Fin r → E) (hv : v ∈ Submodule.span E (X.L' : Set (Fin r → E))) :
        ∃ a : 𝓞 E, a ≠ 0 ∧ (a : E) • v ∈ X.L' := by
      refine Submodule.span_induction (p := fun v _ => ∃ a : 𝓞 E, a ≠ 0 ∧ (a : E) • v ∈ X.L')
        (fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩)
        ⟨1, one_ne_zero, by simp⟩
        ?_ ?_ hv
      · intro x y hx hy ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
        refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
        change ((a : E) * (b : E)) • (x + y) ∈ X.L'
        rw [smul_add]
        have hleft : (b : 𝓞 E) • ((a : E) • x) ∈ X.L' := X.L'.smul_mem b hax
        have hright : (a : 𝓞 E) • ((b : E) • y) ∈ X.L' := X.L'.smul_mem a hby
        have hleft' : ((a : E) * (b : E)) • x ∈ X.L' := by
          convert hleft using 1 <;> ext i <;> simp [smul_eq_mul, Algebra.smul_def] <;> ring
        have hright' : ((a : E) * (b : E)) • y ∈ X.L' := by
          convert hright using 1 <;> ext i <;> simp [smul_eq_mul, Algebra.smul_def] <;> ring
        exact X.L'.add_mem hleft' hright'
      · intro c x hx ⟨a, ha, hax⟩
        have hdiv : ∃ u v : 𝓞 E, v ∈ nonZeroDivisors (𝓞 E) ∧
            (algebraMap (𝓞 E) E u) / algebraMap (𝓞 E) E v = c :=
          IsFractionRing.div_surjective (A := 𝓞 E) (z := c)
        obtain ⟨u, v, hv, hcv⟩ := hdiv
        have hvO : v ≠ 0 := nonZeroDivisors.ne_zero hv
        refine ⟨a * v, mul_ne_zero ha hvO, ?_⟩
        have hvE : (v : E) ≠ 0 := by
          intro h
          exact hvO ((IsFractionRing.injective (𝓞 E) E) h)
        have hmul : ((a * v : 𝓞 E) : E) * c = (u * a : 𝓞 E) := by
          change (a : E) * (v : E) * c = (u : E) * (a : E)
          calc
            (a : E) * (v : E) * c = (a : E) * (v : E) * ((u : E) / (v : E)) := by rw [hcv]
            _ = (u : E) * (a : E) := by field_simp [hvE] <;> ring
        rw [smul_smul]
        change (((a * v : 𝓞 E) : E) * c) • x ∈ X.L'
        rw [hmul]
        change ((u : E) * (a : E)) • x ∈ X.L'
        convert X.L'.smul_mem u hax using 1 <;> ext i <;>
          simp [smul_eq_mul, Algebra.smul_def] <;> ring
    obtain ⟨a, ha, hmem⟩ := hdenom _ hc
    have hcoef : a • c ∈ LBsub X β ξ := by
      refine ⟨0, ?_⟩
      have hsmul : (∑ k, (a • c) k • β k) + (0 : E) • ξ = a • (∑ k, c k • β k) := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
        simp
      rw [hsmul]
      exact hmem
    have haE : (a : E) ≠ 0 := by
      intro h
      exact ha ((IsFractionRing.injective (𝓞 E) E) (by simpa using h))
    have hcspan : a • c ∈ Submodule.span E (LBsub X β ξ : Set (Fin n → E)) :=
      Submodule.subset_span hcoef
    have := Submodule.smul_mem _ ((a : E)⁻¹) hcspan
    have heq : ((a : E)⁻¹) • (a • c) = c := by
      ext k
      change (a : E)⁻¹ * ((a : E) * c k) = c k
      field_simp [haE]
    simpa [heq] using this
def Sform : ReciprocityTheory.MultiplicativeHeights.HermForm E n where
  c := (IsCMField.complexConj E).toRingEquiv.toRingHom
  c_invol x := IsCMField.complexConj_apply_apply E x
  c_emb σ x := IsCMField.complexEmbedding_complexConj E σ x
  G := Matrix.of fun a b => herm X.Gm (β b) (β a)
  G_herm a b := HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm (β b) (β a)

private lemma herm_sum_smul_left' {m : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : Fin m → E)
    (v : Fin m → Fin r → E) (y : Fin r → E) :
    herm G (∑ k, c k • v k) y = ∑ k, c k * herm G (v k) y := by
  unfold herm
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * v k a * G a b * cc (y b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, c k * v k a * G a b * cc (y b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

private lemma herm_sum_smul_right' {m : ℕ} (G : Matrix (Fin r) (Fin r) E) (x : Fin r → E)
    (c : Fin m → E) (v : Fin m → Fin r → E) :
    herm G x (∑ k, c k • v k) = ∑ k, cc (c k) * herm G x (v k) := by
  unfold herm cc
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, x a * G a b * ((IsCMField.complexConj E) (c k) *
        (IsCMField.complexConj E) (v k b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, x a * G a b * ((IsCMField.complexConj E) (c k) *
        (IsCMField.complexConj E) (v k b)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

lemma Sform_h (c c' : Fin n → E) :
    (Sform X β).h c c' = herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k) := by
  rw [herm_sum_smul_left']
  simp only [herm_sum_smul_right', Finset.mul_sum]
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Sform, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  try simp only [cc, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.coe_ringEquiv]
  ring

lemma herm_perp (hβξ : ∀ k, herm X.Gm (β k) ξ = 0) (c : Fin n → E) :
    herm X.Gm (∑ k, c k • β k) ξ = 0 := by
  rw [herm_sum_smul_left']
  simp [hβξ]

private lemma herm_add_left_of_matrix (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  unfold herm
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma herm_add_right_of_matrix (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  unfold herm cc
  simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

private lemma herm_smul_left_of_matrix (G : Matrix (Fin r) (Fin r) E) (e : E) (x y : Fin r → E) :
    herm G (e • x) y = e * herm G x y := by
  unfold herm
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma herm_smul_right_lemma_6 (G : Matrix (Fin r) (Fin r) E) (e : E) (x y : Fin r → E) :
    herm G x (e • y) = cc e * herm G x y := by
  unfold herm cc
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma herm_cross (hβξ : ∀ k, herm X.Gm (β k) ξ = 0) (hξξ : herm X.Gm ξ ξ = 0)
    (c c' : Fin n → E) (e e' : E) :
    herm X.Gm (∑ k, c' k • β k + e' • ξ) (∑ k, c k • β k + e • ξ) =
      herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k) := by
  have hξβ : ∀ k, herm X.Gm ξ (β k) = 0 := fun k => by
    have h := HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm (β k) ξ
    rw [hβξ k] at h
    first
    | simpa [cc] using h
    | simpa [cc] using h.symm
  have hB : herm X.Gm ξ (∑ k, c k • β k) = 0 := by
    rw [herm_sum_smul_right']
    simp [hξβ]
  rw [herm_add_left_of_matrix, herm_add_right_of_matrix, herm_add_right_of_matrix, herm_smul_left_of_matrix,
    herm_smul_left_of_matrix, herm_smul_right_lemma_6, herm_smul_right_lemma_6, hB, herm_perp X β ξ hβξ c', hξξ]
  ring

lemma LB_selfDual (hξ : X.IsIso ξ) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin n → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    ReciprocityTheory.MultiplicativeHeights.IsSelfDual (Sform X β) (LBsub X β ξ) := by
  refine ⟨?_, ?_⟩
  · rintro c ⟨e, he⟩ c' ⟨e', he'⟩
    rw [Sform_h, ← herm_cross X β ξ hβξ hξ.2.1 c c' e e']
    exact ⟨⟨_, X.L'_int _ he' _ he⟩, rfl⟩
  · intro c hc
    obtain ⟨e, he⟩ := hermitian_lattice_pairing_duality r X ξ hξ (∑ k, c k • β k) (herm_perp X β ξ hβξ c) (by
      intro y hy hyξ
      obtain ⟨c', e', rfl⟩ := hspan y hyξ
      have hc' : c' ∈ LBsub X β ξ := ⟨e', hy⟩
      obtain ⟨z, hz⟩ := hc c' hc'
      rw [Sform_h] at hz
      have h1 : herm X.Gm (∑ k, c k • β k) (∑ k, c' k • β k + e' • ξ) =
          cc (herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k)) := by
        rw [herm_add_right', HermitianTraceFormVanishing.herm_smul_right, herm_perp X β ξ hβξ c, mul_zero, add_zero,
          HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm]
      rw [h1, ← hz]
      exact isIntegral_cc (RingOfIntegers.isIntegral_coe z))
    exact ⟨e, he⟩

lemma detG_ne (hξ : X.IsIso ξ) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin n → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    (Sform X β).G.det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hcG⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set μ := ∑ a, cc (c a) • β a with hμdef
  have hβμ : ∀ b, herm X.Gm (β b) μ = 0 := by
    intro b
    have h1 := congrFun hcG b
    simp only [Matrix.vecMul, dotProduct, Sform, Matrix.of_apply, Pi.zero_apply] at h1
    rw [hμdef, herm_sum_right']
    simp only [HermitianTraceFormVanishing.herm_smul_right, HermitianTraceFormVanishing.cc_cc]
    rw [← h1]
  have hμξ : herm X.Gm ξ μ = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm, hμdef, herm_perp X β ξ hβξ, HermitianTraceFormVanishing.cc_zero]
  have hperp : ∀ y, herm X.Gm y ξ = 0 → herm X.Gm μ y = 0 := by
    intro y hy
    obtain ⟨c', e', rfl⟩ := hspan y hy
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm, HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hμξ,
      herm_sum_left']
    simp only [HermitianTraceFormVanishing.herm_smul_left, hβμ, mul_zero, Finset.sum_const_zero, add_zero,
      HermitianTraceFormVanishing.cc_zero]
  obtain ⟨e, he⟩ := HermitianTraceFormVanishing.exists_eq_smul_of_herm X.Gm X.Gm_det X.Gm_herm ξ μ hξ.2.2 hperp
  have h := Fintype.linearIndependent_iff.mp hli (Fin.cons (-e) (fun a => cc (c a))) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    show -e • ξ + μ = 0
    rw [he, neg_smul, neg_add_cancel])
  apply hc0
  funext a
  have := h a.succ
  simpa using this

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
end

namespace ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def eps' (p : ℕ) {n : ℕ} (k : Fin n) : ℂ := if (k : ℕ) < p then 1 else -1

section Coord

variable (X : Data E r) (τ : X.Ψ) {n : ℕ} (p : ℕ) (f : Fin n → Fin r → ℂ)
  (hf : ∀ k l, hermC τ.1 X.Gm (f k) (f l) = if k = l then eps' p k else 0)
include hf

end Coord

def uc (X : Data E r) (z0 : Frame X.Ψ r) (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ :=
  v - (X.Hf z0 τ v (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
    Data.emb τ.1 ξ

section Uc

variable (X : Data E r) {z0 : Frame X.Ψ r} (ξ : Fin r → E) (τ : X.Ψ)

lemma uc_comb (hz : z0 ∈ X.dom) {n : ℕ} (a : Fin n → ℂ) (V : Fin n → Fin r → ℂ) :
    uc X z0 ξ τ (∑ k, a k • V k) = ∑ k, a k • uc X z0 ξ τ (V k) := by
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := X.ppos z0 τ, map_add' := X.ppos_add z0 τ,
      map_smul' := fun k u => X.ppos_smul_eq z0 τ k u }
  have hHf : ∀ u w, X.Hf z0 τ u w = hermC τ.1 X.Gm ((2 : ℂ) • L u - u) w := fun u w => rfl
  have hsum : X.Hf z0 τ (∑ k, a k • V k) (Data.emb τ.1 ξ) =
      ∑ k, a k * X.Hf z0 τ (V k) (Data.emb τ.1 ξ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hHf, map_sum]
    simp only [map_smul]
    have e : (2 : ℂ) • ∑ k, a k • L (V k) - ∑ k, a k • V k =
        ∑ k, a k • ((2 : ℂ) • L (V k) - V k) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_sub, smul_comm]
    rw [e, hermC_sum_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hermC_smul_left, hHf]
  unfold uc
  rw [hsum]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_smul, smul_smul,
    mul_div_assoc]

lemma uc_perp (hξξ : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (v v' : Fin r → ℂ)
    (hv : hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0) (hv' : hermC τ.1 X.Gm v' (Data.emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm (uc X z0 ξ τ v') (uc X z0 ξ τ v) = hermC τ.1 X.Gm v' v := by
  have hsubR : ∀ u w w' : Fin r → ℂ,
      hermC τ.1 X.Gm u (w - w') = hermC τ.1 X.Gm u w - hermC τ.1 X.Gm u w' := by
    intro u w w'
    simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsmulR : ∀ (c : ℂ) (u w : Fin r → ℂ),
      hermC τ.1 X.Gm u (c • w) = conj c * hermC τ.1 X.Gm u w := by
    intro c u w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hsym : hermC τ.1 X.Gm (Data.emb τ.1 ξ) v = 0 := by
    have hc : hermC τ.1 X.Gm (Data.emb τ.1 ξ) v = conj (hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hermC, map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← ReciprocityTheory.ChartRestriction.G.FD.emb_cc, X.Gm_herm]
      ring
    rw [hc, hv, map_zero]
  unfold uc
  simp only [hermC_sub_left, hsubR, hermC_smul_left, hsmulR, hv', hξξ, hsym, mul_zero, sub_zero]

end Uc

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
end

namespace ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma hermC_sub_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u w v : Fin r → ℂ) (a : ℂ) :
    hermC τ G (u - a • w) v = hermC τ G u v - a * hermC τ G w v := by
  unfold hermC
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma hermC_smul_left_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u v : Fin r → ℂ) (a : ℂ) :
    hermC τ G (a • u) v = a * hermC τ G u v := by
  have h := hermC_sub_smul_left τ G 0 u v (-a)
  have h0 : hermC τ G 0 v = 0 := by simp [hermC]
  simpa [h0] using h

private lemma hermC_sum_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (a : Fin n → ℂ) (g : Fin n → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ j, a j • g j) w = ∑ j, a j * hermC τ G (g j) w := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma hermC_sum_smul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (u : Fin r → ℂ) (b : Fin n → ℂ) (g : Fin n → Fin r → ℂ) :
    hermC τ G u (∑ l, b l • g l) = ∑ l, conj (b l) * hermC τ G u (g l) := by
  unfold hermC
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma herm_eq_hermC_emb_emb (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    τ (herm G x y) = hermC τ G (Data.emb τ x) (Data.emb τ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, hermC, map_sum, map_mul, Data.emb, cc, IsCMField.complexEmbedding_complexConj]

private lemma emb_sum_smul' (τ : E →+* ℂ) {n : ℕ} (c : Fin n → E) (β : Fin n → Fin r → E) :
    Data.emb τ (∑ k, c k • β k) = ∑ k, τ (c k) • Data.emb τ (β k) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Data.emb, Finset.sum_apply, map_sum, map_mul]

theorem Q_exists (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (β : Fin (r - 2) → Fin r → E) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hli : LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E))
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    ∃ Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ, (∀ τ, (Q τ).det ≠ 0) ∧
      (∀ τ (c c' : Fin (r - 2) → E), τ.1 ((Sform X β).h c c') =
        ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c)
          (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c')) ∧
      (∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
        ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k) := by
  classical
  have hξξ : herm X.Gm ξ ξ = 0 := hξ.2.1
  have hξ0 : ξ ≠ 0 := hξ.2.2
  have he0 : ∀ τ : X.Ψ, Data.emb τ.1 ξ ≠ 0 := by
    intro τ h
    apply hξ0
    funext a
    have h1 := congrFun h a
    simp only [Data.emb, Pi.zero_apply, map_eq_zero] at h1
    simpa using h1
  have hHf : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    intro τ
    rw [Data.Hf_self X.toData hz]
    exact_mod_cast (Data.maj_pos X.toData hz τ (he0 τ)).ne'
  have hperp : ∀ (τ : X.Ψ) (y : Fin r → E), herm X.Gm y ξ = 0 →
      hermC τ.1 X.Gm (Data.emb τ.1 y) (Data.emb τ.1 ξ) = 0 := by
    intro τ y hy
    rw [← herm_eq_hermC_emb_emb, hy, map_zero]
  have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 :=
    fun τ => hperp τ ξ hξξ
  have huc : ∀ (τ : X.Ψ) (v : Fin r → E),
      X.ucomp z0 ξ (X.embV v) τ = uc X.toData z0 ξ τ (Data.emb τ.1 v) := fun τ v => rfl
  have hmem : ∀ (τ : X.Ψ) (v : Fin r → ℂ), hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0 →
      uc X.toData z0 ξ τ v ∈ Submodule.span ℂ (Set.range (f τ)) := by
    intro τ v hv
    set e := Data.emb τ.1 ξ with he
    set t := X.Hf z0 τ v e / X.Hf z0 τ e e with ht
    have hu : uc X.toData z0 ξ τ v = v - t • e := rfl
    have h1 : hermC τ.1 X.Gm (uc X.toData z0 ξ τ v) e = 0 := by
      rw [hu, hermC_sub_smul_left, hv, hee τ]
      ring
    have h2 : X.Hf z0 τ (uc X.toData z0 ξ τ v) e = 0 := by
      have hl : (2 : ℂ) • X.ppos z0 τ (v - t • e) - (v - t • e) =
          ((2 : ℂ) • X.ppos z0 τ v - v) - t • ((2 : ℂ) • X.ppos z0 τ e - e) := by
        rw [ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines.ppos_sub X.toData, Data.ppos_smul_eq]
        module
      have hd : X.Hf z0 τ (uc X.toData z0 ξ τ v) e =
          X.Hf z0 τ v e - t * X.Hf z0 τ e e := by
        rw [hu]
        show hermC τ.1 X.Gm ((2 : ℂ) • X.ppos z0 τ (v - t • e) - (v - t • e)) e = _
        rw [hl, hermC_sub_smul_left]
        rfl
      rw [hd, ht, div_mul_cancel₀ _ (hHf τ), sub_self]
    have h3 : hermC τ.1 X.Gm (X.Jt z0 τ (uc X.toData z0 ξ τ v)) e = 0 := by
      show hermC τ.1 X.Gm (I • ((2 : ℂ) • X.ppos z0 τ (uc X.toData z0 ξ τ v) -
        uc X.toData z0 ξ τ v)) e = 0
      rw [hermC_smul_left_mul]
      change I * X.Hf z0 τ (uc X.toData z0 ξ τ v) e = 0
      rw [h2, mul_zero]
    exact (hf τ).2.2.2.2 _ h1 h3
  have hcoord : ∀ (τ : X.Ψ) (w : Fin r → ℂ), w ∈ Submodule.span ℂ (Set.range (f τ)) →
      w = ∑ j : Fin (r - 2), ((if (j : ℕ) < X.p0 - 1 then (1 : ℂ) else -1) * hermC τ.1 X.Gm w (f τ j)) • f τ j := by
    intro τ w hw
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hw
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [hermC_sum_smul_left]
    simp_rw [(hf τ).2.2.1]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs <;> ring
  let Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ := fun τ => Matrix.of fun j k =>
    (if (j : ℕ) < X.p0 - 1 then (1 : ℂ) else -1) *
      hermC τ.1 X.Gm (uc X.toData z0 ξ τ (Data.emb τ.1 (β k))) (f τ j)
  have hb : ∀ (τ : X.Ψ) (k : Fin (r - 2)),
      uc X.toData z0 ξ τ (Data.emb τ.1 (β k)) = ∑ j, Q τ j k • f τ j := by
    intro τ k
    exact hcoord τ _ (hmem τ _ (hperp τ _ (hβξ k)))
  have hQf : ∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
      ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k := by
    intro τ c
    rw [huc, emb_sum_smul', uc_comb (X := X.toData) (z0 := z0) (ξ := ξ) (τ := τ) hz]
    simp_rw [hb τ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mulVec, dotProduct, ReciprocityTheory.MultiplicativeHeights.embVec, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hp : ∀ (τ : X.Ψ) (c : Fin (r - 2) → E),
      hermC τ.1 X.Gm (Data.emb τ.1 (∑ k, c k • β k)) (Data.emb τ.1 ξ) = 0 := by
    intro τ c
    rw [emb_sum_smul', hermC_sum_smul_left]
    simp [hperp τ _ (hβξ _)]
  have hSQ : ∀ τ (c c' : Fin (r - 2) → E), τ.1 ((Sform X β).h c c') =
      ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c)
        (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c') := by
    intro τ c c'
    rw [Sform_h, herm_eq_hermC_emb_emb, ← uc_perp (X := X.toData) (z0 := z0) (ξ := ξ) (τ := τ) (hee τ)
      (Data.emb τ.1 (∑ k, c k • β k)) (Data.emb τ.1 (∑ k, c' k • β k)) (hp τ c) (hp τ c'),
      ← huc, ← huc, hQf, hQf, hermC_sum_smul_left]
    simp_rw [hermC_sum_smul_right, (hf τ).2.2.1]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.sgn
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  refine ⟨Q, ?_, hSQ, hQf⟩
  intro τ hdet
  apply detG_ne (X := X) (ξ := ξ) (β := β) hξ hβξ hli hspan
  have hmap : τ.1.mapMatrix (Sform X β).G = (Q τ)ᴴ *
      Matrix.diagonal (fun k : Fin (r - 2) => ReciprocityTheory.MultiplicativeHeights.sgn (X.p0 - 1) k) * Q τ := by
    ext a b
    have h := hSQ τ (Pi.single a 1) (Pi.single b 1)
    have hh : (Sform X β).h (Pi.single a 1) (Pi.single b 1) = (Sform X β).G a b := by
      simp [ReciprocityTheory.MultiplicativeHeights.HermForm.h, Pi.single_apply, apply_ite, ite_mul, mul_ite]
    have hs : ∀ a : Fin (r - 2), ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (Pi.single a (1 : E)) = Pi.single a 1 := by
      intro a
      funext i
      by_cases hi : i = a
      · subst hi; simp [ReciprocityTheory.MultiplicativeHeights.embVec]
      · simp [ReciprocityTheory.MultiplicativeHeights.embVec, hi]
    rw [hh, hs, hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h]
    simp [ReciprocityTheory.MultiplicativeHeights.jForm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdm := RingHom.map_det τ.1 (Sform X β).G
  rw [hmap, Matrix.det_mul, Matrix.det_mul, hdet, mul_zero] at hdm
  exact (map_eq_zero τ.1).1 hdm

end

end ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence

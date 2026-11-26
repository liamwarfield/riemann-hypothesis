module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincLocStep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.Opn

theorem exists_princ_loc_step : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n T f : ℕ} {J : Matrix (Fin n) (Fin n) E} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)), J = 1 → ∃ M : ℕ, 0 < M ∧ ∀ y ∈ UPts σ J (v.adicCompletion F), (∀ a b, ∃ c ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring, ((y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) a b = (M : E ⊗[F] v.adicCompletion F) * c) → y ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n T f J bad S v hJ
  subst hJ
  obtain ⟨M, hM, hMU⟩ := GlobalTheory.Mem.Col2.AdT.Opn.exists_princ σ S.U S.U_open
  refine ⟨M, Nat.pos_of_ne_zero hM, fun y hy hc => ?_⟩
  choose C hC hyC using hc
  have hz := Formalism.UG.P.afsplitU_mem v σ 1 y 1 hy (one_mem _)
  have hzU : Formalism.UG.P.afsplitU v y 1 ∈ S.U := by
    refine hMU _ hz fun a b => ?_
    have hyab : (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b + M • C a b := by
      rw [nsmul_eq_mul, ← hyC a b, Matrix.sub_apply, add_sub_cancel]
    have e : (((Formalism.UG.P.afsplitU v y 1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
        (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * Formalism.UG.P.afsplitIE v (C a b) := by
      rw [Matrix.sub_apply, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_apply, Units.val_one, hyab, map_add (f := _), map_nsmul,
        nsmul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.one_apply_eq, Formalism.UG.P.afsplitEps]
        ring
      · simp [Matrix.one_apply_ne hab]
    rw [e, ← mul_assoc, ← map_natCast (Formalism.L2.Col.iA F E), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, one_mul]
    exact Formalism.UG.P.afsplit_IE_int v _ (hC a b)
  have h := ((S.U_eq _).1 hzU).2 v
  rwa [Formalism.UG.P.afsplit_right1] at h

end GlobalTheory.Mem.Col2.AdT.Opn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatSmulMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIntegral
namespace GlobalTheory.NatMulIntegralExists

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have hz : IsAlgebraic ℤ a := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ a)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hint.neg

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
    ∀ (w : Fin r → E), ∃ (k : ℕ), (0 : ℕ) < k ∧ (↑k : E) • w ∈ Λ := by
  intro E _ _ r Λ hspan w
  have hw : w ∈ Submodule.span E (↑Λ : Set (Fin r → E)) := by rw [hspan]; trivial

  have hnat : ∀ (n : ℕ) (v : Fin r → E), v ∈ Λ → (n : E) • v ∈ Λ := by
    intro n v hv
    rw [Nat.cast_smul_eq_nsmul]
    exact Λ.nsmul_mem hv n
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k₁, hk₁, h₁⟩ := hx
    obtain ⟨k₂, hk₂, h₂⟩ := hy
    refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩
    have e : ((k₁ * k₂ : ℕ) : E) • (x + y) = (k₂ : E) • ((k₁ : E) • x) + (k₁ : E) • ((k₂ : E) • y) := by
      rw [smul_add, smul_smul, smul_smul]; push_cast; ring_nf
    rw [e]
    exact Λ.add_mem (hnat _ _ h₁) (hnat _ _ h₂)
  | smul a x _ hx =>
    obtain ⟨k, hk, h⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_nat_mul_integral a
    refine ⟨d * k, Nat.mul_pos hd hk, ?_⟩
    let c : NumberField.RingOfIntegers E := ⟨(d : E) * a, hint⟩
    have e : ((d * k : ℕ) : E) • (a • x) = c • ((k : E) • x) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Algebra.smul_def]
      change _ = ((d : E) * a) * _
      push_cast; ring
    rw [e]
    exact Λ.smul_mem c h

end GlobalTheory.NatMulIntegralExists
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PrincLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mul_mem (c : E) : ∃ m : ℕ, 0 < m ∧ (m : E) * c ∈ intOE E := by
  obtain ⟨y, hy, hint'⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
  have hint := hint' c (Finset.mem_singleton_self c)
  have key : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : E) * c) := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
    · refine ⟨n, by rintro rfl; simp at hy, ?_⟩
      have e : ((n : E) * c) = ((n : ℤ) • c) := by rw [zsmul_eq_mul]; push_cast; ring
      rw [e]; exact hint
    · refine ⟨n, by rintro rfl; simp at hy, ?_⟩
      have e : ((n : E) * c) = -((-(n : ℤ)) • c) := by rw [zsmul_eq_mul]; push_cast; ring
      rw [e]; exact hint.neg
  obtain ⟨n, hn, h2⟩ := key
  refine ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 h2
  exact ⟨a, ha⟩

theorem exists_nat_smul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E))
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (w : Fin r → E) :
    ∃ k : ℕ, 0 < k ∧ (k : E) • w ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegralExists.main
  | exact _root_.GlobalTheory.NatMulIntegralExists.main
  | (apply _root_.GlobalTheory.NatMulIntegralExists.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegralExists.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegralExists.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegralExists.main ..)

theorem exists_nat_den {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ w ∈ Λ, ∀ i, (d : E) * w i ∈ intOE E := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  choose m hm hmem using fun (p : (Fin r → E) × Fin r) => exists_nat_mul_mem (E := E) (p.1 p.2)
  refine ⟨∏ p ∈ s ×ˢ Finset.univ, m p, Finset.prod_pos fun p _ => hm p, ?_⟩
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    intro i
    obtain ⟨k, hk⟩ : m (x, i) ∣ ∏ p ∈ s ×ˢ Finset.univ, m p :=
      Finset.dvd_prod_of_mem _ (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
    have e : ((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * x i = (k : E) * ((m (x, i) : E) * x i) := by
      rw [hk]; push_cast; ring
    rw [e]
    exact mul_mem (natCast_mem _ k) (hmem (x, i))
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    have e : ((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * (a • x) i =
        algebraMap (𝓞 E) E a * (((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * x i) := by
      rw [Pi.smul_apply, Algebra.smul_def]; ring
    rw [e]
    exact mul_mem ⟨a, rfl⟩ (hx i)

theorem den_locL (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {d : ℕ}
    (hd : ∀ w ∈ Λ, ∀ i, (d : E) * w i ∈ intOE E) {y : Fin r → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ Formalism.L2.Herm.locL v Λ) :
    ∀ i, (d : E ⊗[F] v.adicCompletion F) * y i ∈ intV E v := by
  unfold Formalism.L2.Herm.locL latS at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    intro i
    have e : (d : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (w i) =
        inclE (F := F) (v.adicCompletion F) ((d : E) * w i) := by
      rw [map_mul, map_natCast]
    rw [e]
    exact Subring.subset_closure (Or.inl ⟨⟨_, hd w hw i⟩, rfl⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem a.2 (hx i)

theorem princ_lat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {r : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ d : ℕ, 0 < d ∧ ∀ (M : ℕ) (x : Matrix (Fin r) (Fin r) (E ⊗[F] v.adicCompletion F)), (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ, x *ᵥ y - y = ((M * d : ℕ) : E ⊗[F] v.adicCompletion F) • z) → ∀ a b, ∃ c ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring, (x - 1) a b = (M : E ⊗[F] v.adicCompletion F) * c := by
  intro F E _ _ _ _ _ r v Λ hfg hsp
  classical
  choose k hk hkmem using fun b : Fin r => exists_nat_smul_mem Λ hsp (Pi.single b 1)
  obtain ⟨d₂, hd₂, hden⟩ := exists_nat_den Λ hfg
  have hd₁ : 0 < ∏ b, k b := Finset.prod_pos fun b _ => hk b
  have hmem : ∀ b, ((∏ b, k b : ℕ) : E) • (Pi.single b 1 : Fin r → E) ∈ Λ := fun b => by
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ b)
    have e : ((∏ b, k b : ℕ) : E) • (Pi.single b 1 : Fin r → E) = t • ((k b : E) • (Pi.single b 1 : Fin r → E)) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, ht, Nat.cast_mul, mul_comm]
    rw [e]
    exact Λ.toAddSubmonoid.nsmul_mem (hkmem b) t
  refine ⟨(∏ b, k b) * d₂, Nat.mul_pos hd₁ hd₂, fun M x hx a b => ?_⟩
  set d₁ := ∏ b, k b with hd₁def
  let y : Fin r → E ⊗[F] v.adicCompletion F :=
    fun i => inclE (F := F) (v.adicCompletion F) (((d₁ : E) • (Pi.single b 1 : Fin r → E)) i)
  have hy : y ∈ Formalism.L2.Herm.locL v Λ := Submodule.subset_span ⟨_, hmem b, rfl⟩
  obtain ⟨z, hz, hxz⟩ := hx y hy
  have hy' : y = (d₁ : E ⊗[F] v.adicCompletion F) • (Pi.single b 1 : Fin r → E ⊗[F] v.adicCompletion F) := by
    funext i
    simp only [y, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
    by_cases h : i = b
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hcol : x *ᵥ y - y = (d₁ : E ⊗[F] v.adicCompletion F) • ((x - 1) *ᵥ Pi.single b 1) := by
    rw [hy', Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub]
  have h1 := congrFun hxz a
  rw [hcol, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply, smul_eq_mul,
    smul_eq_mul] at h1
  have hu : IsUnit (d₁ : E ⊗[F] v.adicCompletion F) := by
    have := (IsUnit.mk0 (d₁ : F) (Nat.cast_ne_zero.2 hd₁.ne')).map (algebraMap F (E ⊗[F] v.adicCompletion F))
    rwa [map_natCast] at this
  refine ⟨(d₂ : E ⊗[F] v.adicCompletion F) * z a, den_locL v Λ hden hz a, ?_⟩
  apply hu.mul_left_cancel
  rw [h1]
  push_cast
  ring

end GlobalTheory.PrincLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupContainsPrincipalCongruence
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevQ

theorem princ_in_chart_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {a b T f : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E)
    (hG : G.reindex (finCongr h) (finCongr h) = 1) {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ (G.reindex (finCongr h) (finCongr h)) T f bad) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin a → E)) (hfg : Module.Finite (𝓞 E) (reL h Λ))
    (hsp : Submodule.span E (reL h Λ : Set (Fin b → E)) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : GL (Fin a) (E ⊗[F] v.adicCompletion F), x ∈ levelVL σ G v Λ →
      (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ,
        (x : Matrix (Fin a) (Fin a) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (n : E ⊗[F] v.adicCompletion F) • z) →
      x ∈ (S.Uloc v).comap (reGL h (E ⊗[F] v.adicCompletion F)).toMonoidHom := by
  subst h
  have hR : ∀ (L : Submodule (𝓞 E) (Fin a → E)), reL rfl L = L := by
    intro L
    ext x
    simp [reL, reV]
  have hGr : G.reindex (finCongr rfl) (finCongr rfl) = G := by
    ext i j; simp
  rw [hR] at hfg hsp
  obtain ⟨M, hM, hMU⟩ := GlobalTheory.Mem.Col2.AdT.Opn.exists_princ_loc_step σ S v hG
  obtain ⟨d, hd, hdA⟩ := GlobalTheory.PrincLat.princ_lat v Λ (Module.Finite.iff_fg.1 hfg) hsp
  refine ⟨M * d, Nat.mul_pos hM hd, fun x hx hpr => ?_⟩
  have hxe : reGL rfl (E ⊗[F] v.adicCompletion F) x = x := by
    apply Units.ext
    ext i j
    simp [reGL]
  show reGL rfl (E ⊗[F] v.adicCompletion F) x ∈ S.Uloc v
  rw [hxe]
  refine hMU x ?_ (hdA M _ hpr)
  have hu : x ∈ UPts σ G (v.adicCompletion F) := hx.1
  rw [hGr]
  exact hu

theorem chart_contains_princ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hUloc hchi Lb0 hLb β v hv
  have hG := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  have hfg : Module.Finite (𝓞 (I.rec7 l Z).host.E) (reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0) := by
    rw [← hLb]; exact (F u).levJ.Lb_fin
  have hsp : Submodule.span (I.rec7 l Z).host.E
      (reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 : Set (Fin ((I.rec7 l Z).R.N (B.R.m - 1)) → (I.rec7 l Z).host.E)) = ⊤ := by
    rw [← hLb]; exact (F u).levJ.Lb_span
  obtain ⟨n, hn, hN⟩ := princ_in_chart_gen (sigD (I.rec7 l Z)) (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _))
    ((I.rec7 l Z).sp.X (B.R.m - 1)).gram hG (K β).lev v Lb0 hfg hsp
  exact ⟨n, hn, fun x hx => hN x hx.1 hx.2⟩

end GlobalTheory.Mem.Col2.AdT.LevQ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupContainsPrincipalCongruenceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_local_group_contains_principal_congruence : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ | exact GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ | (intros; apply GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ <;> assumption)
end

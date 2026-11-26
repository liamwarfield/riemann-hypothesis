module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticePropsOfModel

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open Formalism.GradedWeylDivisibility (blockAct)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem valuation_class_translate_mem (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (lam : ι → DomWeight n) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) {V : Frames (gramC J emb) → ℂ}
    (hV : V ∈ ValC (gramC J emb) lam) :
    (fun y => V (frameTranslate emb hc γ hγ y)) ∈ ValC (gramC J emb) lam := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hV
  refine Submodule.mem_map.2 ⟨(∏ τ, (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ).det ^ shiftOf lam τ) •
    blockAct ℂ (atInf emb (γ : Matrix (Fin n) (Fin n) E)) P,
    Submodule.smul_mem _ _ (complex_span_block_action_stable lam _ hP), ?_⟩
  rw [← Formalism.L2.Col.fnOf_mul]
  funext y
  simp only [fnOf, frameTranslate, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.mul_one, Matrix.one_mul]

theorem class_rep_translate_unique (S : StepLevel F E σ J T f bad) {C : Type} (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hinj : Function.Injective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hstab : ∀ c (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → γ = 1)
    (c1 c2 : C) (γ1 γ2 : GL (Fin n) E) (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J)
    (κ1 κ2 : S.U)
    (e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * (yc c1).1 * κ1.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * (yc c2).1 * κ2.1) :
    c1 = c2 ∧ γ1 = γ2 ∧ κ1 = κ2 := by
  have hU : ∀ κ : S.U, κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := fun κ => ((S.U_eq κ.1).1 κ.2).1
  set k : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ1.1 * κ2.1⁻¹, (UPts _ _ _).mul_mem (hU κ1) ((UPts _ _ _).inv_mem (hU κ2))⟩
  set h : UPts σ J (FiniteAdeleRing (𝓞 F) F) := yc c2 * k⁻¹ * (yc c1)⁻¹
  have hh : h.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ2⁻¹ * γ1) := by
    simp only [h, k, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    have e' : (yc c2).1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2)⁻¹ *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * (yc c1).1 * κ1.1) * κ2.1⁻¹ := by
      rw [e]; group
    rw [e']; group
  have hc : c1 = c2 := by
    apply hinj
    show (Quotient.mk'' (yc c1) : Cls S) = Quotient.mk'' (yc c2)
    refine (@DoubleCoset.eq _ _ _ _ (yc c1) (yc c2)).2 ⟨h, ?_, k, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ2⁻¹ * γ1, (UJ _ _).mul_mem ((UJ _ _).inv_mem h2) h1, hh.symm⟩)
    · exact Subgroup.mem_subgroupOf.2 (S.U.mul_mem κ1.2 (S.U.inv_mem κ2.2))
    · simp only [h]; group
  subst hc
  have hγ : γ2⁻¹ * γ1 = 1 := by
    apply hstab c1 _ ((UJ _ _).mul_mem ((UJ _ _).inv_mem h2) h1)
    refine Subgroup.mem_map.2 ⟨κ2.1 * κ1.1⁻¹, S.U.mul_mem κ2.2 (S.U.inv_mem κ1.2), ?_⟩
    show (yc c1).1 * (κ2.1 * κ1.1⁻¹) * (yc c1).1⁻¹ = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ2⁻¹ * γ1)
    rw [map_mul, map_inv]
    have e' : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * (yc c1).1 * κ2.1 * κ1.1⁻¹ * (yc c1).1⁻¹ := by
      rw [← e]; group
    rw [e']; group
  have hγ' : γ1 = γ2 := by
    have := congrArg (γ2 * ·) hγ
    simpa [← mul_assoc] using this
  subst hγ'
  refine ⟨rfl, rfl, Subtype.ext ?_⟩
  have := e
  rw [mul_assoc, mul_assoc] at this
  exact mul_left_cancel (mul_left_cancel this)

theorem adelic_function_ext (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (lam : ι → DomWeight n) {C : Type}
    (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hbij : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hstab : ∀ c (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → γ = 1)
    (φ : C → Frames (gramC J emb) → ℂ) (hφ : ∀ c, φ c ∈ ValC (gramC J emb) lam) :
    φ ∈ FiC S emb lam yc := by
  have hdec : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ c, ∃ γ : GL (Fin n) E, ∃ _ : γ ∈ UJ (σ : E →+* E) J,
      ∃ κ : S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1 := by
    intro x
    obtain ⟨c, hcx⟩ := hbij.2 (Quotient.mk'' x)
    obtain ⟨hh, hhH, κ, hκK, e⟩ := (@DoubleCoset.eq _ _ _ _ (yc c) x).1 hcx
    obtain ⟨g, hgU, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
    refine ⟨c, g, hgU, ⟨κ.1, hκK⟩, ?_⟩
    have := congrArg Subtype.val e
    simp only [Subgroup.coe_mul] at this
    rw [this, hge]
  choose cx γx hγx κx hx using hdec
  have hun := class_rep_translate_unique S yc hbij.1 hstab
  refine Submodule.mem_map.2 ⟨fun x y => (S.chi (κx x) : ℂ) *
    φ (cx x) (frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y), Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  ·
    intro γ' hγ' x x' κ' hx' y y' hy
    obtain ⟨hc2, hg2, hk2⟩ := hun (cx x') (cx x) (γx x') (γ' * γx x) (hγx x') ((UJ _ _).mul_mem hγ' (hγx x))
      (κx x') (κx x * κ') (by
        rw [← hx x', hx', hx x, map_mul, Subgroup.coe_mul]; group)
    have hfr : frameTranslate emb hc (γx x')⁻¹ ((UJ _ _).inv_mem (hγx x')) y =
        frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y' := by
      apply Subtype.ext
      funext τ
      show atInf emb (((γx x')⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ =
        atInf emb (((γx x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y'.1 τ
      rw [hy τ, hg2, _root_.mul_inv_rev]
      simp only [atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    show (S.chi (κx x') : ℂ) * φ (cx x') (frameTranslate emb hc (γx x')⁻¹ ((UJ _ _).inv_mem (hγx x')) y) =
      (S.chi κ' : ℂ) * ((S.chi (κx x) : ℂ) * φ (cx x) (frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y'))
    rw [hfr, hc2, hk2, map_mul, Units.val_mul]
    ring
  · refine Submodule.mem_pi.2 fun x _ => ?_
    exact Submodule.smul_mem _ _ (valuation_class_translate_mem emb hc lam _ _ (hφ (cx x)))
  · funext c y
    obtain ⟨hc1, hg1, hk1⟩ := hun (cx (yc c)) c (γx (yc c)) 1 (hγx (yc c)) (UJ _ _).one_mem (κx (yc c)) 1 (by
      rw [← hx (yc c), map_one]; simp)
    show (S.chi (κx (yc c)) : ℂ) * φ (cx (yc c)) (frameTranslate emb hc (γx (yc c))⁻¹ ((UJ _ _).inv_mem (hγx (yc c))) y) = φ c y
    have hfr : frameTranslate emb hc (γx (yc c))⁻¹ ((UJ _ _).inv_mem (hγx (yc c))) y = y := by
      apply Subtype.ext
      funext τ
      show atInf emb (((γx (yc c))⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = y.1 τ
      rw [hg1, inv_one]
      simp [atInf]
    rw [hfr, hc1, hk1, map_one, Units.val_one, one_mul]

end Gen

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL6.FrameTranslate
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem rnd_tr_tr (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (a b : GL (Fin n) E) (ha : a ∈ UJ (σ : E →+* E) J) (hb : b ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) :
    frameTranslate emb hc a ha (frameTranslate emb hc b hb y) = frameTranslate emb hc (a * b) ((UJ (σ : E →+* E) J).mul_mem ha hb) y := by
  apply Subtype.ext
  funext τ
  simp only [frameTranslate, atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem rnd_tr_one (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (y : Frames (gramC J emb)) : frameTranslate emb hc 1 (UJ (σ : E →+* E) J).one_mem y = y := by
  apply Subtype.ext
  funext τ
  simp [frameTranslate, atInf]

theorem rnd_tr_congr (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {a b : GL (Fin n) E} (hab : a = b) (ha : a ∈ UJ (σ : E →+* E) J) (hb : b ∈ UJ (σ : E →+* E) J)
    (y : Frames (gramC J emb)) : frameTranslate emb hc a ha y = frameTranslate emb hc b hb y := by
  subst hab; rfl

end Gen

section Fill

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

def RndStabTriv (S : StepLevel F E σ J T f bad) (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Prop :=
  ∀ δ : GL (Fin n) E, δ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) δ * x0.1 = x0.1 * κ.1 → δ = 1

theorem rnd_uniq (S : StepLevel F E σ J T f bad) (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0)
    {a b : GL (Fin n) E} (ha : a ∈ UJ (σ : E →+* E) J) (hb : b ∈ UJ (σ : E →+* E) J) {k l : S.U}
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) a * x0.1 * k.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) b * x0.1 * l.1) : a = b ∧ k = l := by
  have hδ : b⁻¹ * a ∈ UJ (σ : E →+* E) J := (UJ (σ : E →+* E) J).mul_mem ((UJ (σ : E →+* E) J).inv_mem hb) ha
  have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (b⁻¹ * a) * x0.1 = x0.1 * (l * k⁻¹ : S.U).1 := by
    have h' : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) a * x0.1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) b * x0.1 * l.1 * k.1⁻¹ := by
      rw [← h]; group
    rw [map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv, mul_assoc, h']; group
  have h1 := hs _ hδ _ e
  have hab : a = b := (inv_mul_eq_one.1 h1).symm
  subst hab
  exact ⟨rfl, Subtype.ext (mul_left_cancel h)⟩


open Classical in
def rndFillG (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h : Frames (gramC J emb) → ℂ) :
    UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ := fun x y =>
  if hx : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1 then
    (S.chi (Classical.choose hx).2 : ℂ) *
      h (frameTranslate emb hc (Classical.choose hx).1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem (Classical.choose hx).1.2) y)
  else 0

theorem rnd_fillG_eq (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ)
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U)
    (hp : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1) (y : Frames (gramC J emb)) :
    rndFillG S emb hc x0 h x y =
      (S.chi p.2 : ℂ) * h (frameTranslate emb hc p.1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem p.1.2) y) := by
  have hx : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1 := ⟨p, hp⟩
  unfold rndFillG
  rw [dite_eq_left hx]
  have hq := Classical.choose_spec hx
  have hu := rnd_uniq S x0 hs (Classical.choose hx).1.2 p.1.2 (k := (Classical.choose hx).2) (l := p.2)
    (by rw [← hq, ← hp])
  have hpq : Classical.choose hx = p := Prod.ext (Subtype.ext hu.1) hu.2
  exact congrArg (fun q : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U =>
    (S.chi q.2 : ℂ) * h (frameTranslate emb hc q.1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem q.1.2) y)) hpq

theorem rnd_fillG_eq' (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ)
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (a : GL (Fin n) E) (ha : a ∈ UJ (σ : E →+* E) J) (k : S.U)
    (hp : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) a * x0.1 * k.1) (y : Frames (gramC J emb)) :
    rndFillG S emb hc x0 h x y = (S.chi k : ℂ) * h (frameTranslate emb hc a⁻¹ ((UJ (σ : E →+* E) J).inv_mem ha) y) :=
  rnd_fillG_eq S emb hc x0 hs h x (⟨a, ha⟩, k) hp y

theorem rnd_fill_at (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ) :
    rndFillG S emb hc x0 h x0 = h := by
  funext y
  rw [rnd_fillG_eq S emb hc x0 hs h x0 (⟨1, (UJ (σ : E →+* E) J).one_mem⟩, 1) (by simp) y, map_one, Units.val_one,
    one_mul, rnd_tr_congr emb hc (inv_one) _ (UJ (σ : E →+* E) J).one_mem, rnd_tr_one]

open Classical in
theorem rnd_fill_mem (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ) :
    rndFillG S emb hc x0 h ∈ AdFun S emb := by
  intro γ hγ x x' κ hx y y' hy
  have hy' : y' = frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y := by
    apply Subtype.ext; funext τ
    show y'.1 τ = atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ
    rw [hy τ, ← Matrix.mul_assoc]
    simp only [atInf]
    rw [← Matrix.map_mul, Units.inv_mul]; simp
  by_cases h1 : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1
  · obtain ⟨p, hp⟩ := h1
    have hp' : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ * p.1.1) * x0.1 * (p.2 * κ).1 := by
      simp only [hx, hp, map_mul, Subgroup.coe_mul]; group
    rw [rnd_fillG_eq' S emb hc x0 hs h x' (γ * p.1.1) ((UJ (σ : E →+* E) J).mul_mem hγ p.1.2) (p.2 * κ) hp' y, rnd_fillG_eq S emb hc x0 hs h x p hp y', map_mul, Units.val_mul,
      rnd_tr_congr emb hc (mul_inv_rev γ p.1.1) _
        ((UJ (σ : E →+* E) J).mul_mem ((UJ (σ : E →+* E) J).inv_mem p.1.2) ((UJ (σ : E →+* E) J).inv_mem hγ)),
      ← rnd_tr_tr, ← hy']
    ring
    · exact (UJ (σ : E →+* E) J).inv_mem p.1.2
    · exact (UJ (σ : E →+* E) J).inv_mem hγ
  · have h2 : ¬ ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
        x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1 := by
      rintro ⟨p, hp⟩
      refine h1 ⟨(⟨γ⁻¹ * p.1.1, (UJ (σ : E →+* E) J).mul_mem ((UJ (σ : E →+* E) J).inv_mem hγ) p.1.2⟩, p.2 * κ⁻¹), ?_⟩
      have : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ⁻¹ * x'.1 * κ.1⁻¹ := by rw [hx, map_inv]; group
      rw [this, hp, map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv]; group
    unfold rndFillG
    rw [dite_eq_right h1, dite_eq_right h2, mul_zero]

end Fill

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.YvRatOfValRat

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValUniqOf
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}

theorem frames_tr (emb : Tau → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (γ : GL (Fin n) E)
    (hγ : γ ∈ UJ (σ : E →+* E) J) (z : Frames (gramC J emb)) : ∃ z' : Frames (gramC J emb), IsTr (atInf emb γ) z' z := by
  have h1 : ∀ τ, atInf emb γ τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
    intro τ
    rw [← atInf_mul, ← Units.val_mul, mul_inv_cancel]
    simp [atInf]
  refine ⟨⟨fun τ => atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ, fun τ => ?_⟩, fun τ => ?_⟩
  · rw [Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (h1 τ)).mul (z.2 τ)
  · show z.1 τ = atInf emb γ τ * (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ)
    rw [← Matrix.mul_assoc, ← atInf_mul, ← Units.val_mul, mul_inv_cancel]
    simp [atInf]

variable (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ)
  (G : GAtP p) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module LL V] (embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def EvInj : Prop :=
  ∀ Q : XR G.P ℂ, evC G.P A.rk pos (gramC J emb) (crdB emb A.B) Q = 0 → Q = 0

def PtEx : Prop :=
  ∀ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)), ∃ (c : cls) (γ : GL (Fin n) E) (κ : S.U),
    γ ∈ UJ (σ : E →+* E) J ∧ A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1)

variable {S emb embLL G A pos embV yc}

theorem valUniq_of (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hi : EvInj emb G A pos (J := J))
    (hp : PtEx S G A yc) : ValUniq S emb embLL G A pos embV yc := by
  intro x i L Q Q' hL h h'
  choose g0 hg0 hLg using hL
  let g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v) := fun v => ((Matrix.isUnit_iff_isUnit_det _).2 (hg0 v)).unit
  have hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := hLg
  obtain ⟨c, γ, κ, hγ, hpt⟩ := hp i g
  have hz : evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q - MvPolynomial.map embLL Q') = 0 := by
    funext z
    obtain ⟨z', hz'⟩ := frames_tr emb hc γ hγ z
    rw [map_sub, Pi.sub_apply, h.2 g hg c γ hγ κ hpt z z' hz', h'.2 g hg c γ hγ κ hpt z z' hz', sub_self]
    rfl
  have := hi _ hz
  exact MvPolynomial.map_injective embLL embLL.injective (sub_eq_zero.1 this)

end Formalism.L2.G.Cmp

end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanRec
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions

section Pl

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (α : Type) {LL : Type} [Field LL] (e : LL →+* Kf) (Mi : Submodule O (FnP P α))

abbrev modLL : Module LL (FnP P α) := Module.compHom _ e

theorem isRational_add {F F' : FnP P α} (h : RatFnP P α e F) (h' : RatFnP P α e F') : RatFnP P α e (F + F') := by
  intro i L
  obtain ⟨Q, hQ⟩ := h i L
  obtain ⟨Q', hQ'⟩ := h' i L
  exact ⟨Q + Q', by rw [map_add (f := _), hQ, hQ']; rfl⟩

theorem isRational_smul (a : LL) {F : FnP P α} (h : RatFnP P α e F) : RatFnP P α e (e a • F) := by
  intro i L
  obtain ⟨Q, hQ⟩ := h i L
  refine ⟨MvPolynomial.C a * Q, ?_⟩
  rw [map_mul, MvPolynomial.map_C, hQ, ← MvPolynomial.smul_eq_C_mul]
  rfl

def formsLL : @Submodule LL (FnP P α) _ _ (modLL P α e) :=
  letI := modLL P α e
  { carrier := {F | F ∈ Submodule.span Kf (Mi : Set (FnP P α)) ∧ RatFnP P α e F}
    add_mem' := fun h h' => ⟨Submodule.add_mem _ h.1 h'.1, isRational_add P α e h.2 h'.2⟩
    zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => ⟨0, map_zero _⟩⟩
    smul_mem' := fun a _ h => ⟨Submodule.smul_mem _ (e a) h.1, isRational_smul P α e a h.2⟩ }

abbrev FormsLL : Type := ↥(formsLL P α e Mi)

instance : Module LL (FormsLL P α e Mi) :=
  letI := modLL P α e
  Submodule.module _

def cmpF : FormsLL P α e Mi →+ FnP P α :=
  letI := modLL P α e
  (formsLL P α e Mi).subtype.toAddMonoidHom

theorem cmpF_apply (x : FormsLL P α e Mi) : cmpF P α e Mi x = x.1 := rfl

theorem cmpF_rat (x : FormsLL P α e Mi) : RatFnP P α e (cmpF P α e Mi x) := by rw [cmpF_apply]; exact x.2.2

def intLL : Set (FormsLL P α e Mi) := {x | cmpF P α e Mi x ∈ Mi}

def MRatSpan : Prop := Submodule.span O (cmpF P α e Mi '' intLL P α e Mi) = Mi

end Pl

section Rec

variable {D : D7} (c : LatCmp D)

abbrev FormsRec u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Type :=
  FormsLL (D.gat u w hg).P (D.gat u w hg).comp (c.embW u w hg) (D.gat u w hg).M

def equivRec (h : ValRat c) u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] FormsRec c u w hg :=
  LinearEquiv.ofBijective
    { toFun := fun x => ⟨c.cmp u w hg x, cmp_mem_span c u w hg x, h.all c u w hg x⟩
      map_add' := fun x y => Subtype.ext (map_add (c.cmp u w hg) x y)
      map_smul' := fun a x => Subtype.ext (c.cmp_smul u w hg a x) }
    ⟨fun x y hxy => cmp_inj c u w hg (congrArg Subtype.val hxy), fun F => by
      obtain ⟨x, hx⟩ := (range_cmp c h u w hg F.1).2 F.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem mRatSpan_rec (h : ValRat c) u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    MRatSpan (D.gat u w hg).P (D.gat u w hg).comp (c.embW u w hg) (D.gat u w hg).M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · refine (c.cmp_M u w hg).symm.le.trans ?_
    apply Submodule.span_mono
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨equivRec c h u w hg x, ?_, rfl⟩
    show c.cmp u w hg x ∈ (D.gat u w hg).M
    rw [← c.cmp_M u w hg]
    exact Submodule.subset_span ⟨x, hx, rfl⟩

end Rec

end Formalism.L2.G.Cmp
end
end

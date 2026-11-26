module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExistsOfMemSmulLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.GlobEntry

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAT
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section T

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ThCorr (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t₁ t₂ : Term V M r)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'),
    H.IsGeneric t₁ → H.IsGeneric t₂ → H.Respects t₁ t₂ φ φ' →
    ∀ (w₁ : V) (hw₁ : w₁ ∈ H.W0 t₁.f t₁.f') (w₂ : V) (hw₂ : w₂ ∈ H.W0 t₂.f t₂.f'),
      φ (H.mkW t₁.f ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp H hw₁⟩) = H.mkW t₂.f ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H hw₂⟩ →
      φ' (H.mkW t₁.f' ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp' H hw₁⟩) = H.mkW t₂.f' ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H hw₂⟩ →
      (w₁ ∈ t₁.abelian₂ ↔ w₂ ∈ t₂.abelian₂)

theorem mem_iff_of_image_eq {A B : Type} [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B]
    (φ : A ≃ₗ[E] B) {S : Set A} {T : Set B} (h : φ '' S = T) {a : A} {b : B} (hab : φ a = b) :
    a ∈ S ↔ b ∈ T := by
  subst hab
  subst h
  exact φ.injective.mem_set_image.symm

theorem thCorr_holds (M : Model F E) (r : ℕ) : ThCorr M r := by
  intro V _ _ H t₁ t₂ φ φ' hg₁ hg₂ hR w₁ hw₁ w₂ hw₂ he he'
  obtain ⟨hL, -, hL', -, hι⟩ := hR
  have e1 := mem_iff_of_image_eq φ hL he
  have e2 := mem_iff_of_image_eq φ' hL' he'
  cases hs : M.split with
  | none =>
    exact (lemma0L_holds M r hs V H t₁ hg₁ w₁ hw₁).trans
      ((and_congr e1 e2).trans (lemma0L_holds M r hs V H t₂ hg₂ w₂ hw₂).symm)
  | some g =>
    have hinj : Function.Injective (Prod.map φ' φ) := φ'.injective.prodMap φ.injective
    have e3 := hinj.mem_set_image (s := H.iotaGraph g t₁)
      (a := (H.mkW t₁.f' ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp' H hw₁⟩, H.mkW t₁.f ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp H hw₁⟩))
    rw [hι g hs, Prod.map_apply, he, he'] at e3
    exact (lemma0G_holds M r g hs V H t₁ hg₁ w₁ hw₁).trans
      ((and_congr e1 (and_congr e2 e3.symm)).trans (lemma0G_holds M r g hs V H t₂ hg₂ w₂ hw₂).symm)

end T

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Cut

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def MMo (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V :=
  Submodule.span M.L.O (Set.range (H.MMfam t))

def MMsharp (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V where
  carrier := {u | u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h u m ∈ M.L.O}
  add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun m hm => by
    rw [H.h_add_left]; exact M.L.O.add_mem (ha.2 m hm) (hb.2 m hm)⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun m _ => by rw [H.h_zero_left]; exact M.L.O.zero_mem⟩
  smul_mem' := fun c u hu => ⟨by rw [Subring.smul_def]; exact Submodule.smul_mem _ _ hu.1, fun m hm => by
    rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 (hu.2 m hm)⟩

abbrev DDt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Type :=
  ↥(MMsharp H t) ⧸ (MMo H t).comap (MMsharp H t).subtype

def ddMk (H : HermSp M V) {r : ℕ} (t : Term V M r) (u : ↥(MMsharp H t)) : DDt H t :=
  Submodule.Quotient.mk u

def IsomD (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) : Prop :=
  ∀ (x y : ↥(MMsharp H t₁)) (x₂ y₂ : ↥(MMsharp H t₂)), θ (ddMk H t₁ x) = ddMk H t₂ x₂ →
    θ (ddMk H t₁ y) = ddMk H t₂ y₂ → H.h x₂ y₂ - H.h x y ∈ M.L.O

def Gam (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f) :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)), p = (ddMk H t u, H.mkW t.f ⟨u, hu⟩)}

def Gam' (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f') :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f')), p = (ddMk H t u, H.mkW t.f' ⟨u, hu⟩)}

def GamR (H : HermSp M V) {r : ℕ} (t : Term V M r) (c : E) :
    Set (DDt H t × DDt H t × H.Wb t.f × H.Wb t.f') :=
  {p | ∃ (u u' u'' : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)) (hu' : (u' : V) ∈ H.perp (H.X t.f')),
    (u : V) - u' = c • (u'' : V) ∧
      p = (ddMk H t u, ddMk H t u'', H.mkW t.f ⟨u, hu⟩, H.mkW t.f' ⟨u', hu'⟩)}

def MMInt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Prop :=
  ∀ m ∈ MMo H t, ∀ m' ∈ MMo H t, H.h m m' ∈ M.L.O

def Theta (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Set (DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :=
  {θ | IsUnit (H.Dl t₂.f t₂.f' (r + 1)) ∧ MMInt H t₂ ∧ IsomD H t₁ t₂ θ ∧
    (M.split = none →
      (fun p => (θ p.1, φ p.2)) '' Gam H t₁ = Gam H t₂ ∧ (fun p => (θ p.1, φ' p.2)) '' Gam' H t₁ = Gam' H t₂) ∧
    (∀ g : SplitG M.L, M.split = some g →
      (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
        GamR H t₂ (algebraMap F E (g.q : F)))}

def LocalCountHypotheses (H : HermSp M V) {r : ℕ} (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') : Prop :=
  H.IsGeneric t₁ ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂ t₁.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂' t₁.T' ∧
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ∧
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) ∧
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r))

end Cut

section Props

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def LatSide (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    Nat.card {Λ₂ : Submodule M.L.O V | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
        H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'} =
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ')

def ModSide0 (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = H.ZZplus t₁ →
      Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIso Z₁ Z₂

def ModSideU (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = H.ZZplus t₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = H.ZZplus t₁ a.castSucc (Fin.last r) ∧
        (be₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc (Fin.last r) ∧
        (al₁ a : E) = H.ZZplus t₁ (Fin.last r) a.castSucc ∧
        (al₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' (Fin.last r) a.castSucc) →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂

end Props

end Formalism.L2.SG.LsDatumA
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AaF
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs PI.NRCW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable (D : D7)

abbrev aaF (a : Fin (D.R.rS + 1)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

theorem entry_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G) (hXS : XLam Λ G = XS D G.fl) (hz : G.fl.z ∈ Λ)
    (c b : Fin (D.R.rS + 1)) (hcb : c < b) : ∀ x ∈ aaF D b, x * fmat D G n c b ∈ aaF D c := by
  have hc : c.val < D.R.rS := by have := b.isLt; omega
  have hf : fmat D G n c b = G.fl.coefX (n (frame G b) - frame G b) ⟨c.val, hc⟩ := by
    simp only [fmat, dif_pos hc]
    rw [if_neg (ne_of_lt hcb), zero_add]
  rw [hf]
  have hXSΛ : ∀ v, v ∈ XS D G.fl → v ∈ Λ := by
    intro v hv
    rw [← hXS, XLam, Submodule.mem_inf] at hv
    exact hv.1
  have haF : aaF D c = aaI D ⟨c.val, hc⟩ := rfl
  rw [haF]
  intro x hx
  by_cases hb : b.val < D.R.rS
  · have hfi : frame G b = G.fl.e ⟨b.val, hb⟩ := by
      have h0 := frame_castSucc G ⟨b.val, hb⟩
      rwa [show (⟨b.val, hb⟩ : Fin D.R.rS).castSucc = b from Fin.ext rfl] at h0
    rw [hfi]
    have hxe : x • G.fl.e ⟨b.val, hb⟩ ∈ XS D G.fl := Submodule.subset_span ⟨⟨b.val, hb⟩, x, hx, rfl⟩
    have hn1 : n (x • G.fl.e ⟨b.val, hb⟩) ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨nlam_mem hn (hXSΛ _ hxe), nlam_X hn (Submodule.smul_mem _ x (e_mem_X _ _))⟩
    have hcx := (coefX_of_mem_XS D G.fl hn1).2 ⟨c.val, hc⟩
    have hd : n (G.fl.e ⟨b.val, hb⟩) - G.fl.e ⟨b.val, hb⟩ ∈ G.fl.X :=
      Xa_le_X _ _ ((nlam_frame_mem G hn).1 _)
    have hsplit : n (x • G.fl.e ⟨b.val, hb⟩) =
        x • (G.fl.e ⟨b.val, hb⟩ + (n (G.fl.e ⟨b.val, hb⟩) - G.fl.e ⟨b.val, hb⟩)) := by
      rw [map_smul]; congr 1; abel
    have hne : (⟨b.val, hb⟩ : Fin D.R.rS) ≠ ⟨c.val, hc⟩ := by
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    rw [hsplit, coefX_smul _ (add_mem (e_mem_X _ _) hd), coefX_add _ (e_mem_X _ _) hd, coefX_e, if_neg hne,
      zero_add] at hcx
    exact hcx
  · have hfz : frame G b = G.fl.z := by
      have h0 := frame_last G
      rwa [show Fin.last D.R.rS = b from Fin.ext (by have := b.isLt; simp; omega)] at h0
    rw [hfz]
    have hb0 : aaF D b = 1 := by
      have : (D.R.rS : ℤ) - (b : ℕ) = 0 := by have := b.isLt; push_cast; omega
      simp only [aaF, this, neg_zero, zpow_zero]
    rw [hb0] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
    have hv : n G.fl.z - G.fl.z ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨sub_mem (nlam_mem hn hz) hz, (nlam_frame_mem G hn).2⟩
    have hcx := (coefX_of_mem_XS D G.fl hv).2 ⟨c.val, hc⟩
    rw [← Algebra.smul_def]
    exact fi_smul _ o hcx

end Glob

end Formalism.L2.SG.Pf.FibQ
end
end

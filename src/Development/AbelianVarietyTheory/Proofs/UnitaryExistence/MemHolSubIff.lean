module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
noncomputable section

namespace GlobalTheory.CuspProduct

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem mem_holSub_iff {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    (P : FDSec X) : P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

open Classical in
theorem rdU_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c (f * g) (U.un k ⟨x, h⟩)) else 0) =
    (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) *
      (if h : x ∈ (U.X k).dom then toC (evR Xo c g (U.un k ⟨x, h⟩)) else 0)
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp

theorem laU_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (hn : Even n)
    (hn' : Even n') (k : U.Comp) : laU U (a + a') (n + n') k = laU U a n k + laU U a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  funext τ j
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

theorem cuspMul_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.CuspMul Xo c U := by
  intro E _ _ _ H Dw l Xo c r U a a' n n' f g hd hd' hf hg
  rw [mem_cusp] at hf hg ⊢
  refine ⟨mulC_mem_sec Xo c a a' n n' hf.1 hg.1, fun σ hσ => ?_⟩
  show rdU (U σ) (f * g) ∈ holSub (U σ).X (laU (U σ) (a + a') (n + n'))
  rw [rdU_mul, mem_holSub_iff]
  intro k
  rw [laU_add (U σ) a a' n n' hd.2 hd'.2 k]
  exact (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_iff _ _ _).1 (hf.2 σ hσ) k) _
    ((mem_holSub_iff _ _ _).1 (hg.2 σ hσ) k).1

end GlobalTheory.CuspProduct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFDOfCuspFiniteClaim
noncomputable section

namespace GlobalTheory.CuspFormsCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private lemma zero_mem_SS_unitary_existence {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    (0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) ∈ X.SS la :=
  ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero X la, fun ξ _ x _ => _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero X la ξ x 0⟩

private lemma add_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) (hQ : Q ∈ X.SS la) : P + Q ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add X hP.1 hQ.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add X hP.1 hQ.1 hξ hx 0, hP.2 ξ hξ x hx, hQ.2 ξ hξ x hx, add_zero]

private lemma smul_mem_SS {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (a : ℂ) {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : a • P ∈ X.SS la := by
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul X a hP.1, fun ξ hξ x hx => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul X la P ξ x 0 a, hP.2 ξ hξ x hx, mul_zero]

theorem _root_.GlobalTheory.CuspFormsCompare.mem_holSub_iff_forall_SS {r : ℕ} {Comp : Type}
    (X : Comp → _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : ∀ k, _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r)
    (P : _root_.Formalism.L2.PjFree.FDSec X) : P ∈ _root_.Formalism.L2.PjFree.holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  constructor
  · intro hP
    unfold _root_.Formalism.L2.PjFree.holSub at hP
    induction hP using Submodule.span_induction with
    | mem Q hQ => exact hQ
    | zero => exact fun k => zero_mem_SS_unitary_existence (X k) (la k)
    | add Q R _ _ hQ hR => exact fun k => add_mem_SS (X k) (la k) (hQ k) (hR k)
    | smul a Q _ hQ => exact fun k => smul_mem_SS (X k) (la k) a (hQ k)
  · intro hP
    exact _root_.Formalism.L2.PjFree.holCusp_mem_holSub X la hP

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end GlobalTheory.CuspFormsCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabGroupIsoOfGeneric
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem sab_group_iso_of_generic
    (hx : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G',
      IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (t t' : SAB H (Sp T)) (tK : SAB H (Sp K))
    (m : SABMap tK t (spMap (algebraMap T K))) (m' : SABMap tK t' (spMap (algebraMap T K))) :
    ∃ ψ : t.G ≅ t'.G, IsMonHom ψ.hom ∧ m.φ ≫ ψ.hom.left = m'.φ ∧
      ∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a := by
  have inj : ∀ (s s' : SAB H (Sp T)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' →
      (Over.pullback (spMap (algebraMap T K))).map F = (Over.pullback (spMap (algebraMap T K))).map F' → F = F' := by
    intro s s' F F' hF hF' h
    exact (hx T K s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩
  have A : ∀ {X Y : Over (Sp T)} (a : X ⟶ Y),
      ((Over.pullback (spMap (algebraMap T K))).map a).left ≫ pullback.fst Y.hom _ =
        pullback.fst X.hom _ ≫ a.left := fun a => pullback.lift_fst _ _ _
  obtain ⟨e, he, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback t.G _)
  obtain ⟨e', he', hφ'⟩ := grpPullback_iso m'.cart (isGrpPullback_pullback t'.G _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx T K t.G t'.G t.semi t'.semi (e.inv ≫ e'.hom) inferInstance
  obtain ⟨F', ⟨hF', hFf'⟩, -⟩ := hx T K t'.G t.G t'.semi t.semi (e'.inv ≫ e.hom) inferInstance
  have key : m.cm.F ≫ F.left = m'.cm.F := by
    rw [← hφ, Category.assoc, ← A, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, hφ']
  refine ⟨⟨F, F', inj _ _ _ _ inferInstance inferInstance ?_, inj _ _ _ _ inferInstance inferInstance ?_⟩, hF, key,
    fun a => ?_⟩
  · rw [Functor.map_comp, hFf, hFf']; simp
  · rw [Functor.map_comp, hFf, hFf']; simp
  · show t.act.act a ≫ F = F ≫ t'.act.act a
    have := t.act.hom a
    have := t'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [← cancel_epi e.hom]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, A]
      rw [reassoc_of% hφ, reassoc_of% hφ, ← reassoc_of% m.act a, reassoc_of% key, key, m'.act]
    · exact (Over.w _).trans (Over.w _).symm

end GlobalTheory
end

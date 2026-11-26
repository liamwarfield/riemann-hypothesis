module

public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypTwA
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypEvChain
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLat
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypChi
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ValIntN
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockRowSubstitutionPreservesComplexSpan

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypForms
noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem isTr_inv_mul (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (γ1 γ2 : GL (Fin n) E)
    (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J) (z : Formalism.L2.Forms.Frames (gramC J emb)) :
    IsTr (atInf emb ((γ1⁻¹ * γ2 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (frameTranslate emb hc γ2⁻¹ ((UJ _ _).inv_mem h2) z) (frameTranslate emb hc γ1⁻¹ ((UJ _ _).inv_mem h1) z) := by
  intro τ
  show atInf emb ((γ1⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ =
    atInf emb ((γ1⁻¹ * γ2 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
      (atInf emb ((γ2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ)
  rw [← Matrix.mul_assoc]
  congr 1
  simp only [atInf]
  rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]

def LawAt (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 →
    ∀ y y' : Formalism.L2.Forms.Frames (gramC J emb), IsTr (atInf emb γ) y' y → v y = (S.chi κ : ℂ) * v y'

theorem law_wd (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) (hv : LawAt S emb y0 v)
    (γ1 γ2 : GL (Fin n) E) (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J) (κ1 κ2 : S.U)
    (e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * y0.1 * κ2.1) (z : Formalism.L2.Forms.Frames (gramC J emb)) :
    (S.chi κ1 : ℂ) * v (frameTranslate emb hc γ1⁻¹ ((UJ _ _).inv_mem h1) z) =
      (S.chi κ2 : ℂ) * v (frameTranslate emb hc γ2⁻¹ ((UJ _ _).inv_mem h2) z) := by
  have e0 : y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ1⁻¹ * γ2) * y0.1 * (κ2 * κ1⁻¹ : S.U).1 := by
    have e' : y0.1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1)⁻¹ *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1) * κ1.1⁻¹ := by group
    rw [e] at e'
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc y0.1 = _ := e'
      _ = _ := by group
  rw [hv (γ1⁻¹ * γ2) ((UJ _ _).mul_mem ((UJ _ _).inv_mem h1) h2) (κ2 * κ1⁻¹) e0 _ _ (isTr_inv_mul emb hc γ1 γ2 h1 h2 z),
    map_mul, map_inv, Units.val_mul, ← mul_assoc, ← mul_assoc, mul_comm (S.chi κ1 : ℂ), mul_assoc (S.chi κ2 : ℂ), mul_comm ((S.chi κ1 : ℂˣ) : ℂ),
    Units.inv_mul, mul_one]


open Classical in
theorem exists_form_of_law (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (lam : ι → DomWeight n) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ)
    (hV : v ∈ ValC (gramC J emb) lam) (hv : LawAt S emb y0 v) : ∃ g ∈ AdForms S emb lam, g y0 = v := by
  let Pd : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Prop := fun x =>
    ∃ q : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) q.1.1 * y0.1 * q.2.1
  let g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Formalism.L2.Forms.Frames (gramC J emb) → ℂ := fun x y =>
    if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0
  have gval : ∀ x (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U),
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 → ∀ y,
      g x y = (S.chi κ : ℂ) * v (frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y) := by
    intro x γ hγ κ e y
    have h : Pd x := ⟨(⟨γ, hγ⟩, κ), e⟩
    show (if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0) = _
    rw [dite_eq_left h]
    exact law_wd S emb hc y0 v hv _ _ h.choose.1.2 hγ _ _ (h.choose_spec.symm.trans e) y
  have gzero : ∀ x, ¬ Pd x → ∀ y, g x y = 0 := by
    intro x h y
    show (if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0) = _
    rw [dite_eq_right h]
  refine ⟨g, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · intro γ' hγ' x x' κ' hx' y y' hy
    by_cases hP : Pd x
    · obtain ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩ := hP
      have e' : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ' * γ) * y0.1 * (κ * κ' : S.U).1 := by
        rw [hx', e, map_mul, Subgroup.coe_mul]; group
      rw [gval x γ hγ κ e, gval x' (γ' * γ) ((UJ _ _).mul_mem hγ' hγ) (κ * κ') e']
      have hfr : frameTranslate emb hc (γ' * γ)⁻¹ ((UJ _ _).inv_mem ((UJ _ _).mul_mem hγ' hγ)) y =
          frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y' := by
        apply Subtype.ext
        funext τ
        show atInf emb (((γ' * γ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ =
          atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y'.1 τ
        rw [hy τ, _root_.mul_inv_rev]
        simp only [atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
        congr 1
        rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
      rw [hfr, map_mul, Units.val_mul]
      ring
    · have hP' : ¬ Pd x' := by
        rintro ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩
        refine hP ⟨(⟨γ'⁻¹ * γ, (UJ _ _).mul_mem ((UJ _ _).inv_mem hγ') hγ⟩, κ * κ'⁻¹), ?_⟩
        show x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ'⁻¹ * γ) * y0.1 * (κ * κ'⁻¹ : S.U).1
        have e1 : x.1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ')⁻¹ * x'.1 * κ'.1⁻¹ := by
          rw [hx']; group
        rw [e1, e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [gzero x hP, gzero x' hP', mul_zero]
  · refine Submodule.mem_pi.2 fun x _ => ?_
    by_cases hP : Pd x
    · obtain ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩ := hP
      have : g x = (S.chi κ : ℂ) • fun y => v (frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y) := by
        funext y
        exact gval x γ hγ κ e y
      rw [this]
      exact Submodule.smul_mem _ _ (valuation_class_translate_mem emb hc lam _ _ hV)
    · have : g x = 0 := by
        funext y
        exact gzero x hP y
      rw [this]
      exact Submodule.zero_mem _
  · funext y
    rw [gval y0 1 (UJ _ _).one_mem 1 (by rw [map_one]; simp)]
    have hfr : frameTranslate emb hc (1 : GL (Fin n) E)⁻¹ ((UJ _ _).inv_mem (UJ (σ : E →+* E) J).one_mem) y = y := by
      apply Subtype.ext
      funext τ
      show atInf emb (((1 : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = y.1 τ
      rw [inv_one]
      simp [atInf]
    rw [hfr, map_one, Units.val_one, one_mul]

end Gen

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem formsOnClassOf (S : StepIn M i hi G) : FormsOnClassOf S := by
  intro β c v hv
  obtain ⟨g, hg, e⟩ := exists_form_of_law (S.K β).lev (embT D) (embedding_conj_compat D) (lamTG M i) ((S.K β).y c) v hv.1 hv.2
  exact Submodule.mem_map.2 ⟨res (embT D) (S.K β).y g, Submodule.mem_map.2 ⟨g, hg, rfl⟩, e⟩

end Formalism.MainNotions.G.ChF

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypFin
noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.KAat

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} {S : StepIn M i hi G} {e : D.what₂.LL →+* G.Kf}


open Classical in
theorem finClasses_of (H : ∀ β, S.Core e β) (X : ChX S) : G.FinClasses := by
  intro a
  refine ⟨((Finset.univ : Finset (C.cls i)).filter fun c => ∃ L, G.P.IsLatTup L ∧ clsOf H a L = c).attach.image
    (fun c => ((Finset.mem_filter.1 c.2).2).choose), ?_, ?_⟩
  · intro L hL
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hL
    exact ((Finset.mem_filter.1 c.2).2).choose_spec.1
  · intro L hL
    have hc : clsOf H a L ∈ (Finset.univ : Finset (C.cls i)).filter fun c => ∃ L, G.P.IsLatTup L ∧ clsOf H a L = c :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, L, hL, rfl⟩
    refine ⟨_, Finset.mem_image.2 ⟨⟨clsOf H a L, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have spec := ((Finset.mem_filter.1 hc).2).choose_spec
    obtain ⟨_, γ, hγ⟩ := (clsOf_iff H X a a _ L spec.1 hL).1 spec.2
    exact ⟨γ, hγ⟩

end Formalism.MainNotions.G.ChF

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypVinRec
noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PValIntN

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {j : ℕ}
  (hj : j + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

structure LatTies (w : D.what₂.places.Pl) (Fo : FormsIn M (j + 1) hj) (β : Fo.Ch)
    (Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (j + 1)).rank → D.host.E)) : Prop where
  siteGood_prime_torsion : ¬ D.what₂.places.resChar w ∣ Fo.T
  Lb_eq : (Fo.K β).lev.Lb = reL (rankN D (j + 1) hj) Lb
  lat : ∀ cl : {c // Fo.chOf c = β}, Submodule.IsFullLattice D.host.E (Fo.lat cl.1)
  chi : ∀ κ : (Fo.K β).lev.U, ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧
    D.what₂.embLL r = ((Fo.K β).lev.chi κ : ℂ)


set_option maxHeartbeats 8000000 in
theorem latIn_of {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X u w hg Lv j Fo.Ch}
    {pos : (Σ v : Fin (Fl.Pj (j + 1)).nV, Fin ((Fl.Pj (j + 1)).n' v)) ≃ D.what₂.Tau} {β : Fo.Ch}
    (hfr : FrRatJ (Lc.t β) Lc.B) (H : LatTies hj w Fo β (Lc.Lb β)) : LatIn (stepInOf hj Fo Lc pos) w β :=
  { prime := hg.1
    resChar := rfl
    siteGood_prime_torsion := H.siteGood_prime_torsion
    alg := fun v a => (X.g u w hg).spl_alg _ ((X.g u w hg).pl v).2 a
    base := fun v t => frlat_re (rankN D (j + 1) hj) ((X.g u w hg).pl v).1 ((X.g u w hg).spl _ ((X.g u w hg).pl v).2) (Lc.Lb β)
      Lc.B ((Lc.t β).fr _ ((X.g u w hg).pl v).2) (hfr _ _) ((Lc.t β).fr_lat _ ((X.g u w hg).pl v).2) (Fo.K β).lev.Lb H.Lb_eq t
    lat := H.lat
    chi := H.chi }


set_option maxHeartbeats 8000000 in
theorem valIntN_rec {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X u w hg Lv j Fo.Ch}
    {pos : (Σ v : Fin (Fl.Pj (j + 1)).nV, Fin ((Fl.Pj (j + 1)).n' v)) ≃ D.what₂.Tau} (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    (HT : ∀ β, LocTies hj Fo Lc pos e β) (hS : BlockRationalityField) (hfrac : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf))
    (HL : ∀ β, LatTies hj w Fo β (Lc.Lb β)) : (stepInOf hj Fo Lc pos).ValIntN e w :=
  valIntN_of (stepInOf hj Fo Lc pos) e w (fun β => core_of hj (HT β)) hS hfrac hR0
    (fun β => latIn_of hj (HT β).frRat (HL β))

end Formalism.MainNotions.G.CmpJ.PValIntN

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.IntWOfPow
noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PValIntN
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {p : ℕ} {G : GAtP p}

theorem epsU_val (B B' γ : GL (Fin n) E) (k : ℕ) :
    ((epsU B B' γ k : Eˣ) : E) = (B'.1.det * (B.1.det)⁻¹) ^ k * (γ.1.det)⁻¹ := by
  simp [epsU]

theorem det_cT (τ : E →+* E) (M : Matrix (Fin n) (Fin n) E) : (cT τ M).det = τ M.det := by
  unfold cT
  rw [Matrix.det_transpose]
  exact (RingHom.map_det τ M).symm

theorem epsU_conj (hJ : IsUnit J.det) (B B' γ : GL (Fin n) E) (k : ℕ) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (hB : cT (σ : E →+* E) B.1 * J * B.1 = 1) :
    σ (epsU B B' γ k : Eˣ) * (epsU B B' γ k : Eˣ) = ((cT (σ : E →+* E) B'.1 * J * B'.1).det) ^ k := _root_.GlobalTheory.HP.epsU_conj hJ B B' γ k hγ hB


set_option maxHeartbeats 2000000 in
theorem epsU_iw (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (hW : LocInt A) (hp : p.Prime) (hT : ¬ p ∣ T)
    (halg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (hb : ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 S.Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, (((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)).mulVec t a ∈ (A.pl v).1.adicCompletionIntegers F)
    (hJ : IsUnit J.det) (hB : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1)
    (Lc : Submodule (𝓞 E) (Fin n → E)) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B')
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U) (b k : ℕ)
    (h : y.1 ^ (b + k) = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y.1 ^ b * κ.1) (v : Fin G.P.nV) :
    (A.iw v (epsU A.B B' γ k : Eˣ) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range ∧
      A.iw v (σ (epsU A.B B' γ k : Eˣ)) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range) ∧
    (A.iw v ((epsU A.B B' γ k : Eˣ) : E)⁻¹ ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range ∧
      A.iw v (σ ((epsU A.B B' γ k : Eˣ) : E)⁻¹) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range) := by
  have key : ∀ x : E, A.phE v x ∈ (A.pl v).1.adicCompletionIntegers F → A.iw v x ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    intro x hx
    refine (hW v _).2 ?_
    have e : A.eQ v (A.iw v x) = A.phE v x := (A.eQ v).apply_symm_apply _
    rw [e]
    exact hx
  obtain ⟨h1, h2⟩ := epsU_ph S A hp hT halg hb Lc y hy hle B' hB' γ κ b k h v
  have e1 : A.iw v (epsU A.B B' γ k : Eˣ) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := key _ h1
  have e2 : A.iw v ((epsU A.B B' γ k : Eˣ) : E)⁻¹ ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    refine key _ ?_
    rw [← map_inv, Units.coe_map] at h2
    rw [← Units.val_inv_eq_inv_val]
    exact h2
  have hg := gramW_gen S A hW hp hT halg hJ Lc y hy hle B' hB' v
  have g1 : A.iw v (cT (σ : E →+* E) B'.1 * J * B'.1).det ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    rw [RingHom.map_det]
    exact det_mem_sub _ _ fun a b => (hg a b).1
  have g2 : A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1).det)⁻¹ ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    have e : ((cT (σ : E →+* E) B'.1 * J * B'.1).det)⁻¹ = ((cT (σ : E →+* E) B'.1 * J * B'.1)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e, RingHom.map_det]
    exact det_mem_sub _ _ fun a b => (hg a b).2
  have hc := epsU_conj hJ A.B B' γ k hγ hB
  have h0 : ((epsU A.B B' γ k : Eˣ) : E) ≠ 0 := Units.ne_zero _
  have c1 : σ (epsU A.B B' γ k : Eˣ) = ((cT (σ : E →+* E) B'.1 * J * B'.1).det) ^ k * ((epsU A.B B' γ k : Eˣ) : E)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ h0).2 hc
  refine ⟨⟨e1, ?_⟩, e2, ?_⟩
  · rw [c1, map_mul, map_pow]
    exact Subring.mul_mem _ (Subring.pow_mem _ g1 k) e2
  · rw [map_inv₀, c1, mul_inv, inv_inv, ← inv_pow, map_mul, map_pow]
    exact Subring.mul_mem _ (Subring.pow_mem _ g2 k) e1

end Gen

theorem zpow_calc {K : Type} [Field K] (a b : K) (c : ℤ) (k : ℕ) :
    (a ^ (-c)) ^ k * ((b⁻¹) ^ (-c)) ^ k = ((b * a⁻¹) ^ k) ^ c := by
  rw [_root_.inv_zpow', neg_neg, _root_.zpow_neg, ← _root_.inv_zpow, ← mul_pow, ← mul_zpow, mul_comm a⁻¹ b, ← zpow_natCast, ← _root_.zpow_mul,
    mul_comm c, _root_.zpow_mul, zpow_natCast]

variable {D : D7}

theorem intW_of_pow (w : D.what₂.places.Pl) (r : D.what₂.LL) (k : ℕ) (hk : 0 < k) (h1 : r ^ k ∈ intW D.what₂.places w)
    (h2 : (r ^ k)⁻¹ ∈ intW D.what₂.places w) : r ∈ intW D.what₂.places w ∧ r⁻¹ ∈ intW D.what₂.places w := _root_.GlobalTheory.HP.intW_of_pow w r k hk h1 h2

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}


set_option maxHeartbeats 4000000 in
theorem exists_pow (S : StepIn M i hi G) (β : S.Ch) (cl : {c // S.chOf c = β}) :
    ∃ (b k : ℕ), 0 < k ∧ ∃ (g κ : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ∧
      g.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ ∧ κ.1 ∈ (S.K β).lev.U ∧
      (S.K β).y cl ^ (b + k) = g * (S.K β).y cl ^ b * κ := by
  have hfin : Finite (Cls (S.K β).lev) := Finite.of_surjective _ (S.K β).y_bij.2
  obtain ⟨a, b, hab, he⟩ := @Finite.exists_ne_map_eq_of_infinite ℕ (Cls (S.K β).lev) _ hfin
    (fun n : ℕ => (Quotient.mk'' ((S.K β).y cl ^ n) : Cls (S.K β).lev))
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm he.symm (by omega)
  obtain ⟨g, hg, κ, hκ, e⟩ := (@DoubleCoset.eq _ _ _ _ ((S.K β).y cl ^ a) ((S.K β).y cl ^ b)).1 he
  obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_subgroupOf.1 hg
  refine ⟨a, b - a, by omega, g, κ, γ, hγ, hγe.symm, Subgroup.mem_subgroupOf.1 hκ, ?_⟩
  rw [show a + (b - a) = b by omega]
  exact e


set_option maxHeartbeats 4000000 in
theorem twUnit_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) (β : S.Ch) (H : S.Core e β)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (L : LatIn S w β) : S.TwUnit w β := by
  intro cl B' hB'
  have hpw := L.resChar
  subst hpw
  obtain ⟨b, k, hk, g, κ, γ, hγ, hg, hκ, hpow⟩ := exists_pow S β cl
  have hσσ : ∀ x : D.host.E, sigD D (sigD D x) = x := fun x => by
    rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.host_conj_involutive]
  have hpow' : ((S.K β).y cl).1 ^ (b + k) =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y cl).1 ^ b * (⟨κ.1, hκ⟩ : (S.K β).lev.U).1 := by
    have := congrArg Subtype.val hpow
    rw [← hg]
    exact this
  have hiw := epsU_iw (S.K β).lev (S.loc β) H.int L.prime L.siteGood_prime_torsion L.alg L.base (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) H.std
    (S.lat cl.1) ((S.K β).y cl) ((S.K β).y_lat cl) (le_dual_chart (S.K β) cl) B' hB' γ hγ ⟨κ.1, hκ⟩ b k hpow'
  set ε : D.host.E := ((epsU (S.loc β).B B' γ k : D.host.Eˣ) : D.host.E) with hε

  have hint : ∀ x : D.host.E, (∀ v, (S.loc β).iw v x ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range ∧
      (S.loc β).iw v (sigD D x) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range) → ∀ τ, tEL D τ x ∈ intW D.what₂.places w := by
    intro x hx τ
    obtain ⟨⟨v, s⟩, rfl⟩ := S.pos.surjective τ
    rw [hR0]
    by_cases hs : Even s.val
    · have h1 := H.pos_emb v s x
      rw [if_pos hs] at h1
      rw [h1]
      exact rho_int v s.val _ (hx v).1
    · have h1 := H.pos_emb v s (sigD D x)
      rw [if_neg hs, hσσ] at h1
      rw [h1]
      exact rho_int v s.val _ (hx v).2
  have i1 : ∀ τ, tEL D τ ε ∈ intW D.what₂.places w := hint ε fun v => (hiw v).1
  have i2 : ∀ τ, (tEL D τ ε)⁻¹ ∈ intW D.what₂.places w := fun τ => by
    rw [← map_inv₀]
    exact hint ε⁻¹ (fun v => (hiw v).2) τ
  have i3 : ∀ τ, D.what₂.embLL (tEL D τ ε) ∈ unitsW D w := fun τ => ⟨_, i1 τ, i2 τ, rfl⟩

  obtain ⟨rc, hrc⟩ := H.chRat cl
  set r : D.what₂.LL := (∏ τ, (tEL D τ (S.loc β).B.1.det) ^ (-(cTw D i))) * rc *
    ∏ τ, (tEL D τ ((B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1.det)) ^ (-(cTw D i)) with hr
  have hrs : D.what₂.embLL r = S.sTw β cl B' := by
    rw [hr, map_mul, map_mul, map_prod, map_prod, hrc]
    unfold StepIn.sTw StepIn.kTw
    congr 1
    · congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, tEL_emb]
    · refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, tEL_emb]
      congr 1
      exact RingHom.map_det (embT D τ) _

  have hch : (((S.tw β).ch ((S.K β).y cl) : ℂˣ) : ℂ) ^ k * ∏ τ, (embT D τ γ.1.det) ^ (cTw D i) = 1 := by
    have h1 := congrArg (S.tw β).ch hpow
    rw [map_mul, map_mul, map_pow, map_pow, (S.tw β).ch_U κ hκ, mul_one, pow_add, mul_comm] at h1
    have h2 : (S.tw β).ch ((S.K β).y cl) ^ k = (S.tw β).ch g := mul_right_cancel h1
    have h3 := (S.tw β).ch_rat γ hγ g hg
    rw [← h2, Units.val_pow_eq_pow_val] at h3
    exact h3
  have hdet : ((B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1.det) = (B'.1.det)⁻¹ := by
    have := congrArg Units.val (map_inv Matrix.GeneralLinearGroup.det B')
    rw [Units.val_inv_eq_inv_val] at this
    exact this
  have hpw : D.what₂.embLL (r ^ k) = ∏ τ, (D.what₂.embLL (tEL D τ ε)) ^ (cTw D i) := by
    have hP0 : (∏ τ, (embT D τ γ.1.det) ^ (cTw D i)) ≠ 0 := right_ne_zero_of_mul_eq_one hch
    have hchk : (((S.tw β).ch ((S.K β).y cl) : ℂˣ) : ℂ) ^ k = (∏ τ, (embT D τ γ.1.det) ^ (cTw D i))⁻¹ :=
      eq_inv_of_mul_eq_one_left hch
    rw [map_pow, hr, map_mul, map_mul, map_prod, map_prod, hrc, mul_pow, mul_pow, hchk, ← Finset.prod_pow, ← Finset.prod_pow,
      mul_right_comm, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, map_zpow₀, tEL_emb, tEL_emb, tEL_emb, hdet, map_inv₀, zpow_calc, hε, epsU_val, map_mul, map_pow, map_mul, map_inv₀,
      map_inv₀, mul_zpow, _root_.inv_zpow]
  have hU : D.what₂.embLL (r ^ k) ∈ unitsW D w := by
    rw [hpw]
    refine Submonoid.prod_mem _ fun τ _ => ?_
    rcases Int.eq_nat_or_neg (cTw D i) with ⟨m, hm | hm⟩
    · rw [hm, zpow_natCast]
      exact Submonoid.pow_mem _ (i3 τ) m
    · rw [hm, _root_.zpow_neg, zpow_natCast]
      exact unitsW_inv (Submonoid.pow_mem _ (i3 τ) m)
  obtain ⟨r', hr1, hr2, hr3⟩ := hU
  have hrr : r' = r ^ k := D.what₂.embLL.injective hr3
  rw [hrr] at hr1 hr2
  obtain ⟨a1, a2⟩ := intW_of_pow w r k hk hr1 hr2
  exact ⟨r, a1, a2, hrs⟩

end Formalism.MainNotions.G.ChF

end
end

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ.PValIntN Formalism.MainNotions.G.CmpJ.PInvLe
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

section Step

variable {j : ℕ} (hj : j + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}


set_option maxHeartbeats 2000000 in
structure StepTies (Fo : FormsIn M (j + 1) hj) (Lc : LocIn X0 u w h Lv j Fo.Ch) (Gt : GatTies D) (c : LatCmp D) : Prop where

  frRat : ∀ β, FrRatJ (Lc.t β) Lc.B

  sameU : ∀ β, SameUlocJ hj (Fo.K β).lev (Lc.Uloc β)

  hypT : ∀ β, HypTJ (Lc.t β)

  bad_p : ∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal

  std : cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (j + 1) hj) D.host.E Lc.B).1 * gramN D (j + 1) hj *
    (reGL (rankN D (j + 1) hj) D.host.E Lc.B).1 = 1

  psi : ∀ β, UnitCharacterChartCompatibility hj (Fo.K β).lev (c.embW u w h) (Lc.ψ β)

  chRat : ∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)

  hypC : ∀ β, HypTJC (Lc.t β)

  ok : Fo.okW w

  siteGood_prime_torsion : ¬ D.what₂.places.resChar w ∣ Fo.T

  Lb_eq : ∀ β, (Fo.K β).lev.Lb = reL (rankN D (j + 1) hj) (Lc.Lb β)

variable {hj} {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}
  {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X0 u w h Lv j Fo.Ch}

theorem StepTies.chi (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) (κ : (Fo.K β).lev.U) :
    ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧ D.what₂.embLL r = ((Fo.K β).lev.chi κ : ℂ) :=
  chiUnit_of hj (Fo.K β).lev (S.sameU β) (c.embW u w h) (S.psi β) S.bad_p (fun x => c.embW_int u w h x) κ


set_option maxHeartbeats 4000000 in
theorem StepTies.ties (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) : LocTiesR hj Fo Lc (c.embW u w h) β :=
  { frRat := S.frRat β
    sameU := S.sameU β
    hypT := S.hypT β
    bad_p := S.bad_p
    std := S.std
    psi := S.psi β
    chiRat := fun κ => let ⟨r, _, _, hr⟩ := S.chi β κ; ⟨r, hr⟩
    chRat := S.chRat β }

theorem StepTies.lat (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) : LatTies hj w Fo β (Lc.Lb β) :=
  { siteGood_prime_torsion := S.siteGood_prime_torsion
    Lb_eq := S.Lb_eq β
    lat := fun cl => isLattice_chart (Fo.K β) cl
    chi := S.chi β }

theorem StepTies.core (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) (β : Fo.Ch) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).Core (c.embW u w h) β :=
  core_of_R hj K ht hF (S.ties β)

theorem StepTies.valIntN (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).ValIntN (c.embW u w h) w := by
  have ties (β : Fo.Ch) : LocTies hj Fo Lc (Gt.gat_pos u w h) (c.embW u w h) β :=
    { frRat := S.frRat β
      sameU := S.sameU β
      hypT := S.hypT β
      bad_p := S.bad_p
      std := S.std
      pos_emb := fun v s x => locJ_pos_emb hj (Lc.t β) Lc.B K v s x
      wt := StepIn.wt_of (M := M) Gt w h Lv ht hF j hj (stepInOf hj Fo Lc (Gt.gat_pos u w h)) rfl β
      psi := S.psi β
      chiRat := (S.ties β).chiRat
      chRat := S.chRat β }
  exact valIntN_rec hj (c.embW u w h) ties Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
    ((D.gat u w h).P.setting (plc Gt u w h)).frac_O (fun x => c.embW_int u w h x) S.lat

theorem StepTies.twUnit (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) (β : Fo.Ch) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).TwUnit w β := by
  have lat : LatIn (stepInOf hj Fo Lc (Gt.gat_pos u w h)) w β :=
    { prime := h.1
      resChar := rfl
      siteGood_prime_torsion := S.siteGood_prime_torsion
      alg := fun v a => (X0.g u w h).spl_alg _ ((X0.g u w h).pl v).2 a
      base := fun v t =>
        Formalism.L2.G.RelativeIndexFlags.frlat_re (rankN D (j + 1) hj) ((X0.g u w h).pl v).1
          ((X0.g u w h).spl _ ((X0.g u w h).pl v).2) (Lc.Lb β) Lc.B
          ((Lc.t β).fr _ ((X0.g u w h).pl v).2) (S.frRat β _ _) ((Lc.t β).fr_lat _ ((X0.g u w h).pl v).2)
          (Fo.K β).lev.Lb (S.Lb_eq β) t
      lat := (S.lat β).lat
      chi := S.chi β }
  exact twUnit_of (stepInOf hj Fo Lc (Gt.gat_pos u w h)) (c.embW u w h) w β (S.core K ht hF β)
    (fun x => c.embW_int u w h x) lat

theorem StepTies.chX (S : StepTies hj Fo Lc Gt c) : ChX (stepInOf hj Fo Lc (Gt.gat_pos u w h)) := by
  have charts : ChX (stepInOf hj Fo Lc (Gt.gat_pos u w h)) := by
    refine { hypC := ?_, inj := ?_, onto := ?_, cinj := ?_ }
    all_goals
      intro β
      let : Fintype (Lc.cmpt β) := Lc.fin β
    · exact locHypC_locJ hj (Lc.t β) Lc.B (Fo.K β).lev (S.sameU β) (S.frRat β) (S.hypC β)
    · exact fun a => gamI_inj_locJ hj (Lc.t β) Lc.B a
    · exact fun a => gamOnto_locJ hj (Lc.t β) Lc.B (Fo.K β).lev (S.sameU β) a
    · exact compInj_locJ hj (Lc.t β) Lc.B (Fo.K β).lev (S.sameU β)
  exact charts

end Step

structure HypTiesI (X0 : Formalism.L2.Herm.Herm0 D) (I : CmpJIn Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where

  fl_t : Fl.t = D.R.t

  fill : FillTie Gt u w h Fl

  step : ∀ j hj, ∃ (Fo : FormsIn (I.at' j hj).M (j + 1) hj) (Lc : LocIn X0 u w h Lv j Fo.Ch),
    (I.at' j hj).st = stepInOf hj Fo Lc (Gt.gat_pos u w h) ∧ StepTies hj Fo Lc Gt c

variable {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}

theorem HypTiesI.chX {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) : ChX (I.at' j hj).st := by
  obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
  rw [e]
  exact S.chX

theorem HypTiesI.core {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    ∀ β, (I.at' j hj).st.Core (c.embW u w h) β := by
  obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
  rw [e]
  exact S.core K A.fl_t A.fill

theorem HypTiesI.fin {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    (gatJ Lv (j + 1)).FinClasses :=
  finClasses_of (S := (I.at' j hj).st) (A.core K j hj) (A.chX j hj)

theorem HypTiesI.hyp {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) : CmpJHyp c I :=
  cmpJHyp_of_two c Gt Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
    (A.core K)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.ok)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.twUnit K A.fl_t A.fill)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.valIntN K A.fl_t A.fill)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact iwF_of hj Fo Lc (Gt.gat_pos u w h))
    (A.fin K) A.chX
    (fun j hj => formsOnClassOf _)
    (fun j hj => Formalism.MainNotions.G.CmpJ.PEvValChain.cmpLiftOf_holds _ _)

structure HypTies (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where
  fl_t : Fl.t = D.R.t
  fill : FillTie Gt u w h Fl
  step : ∀ j hj, StepTies hj (Z.Fo j hj) (Z.Lc j hj) Gt c

theorem HypTies.toI {Z : AtIn X0 Tw u μ w h Lv} (A : HypTies Z Gt c) : HypTiesI X0 (Z.I Gt) Gt c :=
  { fl_t := A.fl_t
    fill := A.fill
    step := fun j hj => ⟨Z.Fo j hj, Z.Lc j hj, rfl, A.step j hj⟩ }

theorem HypTies.hyp {Z : AtIn X0 Tw u μ w h Lv} (A : HypTies Z Gt c) (K : CmpTied D X0 T Gt c) : CmpJHyp c (Z.I Gt) := A.toI.hyp K

theorem HypTies.atHyp {Z : AtIn X0 Tw u μ w h Lv} (A : HypTies Z Gt c) (K : CmpTied D X0 T Gt c) : AtHyp Z Gt c :=
  { fl_t := A.fl_t
    fill := A.fill
    ties := fun j hj => (A.step j hj).ties
    hypC := fun j hj => (A.step j hj).hypC
    ok := fun j hj => (A.step j hj).ok
    twUnit := fun j hj => (A.step j hj).twUnit K A.fl_t A.fill
    valIntN := fun j hj => (A.step j hj).valIntN K A.fl_t A.fill
    fin := A.toI.fin K
    card := (A.hyp K).card }

section Fam

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}

end Fam

end Formalism.MainNotions.G.ChF

end

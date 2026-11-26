module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FieldVA

variable {X : Scheme.{0}}

theorem nonzeroLocus_pullPow (L : LB X) (N : ℕ) (t : (lbPow L N).Sec) :
    nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 X) t) = nonzeroLocus t := by
  apply le_antisymm
  · refine iSup_le fun j y hy => ?_
    have hy' : y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _ (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) j)).hom
        (t.f (fun _ => j 0))) := hy
    rw [Scheme.basicOpen_appLE] at hy'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, hy'.2⟩
  · refine iSup_le fun j y hy => ?_
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j PUnit.unit, ?_⟩
    have hc : y ∈ (lbPow L N).U j := X.basicOpen_le (t.f j) hy
    show y ∈ X.basicOpen ((Scheme.Hom.appLE (𝟙 X) _ _
      (GlobalTheory.ZH.CrdMove.pow_chart_le L N (𝟙 X) (fun _ => j PUnit.unit))).hom (t.f (fun _ => j PUnit.unit)))
    rw [Scheme.basicOpen_appLE]
    exact ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc PUnit.unit, hy⟩

end GlobalTheory.Mum.FieldVA

namespace GlobalTheory.Mum


open GlobalTheory.Mum.FieldVA in
theorem veryAmpleAlong_field (hA : AmpleSt) (K : Type) [Field K] (P : PolAV (Sp K)) :
    ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  obtain ⟨m, t, hcov, hs⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow hA K P 4 le_rfl
  have hb : ∀ i, nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) :=
    fun i => nonzeroLocus_pullPow P.L 4 (t i)
  refine ⟨m, fun i => GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i), ?_, fun i => ?_⟩
  · refine _root_.top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y ∈ ⨆ i ∈ Set.univ, nonzeroLocus (t i) by rw [hcov]; trivial)
    obtain ⟨_, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, show y ∈ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) by
      rw [hb]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i (Set.mem_univ i)
  have hW : (𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i)) = nonzeroLocus (t i) := by
    rw [← hb i]; exact le_antisymm (fun y hy => hy) (fun y hy => hy)
  have le1 := hW.le
  have le2 := hW.ge
  have hconst : ∀ a, resG P.A.left le1 (constFn P.A.hom (nonzeroLocus (t i)) a) =
      AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := by
    intro a
    have h2 : constFn P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a =
        AbLaw.cst P.A.hom ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))) a := rfl
    refine (fn_ext fun x hx => ?_).trans h2
    rw [gs_res _ x le1 hx, gs_constFn _ _ _ _ (le1 hx), gs_constFn _ _ _ _ hx]
  refine ⟨by rw [hW]; exact haff, fun j => resG P.A.left le1 (r j), fun j c a ha hc => ?_, ?_⟩
  · have hc' : a ∈ (lbPow P.L 4).U (fun _ => c 0) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hc 0
    have key : ∀ s : (lbPow P.L 4).Sec, secGerm (𝟙 P.A.left) a (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) s) c =
        gs (𝟙 P.A.left) a ((lbPow P.L 4).U (fun _ => c 0)) (s.f (fun _ => c 0)) := fun s =>
      (gs_appLE (𝟙 P.A.left) _ _ _ (𝟙 P.A.left) a hc _).trans
        (congrArg (fun q => gs q a _ (s.f (fun _ => c 0))) (Category.id_comp _))
    have hm : (𝟙 P.A.left) a ∈ nonzeroLocus (t i) ⊓ (lbPow P.L 4).U (fun _ => c 0) := ⟨le1 ha, hc'⟩
    have e := congrArg (gs (𝟙 P.A.left) a _) (hr j (fun _ => c 0))
    rw [gs_res _ a _ hm, gs_mul _ a _ hm, gs_res _ a _ hm, gs_res _ a _ hm] at e
    rw [key, key, gs_res _ a le1 ha]
    exact e
  · have hρ : ∀ f, resG P.A.left le1 (resG P.A.left le2 f) = f := fun f => fn_ext fun x hx => by
      rw [gs_res _ x le1 hx, gs_res _ x le2 (le1 hx)]
    have hcl : Subring.closure (Set.range (constFn P.A.hom (nonzeroLocus (t i))) ∪ Set.range r) ≤
        (MvPolynomial.eval₂Hom (AbLaw.cst P.A.hom
          ((𝟙 P.A.left) ⁻¹ᵁ nonzeroLocus (GlobalTheory.ZH.CrdMove.pullPow (𝟙 P.A.left) (t i))))
          (fun j => resG P.A.left le1 (r j))).range.comap (resG P.A.left le1) := by
      refine Subring.closure_le.2 ?_
      rintro g (⟨a, rfl⟩ | ⟨j, rfl⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.C a, by
          rw [MvPolynomial.eval₂Hom_C]; exact (hconst a).symm⟩)
      · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨MvPolynomial.X j, by rw [MvPolynomial.eval₂Hom_X']⟩)
    intro f
    obtain ⟨p, hp⟩ := RingHom.mem_range.1 (Subring.mem_comap.1
      (hcl (hsurj ▸ Subring.mem_top (resG P.A.left le2 f))))
    exact ⟨p, hp.trans (hρ f)⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field : AmpleSt → ∀ (K : Type) [Field K] (P : PolAV (Sp K)), ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_field | exact GlobalTheory.Mum.veryAmpleAlong_field | (intros; apply GlobalTheory.Mum.veryAmpleAlong_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAlongPullbackTransportIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAlongPullbackTransportIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem gs_abCst {R : Type} [CommRing R] {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens)
    (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (x : R) :
    gs r z W (GlobalTheory.AbLaw.cst f W x) = gs (r ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) :=
  (gs_res r z le_top hz _).trans (gs_pull r f z ⊤ trivial _)

theorem gs_top_mul {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a * b)) =
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) *
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) := by
  rw [map_mul]; exact gs_mul q z ⊤ trivial _ _

theorem isUnit_gs_top {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : Rˣ) :
    IsUnit (gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a : R))) := by
  rw [gs_eq q z ⊤ trivial]
  exact ((a.isUnit.map _).map _).map _

theorem veryAmpleAlong_transport {K : Type} [Field K] {X Y XA : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K))
    (pA : XA ⟶ Spec (CommRingCat.of K)) (gn : Y ⟶ XA) [IsIso gn] (hp : gn ≫ pA = p) (π : Y ⟶ X) {L : LB X}
    (hL : L.IsLB) {LA : LB XA} (hLA : LA.IsLB) {k m : ℕ} (b : Fin (m + 1) → H0 LA k)
    (hb : VeryAmpleAlong pA (𝟙 XA) LA b) (σ : Fin (m + 1) → H0 L k) (c : Fin (m + 1) → Kˣ)
    (H : ∀ (y : Y) (j : Fin 1 → L.ι) (jA : Fin 1 → LA.ι), π y ∈ L.U (j 0) → gn y ∈ LA.U (jA 0) →
      ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i, secGerm π y (σ i) j =
        u.val * gs p y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) * secGerm gn y (b i) jA) :
    VeryAmpleAlong p π L σ := by
  classical

  have hmem : ∀ i (y : Y), y ∈ π ⁻¹ᵁ nonzeroLocus (σ i) ↔ gn y ∈ (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := by
    intro i y
    obtain ⟨j, hj⟩ := exists_chart hL (π y)
    obtain ⟨jA, hjA⟩ := exists_chart hLA (gn y)
    obtain ⟨u, hu⟩ := H y (fun _ => j) (fun _ => jA) hj hjA
    change π y ∈ nonzeroLocus (σ i) ↔ gn y ∈ nonzeroLocus (b i)
    rw [GlobalTheory.SectionRingIso.mem_iff_isUnit (σ i) π y (j := fun _ => j) hj,
      GlobalTheory.SectionRingIso.mem_iff_isUnit (b i) gn y (j := fun _ => jA) hjA]
    change IsUnit (secGerm π y (σ i) _) ↔ IsUnit (secGerm gn y (b i) _)
    rw [hu i, _root_.mul_assoc, IsUnit.mul_iff, IsUnit.mul_iff]
    simp only [u.isUnit, isUnit_gs_top p y (c i), true_and]
  have hW : ∀ i, π ⁻¹ᵁ nonzeroLocus (σ i) = gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) := fun i =>
    TopologicalSpace.Opens.ext (Set.ext fun y => hmem i y)
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  ·
    refine eq_top_iff.2 fun y _ => ?_
    have : gn y ∈ ⨆ i, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := hb.1 ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hmem i y).2 hi⟩
  · rw [hW i]; exact (hb.2 i).1.preimage gn
  · obtain ⟨-, ρ, hρ, hs⟩ := hb.2 i
    have le : π ⁻¹ᵁ nonzeroLocus (σ i) ≤ gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) := (hW i).le
    have ge : gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) ≤ π ⁻¹ᵁ nonzeroLocus (σ i) := (hW i).ge
    let φ : Γ(XA, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) →+* Γ(Y, π ⁻¹ᵁ nonzeroLocus (σ i)) :=
      (GlobalTheory.AbLaw.rs Y le).comp (gn.app _).hom
    have gsφ : ∀ y (hy : y ∈ π ⁻¹ᵁ nonzeroLocus (σ i)) (a : Γ(XA, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i))),
        gs (𝟙 Y) y _ (φ a) = gs gn y _ a := fun y hy a =>
      (gs_res (𝟙 Y) y le hy _).trans ((gs_pull (𝟙 Y) gn y _ (le hy) a).trans (by rw [Category.id_comp]))
    have hφc : ∀ x : K, φ (GlobalTheory.AbLaw.cst pA _ x) = GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i)) x := fun x =>
      fn_ext fun y hy => by
        rw [gsφ y hy, gs_abCst pA _ gn y (le hy), gs_abCst p _ (𝟙 Y) y hy, hp, Category.id_comp]
    let r : Fin (m + 1) → Γ(Y, π ⁻¹ᵁ nonzeroLocus (σ i)) := fun j =>
      GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i)) ((c j : K) / c i) * φ (ρ j)
    refine ⟨r, ?_, ?_⟩
    · intro j ch a ha hch
      obtain ⟨jA, hjA⟩ := exists_chart hLA (gn a)
      obtain ⟨u, hu⟩ := H a ch (fun _ => jA) (GlobalTheory.SectionRingIso.mem_ch.1 hch) hjA
      have haW : a ∈ π ⁻¹ᵁ nonzeroLocus (σ i) := ha
      have haV : gn a ∈ (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := le haW
      have hA : (𝟙 XA) (gn a) ∈ secChart LA (fun _ => jA) := GlobalTheory.SectionRingIso.mem_ch.2 hjA
      have key : ∀ j', secGerm gn a (b j') (fun _ => jA) =
          (gn.stalkMap a).hom (secGerm (𝟙 XA) (gn a) (b j') (fun _ => jA)) := fun j' => by
        have := secGerm_comp gn (𝟙 XA) a (b j') hA
        rwa [Category.comp_id] at this
      have e := congrArg (gn.stalkMap a).hom (hρ j (fun _ => jA) (gn a) haV hA)
      rw [map_mul, ← key, ← key, ← gs_stalkMap gn a _ haV] at e
      have hci : ((c j : K) / c i) * c i = c j := div_mul_cancel₀ _ (c i).ne_zero
      have hcst : gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c j : K)) =
          gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((c j : K) / c i)) *
            gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) := by
        rw [← gs_top_mul, hci]
      rw [hu j, hu i, gs_mul (𝟙 Y) a _ haW, gs_abCst p _ (𝟙 Y) a haW, gsφ a haW, e, Category.id_comp, hcst]
      ring
    · intro f
      obtain ⟨g0, hg0⟩ := (ConcreteCategory.bijective_of_isIso (gn.app ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)))).2
        (GlobalTheory.AbLaw.rs Y ge f)
      have hf : φ g0 = f := by
        change GlobalTheory.AbLaw.rs Y le ((gn.app _).hom g0) = f
        rw [hg0, GlobalTheory.AbLaw.rs_rs, GlobalTheory.AbLaw.rs_self]
      obtain ⟨P, hP⟩ := hs g0
      have hcomp : φ.comp (MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst pA _) ρ) =
          MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) (fun j => φ (ρ j)) :=
        MvPolynomial.ringHom_ext (fun x => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, hφc])
          (fun j => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'])
      have hρr : ∀ j, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) r
          (MvPolynomial.C ((c i : K) / c j) * MvPolynomial.X j) = φ (ρ j) := fun j => by
        have h1 : ((c i : K) / c j) * ((c j : K) / c i) = 1 := by
          rw [div_mul_div_comm, _root_.mul_comm (c i : K)]
          exact div_self (mul_ne_zero (c j).ne_zero (c i).ne_zero)
        rw [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
        change GlobalTheory.AbLaw.cst p _ ((c i : K) / c j) * (GlobalTheory.AbLaw.cst p _ ((c j : K) / c i) * φ (ρ j)) = φ (ρ j)
        rw [← _root_.mul_assoc, ← map_mul, h1, map_one, _root_.one_mul]
      refine ⟨MvPolynomial.bind₁ (fun j => MvPolynomial.C ((c i : K) / c j) * MvPolynomial.X j) P, ?_⟩
      rw [MvPolynomial.eval₂Hom_bind₁]
      simp only [hρr]
      rw [← hf, ← hP, ← hcomp]
      rfl

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAlongPullbackTransportIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryAmpleAlongPullback_transport_iso : ∀ {K : Type} [Field K] {X Y XA : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) (pA : XA ⟶ Spec (CommRingCat.of K)) (gn : Y ⟶ XA) [IsIso gn], gn ≫ pA = p → ∀ (π : Y ⟶ X) {L : LB X}, L.IsLB → ∀ {LA : LB XA}, LA.IsLB → ∀ {k m : ℕ} (b : Fin (m + 1) → H0 LA k), VeryAmpleAlong pA (𝟙 XA) LA b → ∀ (σ : Fin (m + 1) → H0 L k) (c : Fin (m + 1) → Kˣ), (∀ (y : Y) (j : Fin 1 → L.ι) (jA : Fin 1 → LA.ι), π y ∈ L.U (j 0) → gn y ∈ LA.U (jA 0) → ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i, secGerm π y (σ i) j = u.val * gs p y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) * secGerm gn y (b i) jA) → VeryAmpleAlong p π L σ := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_transport | exact GlobalTheory.Mum.veryAmpleAlong_transport | (intros; apply GlobalTheory.Mum.veryAmpleAlong_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsUniformisedGroupPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsUniformisedGroupPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mum

theorem sections_move_integral : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k m : ℕ}, 1 ≤ k → ∀ (b : Fin (m + 1) → H0 A.L k), ∃ (σ : Fin (m + 1) → H0 U.LG.L k) (c : Fin (m + 1) → (FractionRing R)ˣ), ∀ (y : ↥(pullback G.hom (jK R))) (j : Fin 1 → U.LG.L.ι) (jA : Fin 1 → A.L.ι), pullback.fst G.hom (jK R) y ∈ U.LG.L.U (j 0) → U.gen.hom.left y ∈ A.L.U (jA 0) → ∃ u : ((pullback G.hom (jK R)).presheaf.stalk y)ˣ, ∀ i, secGerm (pullback.fst G.hom (jK R)) y (σ i) j = u.val * gs (pullback.snd G.hom (jK R)) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i : FractionRing R)) * secGerm (show pullback G.hom (jK R) ⟶ A.A.left from U.gen.hom.left) y (b i) jA := by
  intro R _ _ I D A G _ _ U k m hk b
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨w', hw', -⟩ := GlobalTheory.Algebraise.exists_swap _ _ w hw (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
  choose s hs using fun i => GlobalTheory.Algebraise.exists_down A.isLB U.LG.isLB U.gen.hom.left
    (pullback.fst G.hom (jK R)) w' hw' (b i)
  choose c' σ hc' hσ using fun i => GlobalTheory.FormalGeneric.exists_integral U hk (s i)
  refine ⟨σ, fun i => Units.mk0 (algebraMap R (FractionRing R) (c' i))
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hc' i)), fun y j jA hj hjA => ?_⟩
  refine ⟨(gw w' (𝟙 _) y (jA 0) (fun _ => j 0) ^ k)⁻¹, fun i => ?_⟩
  have e₁ := hs i _ (𝟙 _) y (jA 0) (j 0) hjA hj
  have e₂ := hσ i _ (𝟙 _) y (j 0) hj
  have hc : cst (pullback.snd G.hom (jK R) ≫ jK R) y (c' i) = gs (pullback.snd G.hom (jK R)) y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) (c' i))) :=
    (gs_pull _ (jK R) y ⊤ trivial _).symm.trans
      (congrArg (gs _ y ⊤) (GlobalTheory.FormalGeneric.appTop_spec (algebraMap R (FractionRing R)) (c' i)))
  rw [Category.id_comp] at e₁ e₂
  rw [Category.id_comp, hc] at e₂
  rw [GlobalTheory.Algebraise.fin_one_const j, GlobalTheory.Algebraise.fin_one_const jA]
  change GlobalTheory.SectionRingIso.vl (σ i) _ y _ = _ * _ * GlobalTheory.SectionRingIso.vl (b i) _ y _
  rw [e₂, e₁, Units.val_mk0, ← Units.val_pow_eq_pow_val]
  generalize gw w' (𝟙 _) y (jA 0) (fun _ => j 0) ^ k = v
  rw [_root_.mul_assoc, mul_left_comm _ v.val, Units.inv_mul_cancel_left]
  rfl

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsUniformisedGroupPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_sections_uniformisedGroup_power : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k m : ℕ}, 1 ≤ k → ∀ (b : Fin (m + 1) → H0 A.L k), ∃ (σ : Fin (m + 1) → H0 U.LG.L k) (c : Fin (m + 1) → (FractionRing R)ˣ), ∀ (y : ↥(pullback G.hom (jK R))) (j : Fin 1 → U.LG.L.ι) (jA : Fin 1 → A.L.ι), pullback.fst G.hom (jK R) y ∈ U.LG.L.U (j 0) → U.gen.hom.left y ∈ A.L.U (jA 0) → ∃ u : ((pullback G.hom (jK R)).presheaf.stalk y)ˣ, ∀ i, secGerm (pullback.fst G.hom (jK R)) y (σ i) j = u.val * gs (pullback.snd G.hom (jK R)) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i : FractionRing R)) * secGerm (show pullback G.hom (jK R) ⟶ A.A.left from U.gen.hom.left) y (b i) jA := by
  first | exact @GlobalTheory.Mum.sections_move_integral | exact GlobalTheory.Mum.sections_move_integral | (intros; apply GlobalTheory.Mum.sections_move_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerUniformisedGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_veryAmpleAlong_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), ∃ (m : ℕ) (σ : Fin (m + 1) → H0 U.LG.L 4), VeryAmpleAlong ((Over.pullback (jK R)).obj G).hom (pullback.fst G.hom (jK R)) U.LG.L σ := by
  intro R _ _ I D A G _ _ U
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field GlobalTheory.lawsAndExpansions.1.1.ample _ A
  obtain ⟨σ, c, H⟩ := GlobalTheory.T.exists_integral_sections_uniformisedGroup_power R I D A G U (k := 4) (by norm_num) b
  have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact ⟨m, σ, GlobalTheory.T.veryAmpleAlongPullback_transport_iso _ A.A.hom U.gen.hom.left (Over.w U.gen.hom) _ U.LG.isLB A.isLB b hb σ c H⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerUniformisedGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_veryAmple_fourth_power_uniformised_group : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), ∃ (m : ℕ) (σ : Fin (m + 1) → H0 U.LG.L 4), VeryAmpleAlong ((Over.pullback (jK R)).obj G).hom (pullback.fst G.hom (jK R)) U.LG.L σ := by
  first | exact @GlobalTheory.Mum.exists_veryAmpleAlong_unif | exact GlobalTheory.Mum.exists_veryAmpleAlong_unif | (intros; apply GlobalTheory.Mum.exists_veryAmpleAlong_unif <;> assumption)
end

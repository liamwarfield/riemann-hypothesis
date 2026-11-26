module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellIsClosedInLeadingMinorOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellIsClosedInLeadingMinorOpen
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.CellClosed

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have e := Spec.map_injective h
  ext a
  exact congrArg (fun t => t.hom a) e

theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ g : A →+* B, f = spMap g := ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem unit_of_pt_eq {O A : Type} [CommRing O] [CommRing A] {N : ℕ} {b b' : O →+* A} {v v' : Fin (N + 1) → A} {hv hv'}
    (h : pt b v hv = pt b' v' hv') : ∃ u : Aˣ, v' = u • v := by
  have pt_str : ∀ (c : O →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
      pt c v hv ≫ PSpace.str O N = spMap c := by
    intro c v hv
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  have hb : b = b' := sp_inj (by rw [← pt_str b v hv, ← pt_str b' v' hv', h])
  subst hb
  exact (pt_eq_pt_iff b hv hv').1 h

theorem map_lform {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {M k : ℕ} {ι : Type}
    (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) (q) : φ (lform D ρ q) = lform (fun z => φ ∘ D z) ρ q := by
  simp [lform, map_prod]

section

variable {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens} {c D : Let m → Fin (M + 1) → Γ(X, U.1)}
  {w : Pm m} {R : Type} [CommRing R]

theorem map_uvec (ψ : CR m U →+* R) {k : ℕ} (e : Fin k → Let m) :
    ψ ∘ plk (uvec c w) e = plk (cellVec (fun z => ψ.comp MvPolynomial.C ∘ c z) w (ψ ∘ MvPolynomial.X)) e := by
  rw [map_plk]
  congr 1
  funext z
  rw [uvec, map_cellVec]
  rfl

theorem lead_eq (hD : LeftInv D c) (ψ : CR m U →+* R) {k : ℕ} {e : Fin k → Let m} (he : Down e) (u : Rˣ) :
    ∑ q, ψ.comp MvPolynomial.C (lform D (wLet w ∘ e) q) * (u • ψ ∘ plk (uvec c w) e) q = u := by
  have hL := LeftInv.map (ψ.comp MvPolynomial.C) hD
  have key := (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m R M _ _ w (ψ ∘ MvPolynomial.X) hL).1 k e he
  calc _ = (u : R) * ∑ q, lform (fun z => ψ.comp MvPolynomial.C ∘ D z) (wLet w ∘ e) q *
        plk (cellVec (fun z => ψ.comp MvPolynomial.C ∘ c z) w (ψ ∘ MvPolynomial.X)) e q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, map_uvec, map_lform]
        ring
    _ = u := by rw [key, mul_one]

def rd (w : Pm m) (x : CellVar m) : Fin (x.2.1.2 + 1) → Let m := fun l =>
  wLet w ⟨x.1, if (l : ℕ) = x.2.1.2 then x.2.1.1 else Fin.castLE (Nat.succ_le_of_lt x.2.1.2.2) l⟩

abbrev vEn (x : CellVar m) : En m := stdEn x.1 (x.2.1.2 + 1) (Nat.succ_le_of_lt x.2.1.2.2)

theorem read_eq (hD : LeftInv D c) (ψ : CR m U →+* R) (x : CellVar m) (u : Rˣ) :
    ∑ q, ψ.comp MvPolynomial.C (lform D (rd w x) q) * (u • ψ ∘ plk (uvec c w) (vEn x).2.1) q =
      u * ψ (MvPolynomial.X x) := by
  obtain ⟨τ, ⟨⟨i, j⟩, hij⟩⟩ := x
  have hL := LeftInv.map (ψ.comp MvPolynomial.C) hD
  have key := (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m R M _ _ w (ψ ∘ MvPolynomial.X) hL).2 τ i j hij
  calc _ = (u : R) * ∑ q, lform (fun z => ψ.comp MvPolynomial.C ∘ D z) (rd w ⟨τ, ⟨(i, j), hij⟩⟩) q *
        plk (cellVec (fun z => ψ.comp MvPolynomial.C ∘ c z) w (ψ ∘ MvPolynomial.X))
          (vEn (m := m) ⟨τ, ⟨(i, j), hij⟩⟩).2.1 q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, map_uvec, map_lform]
        ring
    _ = u * ψ (MvPolynomial.X ⟨τ, ⟨(i, j), hij⟩⟩) := by
        exact congrArg ((u : R) * ·) key

end

section

variable {O : Type} [CommRing O] {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens}
  {c D : Let m → Fin (M + 1) → Γ(X, U.1)} {w : Pm m} {P : Scheme.{0}} {p0 : P ⟶ X}
  {p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)} {h : Sp (CR m U) ⟶ P} {a : O →+* CR m U}

theorem over_inj {R : Type} [CommRing R] {φ φ' : Γ(X, U.1) →+* R}
    (e : spMap φ ≫ U.2.fromSpec = spMap φ' ≫ U.2.fromSpec) : φ = φ' := by
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have : Mono U.2.fromSpec := IsOpenImmersion.mono _
  exact sp_inj ((cancel_mono U.2.fromSpec).1 e)

theorem base_eq (hb : h ≫ p0 = cbase m U) {R : Type} [CommRing R] (ψ : CR m U →+* R) :
    (spMap ψ ≫ h) ≫ p0 = spMap (ψ.comp MvPolynomial.C) ≫ U.2.fromSpec := by
  rw [Category.assoc, hb, cbase, ← Category.assoc, sp_comp]

theorem unit_of_eq (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {R : Type} [CommRing R]
    (ψ : CR m U →+* R) (en : En m) {b : O →+* R} {v hv} (e : (spMap ψ ≫ h) ≫ p en = pt b v hv) :
    ∃ u : Rˣ, v = u • ψ ∘ plk (uvec c w) en.2.1 := by
  have span_range_comp_eq_top : ∀ {A B : Type} [CommRing A] [CommRing B] {n : ℕ}
      (v : Fin (n + 1) → A), Ideal.span (Set.range v) = ⊤ → (ψ : A →+* B) →
      Ideal.span (Set.range (ψ ∘ v)) = ⊤ := by
    intro A B _ _ n v hv ψ
    rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]
  have spMap_pt : ∀ {O A B : Type} [CommRing O] [CommRing A] [CommRing B] {n : ℕ}
      (c : O →+* A) (v : Fin (n + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) (ψ : A →+* B),
      spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
    intro O A B _ _ _ n c v hv ψ
    letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := O)
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  obtain ⟨hu, he⟩ := hp en
  rw [Category.assoc, he, spMap_pt] at e
  exact unit_of_pt_eq e

theorem range_le (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {W : P.Opens} (hW : IsCellOpen p0 p U D w W) :
    Set.range h ⊆ W := by
  rintro _ ⟨y, rfl⟩
  let y' : PrimeSpectrum (CR m U) := y
  let k := y'.asIdeal.ResidueField
  let f : CR m U →+* k := algebraMap (CR m U) k
  have hz : Set.range (spMap f ≫ h) ⊆ W := by
    refine (hW k (spMap f ≫ h)).2 ⟨f.comp MvPolynomial.C, base_eq hb f, ?_⟩
    intro τ j hj b v hv e
    obtain ⟨u, rfl⟩ := unit_of_eq hp f _ e
    have hl := lead_eq (w := w) hD f (down_std τ j hj) u
    intro h0
    exact u.ne_zero (hl.symm.trans h0)
  have hy : (spMap f) (show Sp k from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)) = y := by
    apply PrimeSpectrum.ext
    exact Ideal.ker_algebraMap_residueField _
  exact hz ⟨_, by rw [Scheme.Hom.comp_apply, hy]⟩

private theorem mono_cell_lemma (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {R : CommRingCat}
    (t₁ t₂ : Spec R ⟶ Sp (CR m U)) (e : t₁ ≫ h = t₂ ≫ h) : t₁ = t₂ := by
  have span_range_comp_eq_top : ∀ {A B : Type} [CommRing A] [CommRing B] {n : ℕ}
      (v : Fin (n + 1) → A), Ideal.span (Set.range v) = ⊤ → (ψ : A →+* B) →
      Ideal.span (Set.range (ψ ∘ v)) = ⊤ := by
    intro A B _ _ n v hv ψ
    rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]
  have spMap_pt : ∀ {O A B : Type} [CommRing O] [CommRing A] [CommRing B] {n : ℕ}
      (c : O →+* A) (v : Fin (n + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) (ψ : A →+* B),
      spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
    intro O A B _ _ _ n c v hv ψ
    letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := O)
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  obtain ⟨ψ₁, rfl⟩ := sp_surj (A := CR m U) (B := R) t₁
  obtain ⟨ψ₂, rfl⟩ := sp_surj (A := CR m U) (B := R) t₂
  have hC : ψ₁.comp MvPolynomial.C = ψ₂.comp MvPolynomial.C :=
    over_inj (by rw [← base_eq hb ψ₁, ← base_eq hb ψ₂, e])
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    exact congrArg (fun f => f r) hC
  · intro x
    obtain ⟨hu₂, he₂⟩ := hp (vEn x)
    have e₂ : (spMap ψ₁ ≫ h) ≫ p (vEn x) =
        pt (ψ₂.comp a) (ψ₂ ∘ plk (uvec c w) (vEn x).2.1) (span_range_comp_eq_top _ hu₂ ψ₂) := by
      rw [e, Category.assoc, he₂, spMap_pt]
    obtain ⟨u, hu⟩ := unit_of_eq hp ψ₁ (vEn x) e₂
    have l₁ := lead_eq (w := w) hD ψ₁ (vEn x).2.2 u
    have l₂ := lead_eq (w := w) hD ψ₂ (vEn x).2.2 1
    have r₁ := read_eq (w := w) hD ψ₁ x u
    have r₂ := read_eq (w := w) hD ψ₂ x 1
    rw [one_smul, hu, ← hC] at l₂ r₂
    have hu₁ : (u : R) = 1 := l₁.symm.trans (by rw [l₂, Units.val_one])
    have key := r₁.symm.trans r₂
    rw [hu₁, Units.val_one, one_mul, one_mul] at key
    exact key

theorem mono_cell (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) : Mono h := by
  constructor
  intro Z g₁ g₂ e
  refine Z.affineCover.hom_ext _ _ fun i => ?_
  exact mono_cell_lemma hD hb hp _ _
    ((Category.assoc _ _ _).trans ((congrArg (Z.affineCover.f i ≫ ·) e).trans (Category.assoc _ _ _).symm))

theorem exists_lift (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {W : P.Opens} (hW : IsCellOpen p0 p U D w W)
    {s : X ⟶ Sp O} [IsSeparated (p0 ≫ s)] (hs : ∀ en, p en ≫ PSpace.str _ _ = p0 ≫ s)
    {R K : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (z : Sp R ⟶ P) (hz : Set.range z ⊆ W) (ψ : CR m U →+* K) (e : spMap ψ ≫ h = spMap (algebraMap R K) ≫ z) :
    ∃ χ : CR m U →+* R, (algebraMap R K).comp χ = ψ ∧ spMap χ ≫ h = z := by
  classical
  have span_range_comp_eq_top : ∀ {A B : Type} [CommRing A] [CommRing B] {n : ℕ}
      (v : Fin (n + 1) → A), Ideal.span (Set.range v) = ⊤ → (ψ : A →+* B) →
      Ideal.span (Set.range (ψ ∘ v)) = ⊤ := by
    intro A B _ _ n v hv ψ
    rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]
  have spMap_pt : ∀ {O A B : Type} [CommRing O] [CommRing A] [CommRing B] {n : ℕ}
      (c : O →+* A) (v : Fin (n + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) (ψ : A →+* B),
      spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
    intro O A B _ _ _ n c v hv ψ
    letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := O)
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let k := IsLocalRing.ResidueField R
  let π : R →+* k := IsLocalRing.residue R
  have hzk : Set.range (spMap π ≫ z) ⊆ W := fun _ ⟨t, ht⟩ => hz ⟨(spMap π) t, by rw [← ht, Scheme.Hom.comp_apply]⟩
  obtain ⟨φk, hφk, hmin⟩ := (hW k (spMap π ≫ z)).1 hzk
  have hU : Set.range (z ≫ p0) ⊆ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have h0 : (z ≫ p0) (show Sp R from IsLocalRing.closedPoint R) ∈ (U.1 : Set X) := by
      have h1 : (spMap π ≫ z ≫ p0) (show Sp k from IsLocalRing.closedPoint k) ∈ Set.range U.2.fromSpec := by
        rw [← Category.assoc, hφk, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩
      rw [U.2.range_fromSpec, Scheme.Hom.comp_apply] at h1
      have hc : (spMap π) (show Sp k from IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R :=
        IsLocalRing.comap_closedPoint π
      rwa [hc] at h1
    exact ((IsLocalRing.specializes_closedPoint (show PrimeSpectrum R from y)).map
      (z ≫ p0).continuous).mem_open U.1.isOpen h0
  obtain ⟨φ0, hφ0⟩ := sp_surj (A := Γ(X, U.1)) (B := R) (IsOpenImmersion.lift U.2.fromSpec (z ≫ p0) hU)
  have hz0 : z ≫ p0 = spMap φ0 ≫ U.2.fromSpec := by rw [← hφ0, IsOpenImmersion.lift_fac]
  have hC : ψ.comp MvPolynomial.C = (algebraMap R K).comp φ0 :=
    over_inj (by rw [← base_eq hb ψ, e, Category.assoc, hz0, ← Category.assoc, sp_comp])
  have hk : φk = π.comp φ0 := over_inj (by rw [← hφk, Category.assoc, hz0, ← Category.assoc, sp_comp])
  obtain ⟨bO, hbO⟩ := sp_surj (A := O) (B := R) (z ≫ p0 ≫ s)
  have hpt : ∀ en, ∃ (v : Fin (plN M en.1 + 1) → R) (hv : Ideal.span (Set.range v) = ⊤), z ≫ p en = pt bO v hv :=
    fun en => exists_eq_pt bO (z ≫ p en) (by rw [Category.assoc, hs, hbO])
  choose V hV hzV using hpt
  have key : ∀ x : CellVar m, ∃ r : R, algebraMap R K r = ψ (MvPolynomial.X x) := by
    intro x
    obtain ⟨u, hu⟩ := unit_of_eq hp ψ (vEn x) (b := (algebraMap R K).comp bO) (v := algebraMap R K ∘ V (vEn x))
      (hv := span_range_comp_eq_top _ (hV _) _) (by rw [e, Category.assoc, hzV, spMap_pt])
    have hL : algebraMap R K (∑ q, φ0 (lform D (wLet w ∘ (vEn x).2.1) q) * V (vEn x) q) = u := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← lead_eq (w := w) hD ψ (vEn x).2.2 u]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, ← hu, hC]
      rfl
    have hR : algebraMap R K (∑ q, φ0 (lform D (rd w x) q) * V (vEn x) q) = u * ψ (MvPolynomial.X x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← read_eq hD ψ x u]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, ← hu, hC]
      rfl
    have hne : π (∑ q, φ0 (lform D (wLet w ∘ (vEn x).2.1) q) * V (vEn x) q) ≠ 0 := by
      have := hmin x.1 (x.2.1.2 + 1) (Nat.succ_le_of_lt x.2.1.2.2) (π.comp bO) (π ∘ V (vEn x))
        (span_range_comp_eq_top _ (hV _) π) (by rw [Category.assoc, hzV, spMap_pt])
      rw [hk] at this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_mul]
      exact this
    obtain ⟨t, ht⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hne
    have ht' : algebraMap R K (t : R) = u := by rw [ht, hL]
    have h1 : algebraMap R K (↑t⁻¹ : R) * (u : K) = 1 := by
      rw [← ht', ← map_mul, Units.inv_mul, map_one]
    refine ⟨(∑ q, φ0 (lform D (rd w x) q) * V (vEn x) q) * ↑t⁻¹, ?_⟩
    rw [map_mul, hR]
    calc (u : K) * ψ (MvPolynomial.X x) * algebraMap R K ↑t⁻¹ =
        (algebraMap R K ↑t⁻¹ * u) * ψ (MvPolynomial.X x) := by ring
      _ = ψ (MvPolynomial.X x) := by rw [h1, one_mul]
  choose r hr using key
  have hχ : (algebraMap R K).comp (MvPolynomial.eval₂Hom φ0 r) = ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact (congrArg (fun f => f a) hC).symm
    · intro x
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hr x
  refine ⟨MvPolynomial.eval₂Hom φ0 r, hχ, ?_⟩
  have : IsDominant (spMap (algebraMap R K)) := by
    constructor
    rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    have hg : (show Sp R from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) ∈ Set.range (spMap (algebraMap R K)) :=
      ⟨show Sp K from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K),
        PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K))⟩
    refine closure_mono (Set.singleton_subset_iff.2 hg) ?_
    show (show PrimeSpectrum R from y) ∈ closure ({⟨⊥, Ideal.isPrime_bot⟩} : Set (PrimeSpectrum R))
    rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    rw [SetLike.mem_coe, Ideal.mem_bot] at ha
    rw [ha]
    exact Submodule.zero_mem _
  refine ext_of_isDominant_of_isSeparated (p0 ≫ s) ?_ (spMap (algebraMap R K)) ?_
  · rw [← Category.assoc, base_eq hb, MvPolynomial.eval₂Hom_comp_C, ← hz0, Category.assoc]
  · rw [← Category.assoc, sp_comp, hχ, e]

theorem closed_of [Finite T] (hD : LeftInv D c) (hb : h ≫ p0 = cbase m U)
    (hp : ∀ en, ∃ hu, h ≫ p en = pt a (plk (uvec c w) en.2.1) hu) {W : P.Opens} (hW : IsCellOpen p0 p U D w W)
    {s : X ⟶ Sp O} [IsSeparated (p0 ≫ s)] (hs : ∀ en, p en ≫ PSpace.str _ _ = p0 ≫ s) :
    ∃ h' : Sp (CR m U) ⟶ W.toScheme, h' ≫ W.ι = h ∧ IsClosedImmersion h' := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact range_le hD hb hp hW
  let h' := IsOpenImmersion.lift W.ι h hr
  have hfac : h' ≫ W.ι = h := IsOpenImmersion.lift_fac _ _ _
  refine ⟨h', hfac, ?_⟩
  have : Mono h := mono_cell hD hb hp
  have : Mono h' := mono_of_mono_fac hfac
  have : IsAffine (Sp (CR m U)) := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Sp O) := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (h' ≫ W.ι ≫ p0 ≫ s) := isAffineHom_of_isAffine _
  have : QuasiCompact (h' ≫ W.ι ≫ p0 ≫ s) :=
    quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage _).isCompact
  have : QuasiCompact h' := QuasiCompact.of_comp h' (W.ι ≫ p0 ≫ s)
  have : LocallyOfFiniteType (h' ≫ W.ι ≫ p0) := by
    rw [← Category.assoc, hfac, hb, cbase]
    have : LocallyOfFiniteType (spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) := by
      rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.2 inferInstance
    have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    infer_instance
  have : LocallyOfFiniteType h' := locallyOfFiniteType_of_comp h' (W.ι ≫ p0)
  have hV : ValuativeCriterion h' := by
    rw [ValuativeCriterion.iff]
    refine ⟨fun S => ?_, IsSeparated.valuativeCriterion h'⟩
    obtain ⟨ψ, hψ⟩ := sp_surj (A := CR m U) (B := S.K) S.i₁
    have hz : Set.range (S.i₂ ≫ W.ι) ⊆ W := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← Scheme.Opens.range_ι W]
      exact Set.image_subset_range _ _
    have e : spMap ψ ≫ h = spMap (algebraMap S.R S.K) ≫ (S.i₂ ≫ W.ι) := by
      rw [← hψ, ← hfac, ← Category.assoc, S.commSq.w, Category.assoc]
    obtain ⟨χ, hχ₁, hχ₂⟩ := exists_lift hD hb hp hW hs _ hz ψ e
    refine CommSq.HasLift.mk' ⟨spMap χ, ?_, ?_⟩
    · change spMap (algebraMap S.R S.K) ≫ spMap χ = S.i₁
      rw [sp_comp, hχ₁, hψ]
    · rw [← cancel_mono W.ι, Category.assoc, hfac, hχ₂]
  have : IsProper h' := IsProper.of_valuativeCriterion h' hV
  exact (IsClosedImmersion.iff_isProper_and_mono h').2 ⟨inferInstance, inferInstance⟩

end

theorem cell_closed : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → IsNoetherianRing O → IsProjOver s → ∀ b w (W : P.Opens), IsCellOpen p0 p (V b) (D b) w W → ∃ h' : Sp (CR m (V b)) ⟶ W.toScheme, h' ≫ W.ι = h b w ∧ IsClosedImmersion h' := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hcov hpl _ _ b w W hW
  obtain ⟨N, i, hi, hi'⟩ := hpl.proj
  have : IsSeparated (PSpace.str O N) := inferInstance
  have : IsSeparated (p0 ≫ s) := by
    rw [← hi']
    infer_instance
  exact closed_of (hcov.inv b) (hpl.base b w) (hpl.plk b w) hW hpl.ovr

end GlobalTheory.FlagEmb.CellClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellIsClosedInLeadingMinorOpenStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCell_isClosed_in_leadingMinor_open : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → IsNoetherianRing O → IsProjOver s → ∀ b w (W : P.Opens), IsCellOpen p0 p (V b) (D b) w W → ∃ h' : Sp (CR m (V b)) ⟶ W.toScheme, h' ≫ W.ι = h b w ∧ IsClosedImmersion h' := by
  first | exact @GlobalTheory.FlagEmb.CellClosed.cell_closed | exact GlobalTheory.FlagEmb.CellClosed.cell_closed | (intros; apply GlobalTheory.FlagEmb.CellClosed.cell_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLESpMapFromSpec
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb

namespace GlobalTheory.FlagEmb.CellOpen

variable {O : Type} [CommRing O] {X P : Scheme.{0}} {N : ℕ} {k : Type} [Field k]

theorem top_le_of_mem {W : (Sp k).Opens} {x : Sp k} (hx : x ∈ W) : ⊤ ≤ W := fun y _ => by
  have : y = x := Subsingleton.elim (α := PrimeSpectrum k) y x
  exact this ▸ hx

theorem mem_basicOpen_fnOn (x : Sp k) (a : k) : x ∈ (Sp k).basicOpen (fnOn ⊤ a) ↔ a ≠ 0 := by
  rw [basicOpen_fnOn, top_inf_eq, mem_spOpen]
  have : x.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum k) x ⊥)
  rw [this, Ideal.mem_bot]

theorem appLE_spMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) {A : Type} [CommRing A] (φ : Γ(X, U) →+* A)
    {x : Sp A ⟶ X} (hx : x = spMap φ ≫ hU.fromSpec) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    (x.appLE U ⊤ h).hom a = fnOn ⊤ (φ a) := by
  subst hx
  have e := appLE_appLE (spMap φ) hU.fromSpec hU.fromSpec_preimage_self.ge (le_rfl : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) a
  refine e.symm.trans ?_
  rw [fromSpec_appLE_self]
  have e2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (R := Γ(X, U)) (S := .of A) (CommRingCat.ofHom φ))
  refine Eq.trans ?_ (congrArg (resG (Sp A) (le_top : (⊤ : (Sp A).Opens) ≤ ⊤)) e2.symm)
  rfl

def sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) (r : Fin (N + 1)) :
    Γ(P, p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r) :=
  ∑ q, (p0.appLE U _ inf_le_left).hom (a q) * pullRatio g _ r inf_le_right q

theorem appLE_sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U) (a : Fin (N + 1) → Γ(X, U))
    (r : Fin (N + 1)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)) :
    v r ≠ 0 ∧ (z.appLE _ ⊤ h).hom (sec p0 g U a r) = fnOn ⊤ ((∑ q, φ (a q) * v q) / v r) := open MvPolynomial GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjFrac in by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := O)
  have pre : pt b v hv ⁻¹ᵁ chart O N r = spOpen (v r) := by
    change ProjPoint.ofHom (grading O N) (eval₂Hom b v) (map_irrelevant_eval₂Hom b hv) ⁻¹ᵁ
      Proj.basicOpen (grading O N) (MvPolynomial.X r) = _
    rw [ProjPoint.ofHom_preimage_basicOpen _ _ _ one_pos (isHomogeneous_X O r), eval₂Hom_X']
    rfl
  have from_chart : (isAffineOpen_chart O N r).fromSpec =
      Spec.map (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos := by
    rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
    refine (Category.id_comp _).symm.trans (congrArg (· ≫ _) ?_)
    exact (Proj.basicOpenIsoSpec (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).hom_inv_id.symm
  have away_ratio (q : Fin (N + 1)) :
      (Proj.awayToSection (grading O N) (MvPolynomial.X r)).hom (ratioAway O N r q) = ratio O N r q := by
    rw [ratioAway, awayToSection_mk]
    exact frac_eq (by ring)
  have h2 : ⊤ ≤ pt b v hv ⁻¹ᵁ chart O N r := hz ▸ h.trans (z.preimage_mono inf_le_right)
  have hr : v r ≠ 0 := by
    have := h2 (Set.mem_univ (IsLocalRing.closedPoint k))
    rw [pre] at this
    intro e
    exact (mem_spOpen.1 this) (e ▸ zero_mem _)
  have ratio_mul (q : Fin (N + 1)) :
      pullRatio (pt b v hv) ⊤ r h2 q * fnOn ⊤ (v r) = fnOn ⊤ (v q) := by
    have hu' : IsUnit (eval₂Hom b v (MvPolynomial.X r)) := by rw [eval₂Hom_X']; exact IsUnit.mk0 _ hr
    have h4 := ProjPoint.awayLift_mk_mul (grading O N) (eval₂Hom b v) hu' (X_mem O N r) 1 (MvPolynomial.X q) (X_mem O N q)
    have he : pt b v hv = spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫ _ :=
      ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem O N r) hu'
    have : IsIso (Proj.awayToSection (grading O N) (MvPolynomial.X r)) :=
      (Proj.basicOpenIsoAway (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).isIso_hom
    have he2 : spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos =
        ofChartHom r (inv (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
          CommRingCat.ofHom (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
          (Scheme.ΓSpecIso (.of k)).inv) := by
      rw [ofChartHom, from_chart, ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
    rw [pullRatio_of_eq he h2 (he ▸ h2), pullRatio_of_eq he2 _ (ofChartHom_preimage _ _),
      pullRatio, ofChartHom_appLE, ← away_ratio, ← CommRingCat.comp_apply, IsIso.hom_inv_id_assoc,
      ]
    change (Scheme.ΓSpecIso (.of k)).inv.hom
      (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu' (ratioAway O N r q)) * _ = _
    rw [← resG_self (X := Sp k) le_top ((Scheme.ΓSpecIso (.of k)).inv.hom _)]
    change fnOn ⊤ _ * fnOn ⊤ _ = fnOn ⊤ _
    rw [← map_mul]
    exact congrArg _ (by simpa only [ratioAway, eval₂Hom_X', pow_one] using h4)
  refine ⟨hr, ((IsUnit.mk0 _ hr).map (fnOn ⊤)).mul_right_cancel ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_mul, div_mul_cancel₀ _ hr, sec, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, map_mul, appLE_appLE, appLE_spMap_fromSpec hU φ hφ, appLE_pullRatio, pullRatio_of_eq hz _ h2, mul_assoc,
    ratio_mul]

def linOpen (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) : P.Opens :=
  ⨆ r, P.basicOpen (sec p0 g U a r)

theorem mem_linOpen_iff (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Fin (N + 1) → Γ(X, U)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (x : Sp k) :
    z x ∈ linOpen p0 g U a ↔ ∑ q, φ (a q) * v q ≠ 0 := by
  have key : ∀ r (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)),
      z x ∈ P.basicOpen (sec p0 g U a r) ↔ ∑ q, φ (a q) * v q ≠ 0 := fun r h => by
    obtain ⟨hr, e⟩ := appLE_sec p0 g hU a r z φ hφ b v hv hz h
    have e2 := Scheme.basicOpen_appLE z ⊤ _ h (sec p0 g U a r)
    rw [top_inf_eq] at e2
    refine (iff_of_eq (congrArg (x ∈ ·) e2)).symm.trans ?_
    refine (iff_of_eq (congrArg (fun t => x ∈ (Sp k).basicOpen t) e)).trans ?_
    rw [mem_basicOpen_fnOn, div_ne_zero_iff, and_iff_left hr]
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := Opens.mem_iSup.1 hx
    exact (key r (top_le_of_mem (x := x) (P.basicOpen_le _ hr))).1 hr
  · intro hx
    obtain ⟨r, hr⟩ := GlobalTheory.ProjSpace.exists_mem_chart O N (g (z x))
    refine Opens.mem_iSup.2 ⟨r, (key r (top_le_of_mem (x := x) ⟨?_, hr⟩)).2 hx⟩
    change x ∈ (z ≫ p0) ⁻¹ᵁ U
    rw [hφ, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    trivial

theorem exists_isCellOpen (O : Type) [CommRing O] (X P : Scheme.{0}) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ)
    (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (U : X.affineOpens)
    (D : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) : ∃ W : P.Opens, IsCellOpen p0 p U D w W := by
  let F : (Σ τ : T, Fin (m τ + 1)) → P.Opens := fun i =>
    linOpen p0 (p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))) U.1 (lform D (wLet w ∘ std i.1 i.2 (Nat.le_of_lt_succ i.2.2)))
  refine ⟨p0 ⁻¹ᵁ U.1 ⊓ ⟨⋂ i, (F i : Set P), isOpen_iInter_of_finite fun i => (F i).2⟩, fun k _ z => ⟨fun h => ?_, ?_⟩⟩
  · have h1 : Set.range (z ≫ p0) ⊆ Set.range U.2.fromSpec := by
      rw [U.2.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact (h ⟨x, rfl⟩).1
    have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    let l := IsOpenImmersion.lift U.2.fromSpec (z ≫ p0) h1
    have hφ : z ≫ p0 = spMap (Spec.preimage l).hom ≫ U.2.fromSpec :=
      (IsOpenImmersion.lift_fac _ _ h1).symm.trans (congrArg (· ≫ _) (Spec.map_preimage l).symm)
    refine ⟨(Spec.preimage l).hom, hφ, fun τ j hj b v hv hz => ?_⟩
    refine (mem_linOpen_iff p0 _ U.2 _ z _ hφ b v hv hz (IsLocalRing.closedPoint k)).1 ?_
    exact Set.mem_iInter.1 (h ⟨_, rfl⟩).2 ⟨τ, j, Nat.lt_succ_of_le hj⟩
  · rintro ⟨φ, hφ, H⟩ _ ⟨x, rfl⟩
    refine ⟨?_, Set.mem_iInter.2 fun i => ?_⟩
    · change x ∈ (z ≫ p0) ⁻¹ᵁ U.1
      rw [hφ, Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_self]
      trivial
    · let y := z ≫ p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))
      obtain ⟨v, hv, e⟩ := exists_eq_pt (Spec.preimage (y ≫ PSpace.str _ _)).hom y (Spec.map_preimage _).symm
      exact (mem_linOpen_iff p0 _ U.2 _ z φ hφ _ v hv e x).2 (H _ _ _ _ v hv e)

end GlobalTheory.FlagEmb.CellOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImmersionOfClosedPieces
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.MemberGlue

theorem exists_immersion_of_closed_pieces : ∀ (P : Scheme.{0}) (ι : Type) [Finite ι] (C : ι → Scheme.{0}) [∀ a, IsAffine (C a)] [∀ a, IsReduced (C a)] (h : ∀ a, C a ⟶ P) (W : ι → P.Opens) (h' : ∀ a, C a ⟶ (W a).toScheme), IsLocallyNoetherian P → (∀ a, h' a ≫ (W a).ι = h a) → (∀ a, IsClosedImmersion (h' a)) → (∀ a a', Set.range (h a') ∩ (W a : Set P) ⊆ Set.range (h a)) → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ a, C a ⟶ F), IsImmersion f ∧ (∀ a, IsOpenImmersion (i a)) ∧ (∀ a, i a ≫ f = h a) ∧ ∀ x : F, ∃ a, x ∈ Set.range (i a) := by
  intro P ι _ C _ _ h W h' _ hh hcl hag
  have hpt : ∀ a c, (W a).ι (h' a c) = h a c := fun a c => by rw [← hh a]; rfl
  let U : P.Opens := ⨆ a, W a
  let Φ : Set P := ⋃ a, Set.range (h a)
  let O : ι → Set P := fun a => (W a).ι '' (Set.range (h' a))ᶜ
  have hO : ∀ a, IsOpen (O a) := fun a =>
    (W a).ι.isOpenEmbedding.isOpenMap _ (h' a).isClosedEmbedding.isClosed_range.isOpen_compl
  have hW : ∀ a c, h a c ∈ (W a : Set P) := fun a c => by
    rw [← hpt a c]; exact (h' a c).2
  have hU : ∀ a, (W a : Set P) ⊆ U := fun a =>
    SetLike.coe_subset_coe.mpr (le_iSup W a)
  have hΦ : U.ι ⁻¹' Φ = (U.ι ⁻¹' ⋃ a, O a)ᶜ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hx hxO
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, w, hw, e⟩ := Set.mem_iUnion.mp hxO |>.imp fun _ h => h
      have h1 : U.ι x ∈ Set.range (h a') ∩ (W a : Set P) :=
        ⟨⟨c', hc'⟩, e ▸ w.2⟩
      obtain ⟨c, hc⟩ := hag a a' h1
      exact hw ⟨c, (W a).ι.isOpenEmbedding.injective ((hpt a c).trans (hc.trans e.symm))⟩
    · intro hx
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
      have h2 : (⟨x.1, ha⟩ : (W a).toScheme) ∈ Set.range (h' a) := by
        by_contra hn
        exact hx (Set.mem_iUnion.mpr ⟨a, ⟨x.1, ha⟩, hn, rfl⟩)
      obtain ⟨c, hc⟩ := h2
      exact Set.mem_iUnion.mpr ⟨a, c, by rw [← hpt a c, hc]; rfl⟩
  let Z : TopologicalSpace.Closeds U.toScheme := ⟨U.ι ⁻¹' Φ, by
    rw [hΦ]
    exact ((isOpen_iUnion hO).preimage U.ι.continuous).isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let g : I.subscheme ⟶ U.toScheme := I.subschemeι
  let f : I.subscheme ⟶ P := g ≫ U.ι
  have hrg : Set.range g = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hfΦ : ∀ x, f x ∈ Φ := fun x => by
    have : g x ∈ (Z : Set U.toScheme) := hrg ▸ ⟨x, rfl⟩
    exact this
  have hfinj : Function.Injective f := f.isEmbedding.injective
  have hrU : ∀ a, Set.range (h a) ⊆ Set.range U.ι := fun a => by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hU a (hW a c)
  let k : ∀ a, C a ⟶ U.toScheme := fun a => IsOpenImmersion.lift U.ι (h a) (hrU a)
  have hk : ∀ a, k a ≫ U.ι = h a := fun a => IsOpenImmersion.lift_fac _ _ _
  have hkZ : ∀ a, Set.range (k a) ⊆ Z := fun a => by
    rintro _ ⟨c, rfl⟩
    change U.ι (k a c) ∈ Φ
    have : U.ι (k a c) = h a c := by rw [← hk a]; rfl
    rw [this]
    exact Set.mem_iUnion.mpr ⟨a, c, rfl⟩
  have hker : ∀ a, g.ker ≤ (k a).ker := fun a => by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ReducedSubgroup.vanishingIdeal_le_ker (k a) Z (hkZ a)
  let i : ∀ a, C a ⟶ I.subscheme := fun a => IsClosedImmersion.lift g (k a) (hker a)
  have hig : ∀ a, i a ≫ g = k a := fun a => IsClosedImmersion.lift_fac _ _ _
  have hif : ∀ a, i a ≫ f = h a := fun a => by
    rw [← hk a, ← hig a, Category.assoc]
  have hipt : ∀ a c, f (i a c) = h a c := fun a c => by rw [← hif a]; rfl
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  refine ⟨I.subscheme, f, i, inferInstance, fun a => ?_, hif, fun x => ?_⟩
  · let V : I.subscheme.Opens := f ⁻¹ᵁ W a
    have hiV : Set.range (i a) ⊆ Set.range V.ι := by
      rintro _ ⟨c, rfl⟩
      rw [Scheme.Opens.range_ι]
      change f (i a c) ∈ W a
      rw [hipt]
      exact hW a c
    have hrW : Set.range (V.ι ≫ f) ⊆ Set.range (W a).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2
    let j : C a ⟶ V.toScheme := IsOpenImmersion.lift V.ι (i a) hiV
    have hj : j ≫ V.ι = i a := IsOpenImmersion.lift_fac _ _ _
    let r : V.toScheme ⟶ (W a).toScheme := IsOpenImmersion.lift (W a).ι (V.ι ≫ f) hrW
    have hr : r ≫ (W a).ι = V.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have hjr : j ≫ r = h' a := by
      rw [← cancel_mono (W a).ι, Category.assoc, hr, reassoc_of% hj, hif, hh]
    have : Mono r := by
      have : Mono (r ≫ (W a).ι) := by rw [hr]; infer_instance
      exact mono_of_mono r (W a).ι
    have : IsClosedImmersion (j ≫ r) := by rw [hjr]; infer_instance
    have : IsClosedImmersion j := IsClosedImmersion.of_comp j r
    have : Surjective j := ⟨fun y => by
      have hy : f (V.ι y) ∈ (W a : Set P) := y.2
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp (hfΦ (V.ι y))
      obtain ⟨c, hc⟩ := hag a a' ⟨⟨c', hc'⟩, hy⟩
      refine ⟨c, V.ι.isOpenEmbedding.injective (hfinj ?_)⟩
      have : V.ι (j c) = i a c := by rw [← hj]; rfl
      rw [this, hipt, hc]⟩
    have : IsIso j := isIso_of_isClosedImmersion_of_surjective j
    rw [← hj]
    infer_instance
  · obtain ⟨a, c, hc⟩ := Set.mem_iUnion.mp (hfΦ x)
    exact ⟨a, c, hfinj ((hipt a c).trans hc)⟩

end GlobalTheory.MemberGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProduct
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.FlagEmb.cells_glue : ∀ (O K : Type) [CommRing O] [IsNoetherianRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover β s V α c D → IsPlk β s V α c p0 p h → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), IsImmersion f ∧ (∀ b w, IsOpenImmersion (i b w)) ∧ (∀ b w, i b w ≫ f = h b w) ∧ ∀ x : F, ∃ b w, x ∈ Set.range (i b w) := by
  intro O K _ _ _ β X s T _ m M B _ V α c D P p0 p h hs hX hC hP
  have hLN : ∀ {Y : Scheme.{0}} (g : Y ⟶ Sp O), IsProjOver g → IsLocallyNoetherian Y := by
    intro Y g hg
    obtain ⟨N, ι, _, rfl⟩ := hg
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str O N)
  haveI : IsLocallyNoetherian X := hLN s hs
  haveI : IsLocallyNoetherian P := hLN _ hP.proj
  have hW : ∀ b w, ∃ W, IsCellOpen p0 p (V b) (D b) w W := fun b w =>
    GlobalTheory.FlagEmb.CellOpen.exists_isCellOpen O X P T m M p0 p (V b) (D b) w
  choose W hW using hW
  have hcl := fun b w => GlobalTheory.T.flagCell_isClosed_in_leadingMinor_open O K β X s T m M B V α c D P p0 p h hC hP inferInstance hs b w (W b w) (hW b w)
  choose h' hh' hci using hcl
  have hred : ∀ b, AlgebraicGeometry.IsReduced (Sp (CR m (V b))) := by
    intro b
    have hn := (GlobalTheory.FlagEmb.cell_smooth_normal X T m (V b) hX).2
    haveI := fun x => (hn x).1
    exact isReduced_of_isReduced_stalk _
  let ι := B × Pm m
  haveI : Finite (Pm m) := Pi.finite
  haveI : ∀ a : ι, IsAffine (Sp (CR m (V a.1))) := fun a => inferInstance
  haveI : ∀ a : ι, AlgebraicGeometry.IsReduced (Sp (CR m (V a.1))) := fun a => hred a.1
  obtain ⟨F, f, i, hf, hio, hcomp, hcov⟩ := GlobalTheory.MemberGlue.exists_immersion_of_closed_pieces P ι
    (fun a => Sp (CR m (V a.1))) (fun a => h a.1 a.2) (fun a => W a.1 a.2) (fun a => h' a.1 a.2) inferInstance
    (fun a => hh' a.1 a.2) (fun a => hci a.1 a.2)
    (fun a a' => GlobalTheory.FlagEmb.Overlap.range_inter_cellOpen_subset O K β X s T m M B V α c D P p0 p h hC hP a.1 a.2
      (W a.1 a.2) (hW a.1 a.2) a'.1 a'.2)
  refine ⟨F, f, fun b w => i (b, w), hf, fun b w => hio (b, w), fun b w => hcomp (b, w), fun x => ?_⟩
  obtain ⟨a, ha⟩ := hcov x
  exact ⟨a.1, a.2, ha⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProductStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCells_glue_locallyClosed_pluckerProduct : ∀ (O K : Type) [CommRing O] [IsNoetherianRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover β s V α c D → IsPlk β s V α c p0 p h → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), IsImmersion f ∧ (∀ b w, IsOpenImmersion (i b w)) ∧ (∀ b w, i b w ≫ f = h b w) ∧ ∀ x : F, ∃ b w, x ∈ Set.range (i b w) := by
  first | exact @GlobalTheory.FlagEmb.cells_glue | exact GlobalTheory.FlagEmb.cells_glue | (intros; apply GlobalTheory.FlagEmb.cells_glue <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorAlgebraisationReductions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerCechH1Uniform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftSectionsOneLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphismsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConsecutiveVeryAmplePowersRelAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmple
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.GenTwist
variable {X : Scheme.{0}} {M H : LB X}

theorem tw_one_g (p q : M.ι) (k l : H.ι) :
    (((tw M H 1).g (p, k) (q, l) : Γ(X, (tw M H 1).U (p, k) ⊓ (tw M H 1).U (q, l))ˣ) :
      Γ(X, (tw M H 1).U (p, k) ⊓ (tw M H 1).U (q, l))) =
    rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
    rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l) := by
  have e : (tw M H 1).g (p, k) (q, l) = (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l ^ (-(1 : ℤ))))⁻¹ :
        Γ(X, M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l))ˣ) := rfl
  rw [e, map_zpow, zpow_neg, zpow_one, inv_inv]
  rfl

def prodSec (u : LB.Sec M) (s : LB.Sec H) : LB.Sec (tw M H 1) where
  f := fun pk => rs X (inf_le_left : M.U pk.1 ⊓ H.U pk.2 ≤ M.U pk.1) (u.f pk.1) *
    rs X (inf_le_right : M.U pk.1 ⊓ H.U pk.2 ≤ H.U pk.2) (s.f pk.2)
  compat := fun pk ql => by
    have key : ∀ (p q : M.ι) (k l : H.ι),
        rs X (inf_le_left : M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ H.U k)
          (rs X inf_le_left (u.f p) * rs X inf_le_right (s.f k)) =
        (rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q) (M.g p q) *
         rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l) (H.g k l)) *
        rs X (inf_le_right : M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U q ⊓ H.U l)
          (rs X inf_le_left (u.f q) * rs X inf_le_right (s.f l)) := by
      intro p q k l
      have hu := congrArg (rs X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ M.U p ⊓ M.U q)) (u.compat p q)
      have hs := congrArg (rs X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l) ≤ H.U k ⊓ H.U l)) (s.compat k l)
      simp only [rs_rs, map_mul] at hu hs ⊢
      rw [hu, hs]
      ring
    exact (key pk.1 ql.1 pk.2 ql.2).trans (congrArg (· * _) (tw_one_g (M := M) (H := H) pk.1 ql.1 pk.2 ql.2).symm)

theorem nonzeroLocus_prodSec (u : LB.Sec M) (s : LB.Sec H) :
    nonzeroLocus (prodSec u s) = nonzeroLocus u ⊓ nonzeroLocus s := by
  have hb : ∀ (p : M.ι) (k : H.ι), X.basicOpen ((prodSec u s).f ((p, k) : (tw M H 1).ι)) =
      X.basicOpen (u.f p) ⊓ X.basicOpen (s.f k) := by
    intro p k
    change X.basicOpen (rs X (inf_le_left : M.U p ⊓ H.U k ≤ M.U p) (u.f p) *
      rs X (inf_le_right : M.U p ⊓ H.U k ≤ H.U k) (s.f k)) = _
    rw [Scheme.basicOpen_mul]
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res]
    refine le_antisymm (inf_le_inf inf_le_right inf_le_right)
      (le_inf (le_inf (le_inf ((inf_le_left).trans (X.basicOpen_le _)) ((inf_le_right).trans (X.basicOpen_le _)))
        inf_le_left) (le_inf (le_inf ((inf_le_left).trans (X.basicOpen_le _))
          ((inf_le_right).trans (X.basicOpen_le _))) inf_le_right))
  refine le_antisymm (iSup_le fun pk => ?_) ?_
  · exact (hb pk.1 pk.2).le.trans (inf_le_inf (le_iSup (fun k => X.basicOpen (u.f k)) pk.1)
      (le_iSup (fun k => X.basicOpen (s.f k)) pk.2))
  · change (⨆ p, X.basicOpen (u.f p)) ⊓ (⨆ k, X.basicOpen (s.f k)) ≤ _
    rw [iSup_inf_eq]
    refine iSup_le fun p => ?_
    rw [inf_iSup_eq]
    exact iSup_le fun k => (hb p k).ge.trans
      (le_iSup (fun pk => X.basicOpen ((prodSec u s).f pk)) ((p, k) : (tw M H 1).ι))

theorem eval₂Hom_ratios_surjective (hM : M.IsLB) {m : ℕ} (u : Fin (m + 1) → LB.Sec M)
    (hu : ⨆ b, nonzeroLocus (u b) = ⊤) (a : Fin (m + 1)) {D N : X.Opens} (hD : IsAffineOpen D)
    (hN : N = nonzeroLocus (u a) ⊓ D) (ρ : Fin (m + 1) → Γ(X, N))
    (hρ : ∀ c q, rs X (inf_le_right : N ⊓ M.U q ≤ M.U q) ((u c).f q) =
      rs X (inf_le_left : N ⊓ M.U q ≤ N) (ρ c) * rs X (inf_le_right : N ⊓ M.U q ≤ M.U q) ((u a).f q)) :
    Function.Surjective (MvPolynomial.eval₂Hom (rs X (hN.le.trans inf_le_right : N ≤ D)) ρ) := by
  subst hN
  have hVD : nonzeroLocus (u a) ⊓ D ≤ D := inf_le_right
  have hV : IsAffineOpen (nonzeroLocus (u a) ⊓ D) := GlobalTheory.isAffineOpen_nonzeroLocus_inf hM (u a) hD
  letI : Algebra Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) := (rs X hVD).toAlgebra
  intro x
  suffices hx : x ∈ Algebra.adjoin Γ(X, D) (Set.range ρ) by
    rw [Algebra.adjoin_range_eq_range_aeval] at hx
    obtain ⟨P, rfl⟩ := hx
    exact ⟨P, rfl⟩
  let T : Set Γ(X, D) := {t | ∃ b p, X.basicOpen t ≤ X.basicOpen ((u b).f p)}
  have hT : Ideal.span T = ⊤ := by
    rw [← hD.self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ y))
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 hb
    obtain ⟨t, ht, hyt⟩ := hD.exists_basicOpen_le ⟨y, hp⟩ hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨t, b, p, ht⟩, hyt⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (Algebra.adjoin Γ(X, D) (Set.range ρ)).toSubmodule T hT x ?_
  rintro ⟨t, b, p, ht⟩
  have hWD : X.basicOpen t ≤ D := X.basicOpen_le t
  have hWp : X.basicOpen t ≤ M.U p := ht.trans (X.basicOpen_le _)
  have hW : IsAffineOpen (X.basicOpen t) := hD.basicOpen t
  let α : Γ(X, X.basicOpen t) := rs X hWp ((u a).f p)
  let β : Γ(X, X.basicOpen t) := rs X hWp ((u b).f p)
  have hβ : IsUnit β := by
    have h0 : IsUnit (rs X (X.basicOpen_le ((u b).f p)) ((u b).f p)) :=
      X.toRingedSpace.isUnit_res_basicOpen _
    have h1 := h0.map (rs X ht)
    rwa [rs_rs] at h1
  have hW'W : X.basicOpen α ≤ X.basicOpen t := X.basicOpen_le α
  have hW'eq : X.basicOpen α = X.basicOpen t ⊓ X.basicOpen ((u a).f p) := Scheme.basicOpen_res _ _ _
  have hW'V : X.basicOpen α ≤ nonzeroLocus (u a) ⊓ D := by
    rw [hW'eq]
    exact le_inf (inf_le_right.trans (GlobalTheory.basicOpen_le_nonzeroLocus _ _)) (inf_le_left.trans hWD)
  have hOW' : X.basicOpen (rs X hVD t) ≤ X.basicOpen α := by
    have e0 : X.basicOpen (rs X hVD t) = (nonzeroLocus (u a) ⊓ D) ⊓ X.basicOpen t :=
      Scheme.basicOpen_res _ _ _
    rw [e0, hW'eq]
    refine le_inf inf_le_right ?_
    rw [← GlobalTheory.nonzeroLocus_inf_chart]
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hWp)
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (X.basicOpen t)
    hW.isCompact hW.isQuasiSeparated α (rs X hW'V x)
  obtain ⟨k, z, hz⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X D
    hD.isCompact hD.isQuasiSeparated t y
  obtain ⟨k', z', hz'⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X D
    hD.isCompact hD.isQuasiSeparated t ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t))
  change rs X hW'W y = (rs X hW'W α) ^ n * rs X hW'V x at hy
  change rs X hWD z = (rs X hWD t) ^ k * y at hz
  change rs X hWD z' = (rs X hWD t) ^ k' * ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t)) at hz'
  have hr := congrArg (rs X (le_inf hW'V (hW'W.trans hWp) : X.basicOpen α ≤ (nonzeroLocus (u a) ⊓ D) ⊓ M.U p))
    (hρ b p)
  simp only [map_mul, rs_rs] at hr
  set I : Γ(X, X.basicOpen t) := ((hβ.unit⁻¹ : Γ(X, X.basicOpen t)ˣ) : Γ(X, X.basicOpen t)) with hIdef
  have hIβ : I * β = 1 := hβ.val_inv_mul
  have hz1 := congrArg (rs X hW'W) hz
  have hz1' := congrArg (rs X hW'W) hz'
  have hIβ' := congrArg (rs X hW'W) hIβ
  simp only [map_mul, map_pow, map_one, rs_rs] at hz1 hz1' hIβ'
  have hα : rs X hW'W α = rs X (hW'W.trans hWp) ((u a).f p) := rs_rs _ _ _
  have hβ' : rs X hW'W β = rs X (hW'W.trans hWp) ((u b).f p) := rs_rs _ _ _
  let c : Γ(X, D) := z * z' ^ n
  have e1 : rs X hW'V ((rs X hVD t) ^ (k + n * k') * x - rs X hVD c * ρ b ^ n) = 0 := by
    simp only [c, map_sub, map_mul, map_pow, rs_rs]
    rw [hz1, hz1', hy]
    have hARI : rs X hW'W α * rs X hW'V (ρ b) * rs X hW'W I = 1 := by
      rw [hα, mul_comm (rs X _ ((u a).f p)), ← hr, ← hβ', mul_comm, hIβ']
    calc _ = rs X (hW'W.trans hWD) t ^ (k + n * k') * rs X hW'V x -
          rs X (hW'W.trans hWD) t ^ (k + n * k') * rs X hW'V x *
            (rs X hW'W α * rs X hW'V (ρ b) * rs X hW'W I) ^ n := by ring
      _ = 0 := by rw [hARI, one_pow, mul_one, sub_self]
  obtain ⟨l, hl⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hV.isCompact
    ((rs X hVD t) ^ (k + n * k') * x - rs X hVD c * ρ b ^ n) (rs X hVD t) (by
      change rs X (X.basicOpen_le _) _ = 0
      rw [← rs_rs hW'V hOW', e1, map_zero])
  refine ⟨l + (k + n * k'), ?_⟩
  rw [Subalgebra.mem_toSubmodule, Algebra.smul_def]
  have e2 : algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ (l + (k + n * k'))) * x =
      algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ l * c) * ρ b ^ n := by
    change rs X hVD (t ^ (l + (k + n * k'))) * x = rs X hVD (t ^ l * c) * ρ b ^ n
    rw [mul_sub, sub_eq_zero] at hl
    rw [map_pow, map_mul, map_pow, pow_add, mul_assoc, hl, mul_assoc]
  change algebraMap Γ(X, D) Γ(X, nonzeroLocus (u a) ⊓ D) (t ^ (l + (k + n * k'))) * x ∈ _
  rw [e2]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self b)) _)

theorem veryAmpleBy_tw_of_generated : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  intro R _ X f H M n m s u hH hM hs hu
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans finProdFinEquiv.symm
  refine ⟨m * n + m + n, fun j => prodSec (u (e j).1) (s (e j).2), ?_, fun j => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ a, nonzeroLocus (u a) by rw [hu]; trivial)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (a, i), ?_⟩
    rw [nonzeroLocus_prodSec, e.apply_symm_apply]
    exact ⟨ha, hi⟩
  obtain ⟨aff, r, hr, sj⟩ := hs.2 (e j).2
  have loc := nonzeroLocus_prodSec (u (e j).1) (s (e j).2)
  have hNE := loc.le.trans inf_le_left
  have hND := loc.le.trans inf_le_right
  have o : r (e j).2 = 1 := Segre.ratio_self _ _ (hr _)
  choose ρ₀ hρ₀ using fun c => GlobalTheory.AmpleSpan.exists_isRatio (u c) (u (e j).1)
  have o' : ρ₀ (e j).1 = 1 := Segre.ratio_self _ _ (hρ₀ _)
  refine ⟨?_, fun b => rs X hNE (ρ₀ (e b).1) * rs X hND (r (e b).2), fun b kk => ?_, ?_⟩
  · rw [loc]
    exact GlobalTheory.isAffineOpen_nonzeroLocus_inf hM _ aff
  · have h1 : rs X (inf_le_right : nonzeroLocus (u (e j).1) ⊓ M.U kk.1 ≤ M.U kk.1) ((u (e b).1).f kk.1) =
        rs X inf_le_left (ρ₀ (e b).1) * rs X inf_le_right ((u (e j).1).f kk.1) := hρ₀ _ _
    have h2 := hr (e b).2 kk.2
    have hk1 : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
        nonzeroLocus (u (e j).1) ⊓ M.U kk.1 :=
      le_inf (inf_le_left.trans hNE) (inf_le_right.trans inf_le_left)
    have hk2 : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
        nonzeroLocus (s (e j).2) ⊓ H.U kk.2 :=
      le_inf (inf_le_left.trans hND) (inf_le_right.trans inf_le_right)
    replace h1 := congrArg (rs X hk1) h1
    replace h2 := congrArg (rs X hk2) h2
    simp only [map_mul, rs_rs] at h1 h2
    change rs X (inf_le_right : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          M.U kk.1 ⊓ H.U kk.2)
        (rs X inf_le_left ((u (e b).1).f kk.1) * rs X inf_le_right ((s (e b).2).f kk.2)) =
      rs X (inf_le_left : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          nonzeroLocus (prodSec (u (e j).1) (s (e j).2)))
        (rs X hNE (ρ₀ (e b).1) * rs X hND (r (e b).2)) *
      rs X (inf_le_right : nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ (M.U kk.1 ⊓ H.U kk.2) ≤
          M.U kk.1 ⊓ H.U kk.2)
        (rs X inf_le_left ((u (e j).1).f kk.1) * rs X inf_le_right ((s (e j).2).f kk.2))
    simp only [map_mul, rs_rs]
    rw [h1, h2]
    ring
  · have hgen := eval₂Hom_ratios_surjective hM u hu (e j).1 aff loc (fun c => rs X hNE (ρ₀ c))
      (fun c q => by
        have h : rs X (inf_le_right : nonzeroLocus (u (e j).1) ⊓ M.U q ≤ M.U q) ((u c).f q) =
            rs X inf_le_left (ρ₀ c) * rs X inf_le_right ((u (e j).1).f q) := hρ₀ c q
        have h' := congrArg (rs X (le_inf (inf_le_left.trans hNE) inf_le_right :
          nonzeroLocus (prodSec (u (e j).1) (s (e j).2)) ⊓ M.U q ≤ nonzeroLocus (u (e j).1) ⊓ M.U q)) h
        simp only [map_mul, rs_rs] at h' ⊢
        exact h')
    rw [← RingHom.range_eq_top, eq_top_iff]
    rintro x -
    obtain ⟨P, rfl⟩ := hgen x
    induction P using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨F, rfl⟩ := sj c
      induction F using MvPolynomial.induction_on with
      | C c₀ =>
        refine ⟨MvPolynomial.C c₀, ?_⟩
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        simp only [AbLaw.cst, RingHom.comp_apply, rs_rs]
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F l hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e j).1, l)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o', map_one, _root_.one_mul]
    | add P Q hP hQ => rw [map_add (f := _)]; exact Subring.add_mem _ hP hQ
    | mul_X P c hP =>
      rw [map_mul]
      refine Subring.mul_mem _ hP ⟨MvPolynomial.X (e.symm (c, (e j).2)), ?_⟩
      simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o, map_one, _root_.mul_one]
end GlobalTheory.GenTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmpleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  first | exact @GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | exact GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | (intros; apply GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem units_identity {G : Type*} [CommGroup G] (u P Q R β γ ε : G) (d t : ℤ) :
    (u * P * β⁻¹) * (u * Q * γ⁻¹) ^ (d * t) * (u * R * ε⁻¹) ^ d =
      u ^ (d * (t + 1) + 1) * (β * (γ ^ d) ^ t * (ε ^ d) ^ (1 : ℤ))⁻¹ * (P * Q ^ (d * t) * R ^ d) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

theorem pw_pw {X : Scheme.{0}} (L : LB X) (a b : ℤ) : pw (pw L a) b = pw L (a * b) := by
  show (⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩
  congr 1
  funext i j
  exact (zpow_mul _ _ _).symm

theorem lbIso_tw_tw {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (d t : ℤ) :
    LBIso (tw (tw L (pw L d) t) (pw L d) 1) (pw L (d * (t + 1) + 1)) := by
  refine GlobalTheory.LBAlg.lbIso_of_germs
    (A := tw (tw L (pw L d) t) (pw L d) 1) (B := pw L (d * (t + 1) + 1))
    (fun p => res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.1 from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g p.1 p.2.1.1) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.2 from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g p.1 p.2.1.2) ^ (d * t) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.2 from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g p.1 p.2.2) ^ d) ?_
  rintro x ⟨a, ⟨b, c⟩, e⟩ ⟨a', ⟨b', c'⟩, e'⟩ ha hp ha' hq
  have hb : x ∈ L.U b := hp.1.1
  have hc : x ∈ L.U c := hp.1.2
  have he : x ∈ L.U e := hp.2
  have hb' : x ∈ L.U b' := hq.1.1
  have hc' : x ∈ L.U c' := hq.1.2
  have he' : x ∈ L.U e' := hq.2
  have inv : ∀ {j j' : L.ι}, x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U j' ⊓ L.U j) (L.g j' j) = (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ :=
    fun hj hj' => eq_inv_of_mul_eq_one_right
      ((gm_cocycle hL (𝟙 X) x hj hj' hj).trans (gm_self hL (𝟙 X) x hj))
  have rel : ∀ {i i' j j' : L.ι}, x ∈ L.U i → x ∈ L.U i' → x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U i ⊓ L.U j) (L.g i j) = gm (𝟙 X) x (L.U i ⊓ L.U i') (L.g i i') *
        gm (𝟙 X) x (L.U i' ⊓ L.U j') (L.g i' j') * (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ := by
    intro i i' j j' hi hi' hj hj'
    rw [← gm_cocycle hL (𝟙 X) x hi hi' hj, ← gm_cocycle hL (𝟙 X) x hi' hj' hj, inv hj hj', mul_assoc]
  have sec : ∀ (a₀ b₀ c₀ e₀ : L.ι) (h : (𝟙 X : X ⟶ X) x ∈ (pw L (d * (t + 1) + 1)).U a₀ ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀)),
      gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀))
        (res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U b₀ from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g a₀ b₀) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U c₀ from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g a₀ c₀) ^ (d * t) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U e₀ from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g a₀ e₀) ^ d) =
      gm (𝟙 X) x (L.U a₀ ⊓ L.U b₀) (L.g a₀ b₀) * gm (𝟙 X) x (L.U a₀ ⊓ L.U c₀) (L.g a₀ c₀) ^ (d * t) *
        gm (𝟙 X) x (L.U a₀ ⊓ L.U e₀) (L.g a₀ e₀) ^ d := by
    intro a₀ b₀ c₀ e₀ h
    rw [map_mul, map_mul, map_zpow, map_zpow, gm_res _ x _ h, gm_res _ x _ h, gm_res _ x _ h]
  have eB : gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a ⊓ (pw L (d * (t + 1) + 1)).U a')
      ((pw L (d * (t + 1) + 1)).g a a') = gm (𝟙 X) x (L.U a ⊓ L.U a') (L.g a a') ^ (d * (t + 1) + 1) :=
    map_zpow (gm (𝟙 X) x (L.U a ⊓ L.U a')) (L.g a a') _
  have eA : gm (𝟙 X) x ((tw (tw L (pw L d) t) (pw L d) 1).U ((b, c), e) ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b', c'), e'))
      ((tw (tw L (pw L d) t) (pw L d) 1).g ((b, c), e) ((b', c'), e')) =
      gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b') * (gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d) ^ t *
        (gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d) ^ (1 : ℤ) := by
    have g1 : gm (𝟙 X) x ((pw L d).U c ⊓ (pw L d).U c') ((pw L d).g c c') =
        gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d := map_zpow _ _ _
    have g2 : gm (𝟙 X) x ((pw L d).U e ⊓ (pw L d).U e') ((pw L d).g e e') =
        gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d := map_zpow _ _ _
    refine (GlobalTheory.LBAlg.gm_tw (tw L (pw L d) t) (pw L d) 1 (𝟙 X) x ((b, c), e) ((b', c'), e') ⟨hp, hq⟩).trans ?_
    exact congrArg₂ (· * ·) ((GlobalTheory.LBAlg.gm_tw L (pw L d) t (𝟙 X) x (b, c) (b', c') ⟨hp.1, hq.1⟩).trans
      (congrArg₂ (· * ·) rfl (congrArg (· ^ t) g1))) (congrArg (· ^ (1 : ℤ)) g2)
  refine (sec a b c e ⟨ha, hp⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) eB.symm
    (congrArg (·⁻¹) eA.symm)) (sec a' b' c' e' ⟨ha', hq⟩).symm))
  rw [rel ha ha' hb hb', rel ha ha' hc hc', rel ha ha' he he']
  exact units_identity _ _ _ _ _ _ _ d t

end GlobalTheory.FormalAlg.ConsecPowers

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem exists_veryAmpleBy_pw_and_succ : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∀ c : ℕ, c = d ∨ c = d + 1 → ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw L c)), VeryAmpleBy X.hom (GlobalTheory.AbLaw.pw L c) s := by
  intro R _ X L hL hA
  obtain ⟨d₁, hd₁, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R X L hL).1 hA
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (AbLaw.pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have hH := isLB_pw hL (d₁ : ℤ)
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.TwistGen.twist_generated R X.left X.hom _ n s hH hs L hL
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t₀ ≤ (t : ℤ) := ⟨t₀.toNat, Int.self_le_toNat t₀⟩
  obtain ⟨m, u, hu⟩ := ht₀ (t : ℤ) ht
  refine ⟨d₁ * (t + 1), Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), fun c hc => ?_⟩
  rcases hc with rfl | rfl
  · obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R X.left X.hom _ n s hH hs (t + 1) (by omega)
    have e : GlobalTheory.AbLaw.pw L ((d₁ * (t + 1) : ℕ) : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) ((t + 1 : ℕ) : ℤ) := by
      rw [pw_pw]
      push_cast
      rfl
    rw [e]
    exact ⟨n', s', hs'⟩
  · obtain ⟨n', s', hs'⟩ := GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple R X.left X.hom (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (tw L (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (t : ℤ))
      n m s u hH (isLB_tw hL hH _) hs hu
    obtain ⟨s'', hs''⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw (isLB_tw hL hH _) hH 1) (isLB_pw hL _)
      (lbIso_tw_tw hL (d₁ : ℤ) (t : ℤ)) hs'
    have e : ((d₁ * (t + 1) + 1 : ℕ) : ℤ) = (d₁ : ℤ) * ((t : ℤ) + 1) + 1 := by push_cast; ring
    rw [e]
    exact ⟨n', s'', hs''⟩

end GlobalTheory.FormalAlg.ConsecPowers
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardChartsFormalTowerOfVeryAmple
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.ChartsEx

section Level0

variable {X : Scheme.{0}} {H : LB X}

theorem exists_chart_of_mem_nonzeroLocus (s : LB.Sec H) {x : X} (hx : x ∈ nonzeroLocus s) :
    ∃ k, x ∈ H.U k := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨l, X.basicOpen_le _ hl⟩

theorem mem_nonzeroLocus_iff_basicOpen (s : LB.Sec H) (k : H.ι) {x : X} (hk : x ∈ H.U k) :
    x ∈ nonzeroLocus s ↔ x ∈ X.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg X.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, X.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem isUnit_rs (s : LB.Sec H) (k : H.ι) {O : X.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus s) : IsUnit (rs X hk (s.f k)) := by
  have hb : O ≤ X.basicOpen (s.f k) := fun x hx => (mem_nonzeroLocus_iff_basicOpen s k (hk hx)).1 (h hx)
  have hu : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  simpa only [rs_rs] using hu.map (rs X hb)

theorem ratio_self (s : LB.Sec H) {V : X.Opens} (h : V ≤ nonzeroLocus s) (r : Γ(X, V))
    (hr : ∀ k, rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : V ⊓ H.U k ≤ V) r * rs X (inf_le_right : V ⊓ H.U k ≤ H.U k) (s.f k)) :
    r = 1 := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => V ⊓ H.U k) V (fun k => homOfLE inf_le_left)
    (fun x hx => ?_) _ _ fun k => ?_
  · obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus s (h hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hx, hl⟩
  · change rs X inf_le_left r = rs X inf_le_left 1
    rw [map_one]
    exact (isUnit_rs s k inf_le_right (inf_le_left.trans h)).mul_right_cancel
      ((hr k).symm.trans (_root_.one_mul _).symm)

variable {n : ℕ} (s : Fin (n + 1) → LB.Sec H) (r : ∀ i, Fin (n + 1) → Γ(X, nonzeroLocus (s i)))
  (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
      rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))


include hr in
theorem basicOpen_ratio (i j : Fin (n + 1)) :
    X.basicOpen (r i j) = nonzeroLocus (s i) ⊓ nonzeroLocus (s j) := by
  have key : ∀ k, (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) =
      (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := by
    intro k
    have e := congrArg X.basicOpen (hr i j k)
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (isUnit_rs (s i) k inf_le_right inf_le_left)] at e
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
    rw [e, inf_assoc, inf_comm (X.basicOpen (r i j)), ← inf_assoc, inf_idem]
  ext x
  constructor
  · intro hx
    have hxi : x ∈ nonzeroLocus (s i) := X.basicOpen_le _ hx
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen (r i j) := ⟨⟨hxi, hk⟩, hx⟩
    rw [← key k] at hm
    exact ⟨hxi, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hm.2⟩⟩
  · rintro ⟨hxi, hxj⟩
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (s i) hxi
    have hm : x ∈ (nonzeroLocus (s i) ⊓ H.U k) ⊓ X.basicOpen ((s j).f k) :=
      ⟨⟨hxi, hk⟩, (mem_nonzeroLocus_iff_basicOpen (s j) k hk).1 hxj⟩
    rw [key k] at hm
    exact hm.2


include hr in
theorem ratio_cocycle (i j l : Fin (n + 1)) :
    rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i l) =
      rs X (inf_le_left : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s i)) (r i j) *
        rs X (inf_le_right : nonzeroLocus (s i) ⊓ nonzeroLocus (s j) ≤ nonzeroLocus (s j)) (r j l) := by
  refine X.sheaf.eq_of_locally_eq' (fun k : H.ι => (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k)
    (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) (fun k => homOfLE inf_le_left) (fun x hx => ?_) _ _
    fun k => ?_
  · obtain ⟨l', hl⟩ := exists_chart_of_mem_nonzeroLocus (s i) hx.1
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l', hx, hl⟩
  · change rs X inf_le_left _ = rs X inf_le_left _
    have hi : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s i) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_left
    have hj : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ nonzeroLocus (s j) ⊓ H.U k :=
      inf_le_inf_right _ inf_le_right
    have e1 := congrArg (rs X hi) (hr i l k)
    have e2 := congrArg (rs X hi) (hr i j k)
    have e3 := congrArg (rs X hj) (hr j l k)
    simp only [map_mul, rs_rs] at e1 e2 e3 ⊢
    have hu := isUnit_rs (s i) k (inf_le_right : (nonzeroLocus (s i) ⊓ nonzeroLocus (s j)) ⊓ H.U k ≤ H.U k)
      (inf_le_left.trans inf_le_left)
    refine hu.mul_right_cancel ?_
    rw [← e1, e3, e2]
    ring

end Level0

end GlobalTheory.FormalAlg.ChartsEx

namespace GlobalTheory.FormalAlg.ChartsEx

section Tower

variable {R : Type} [CommRing R] {I : Ideal R}

theorem surjective_thickTrans (e : ℕ) : Surjective (thickTrans R I e) := by
  refine ⟨fun x => ?_⟩
  have h : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1 + 1))) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [_root_.range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (e + 1) := by
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using ha
    refine x.2.mem_of_pow_mem 2 ?_
    have : Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) * 2 by omega) ?_
      rw [pow_mul]
      exact Ideal.pow_mem_pow ha' 2
    rw [this]
    exact Ideal.zero_mem _
  exact hx

theorem isNilpotent_ker_factor (e : ℕ) (h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
  have hb : b ∈ I ^ (e + 1) := by simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hy
  rw [← map_mul, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.pow_le_pow_right (show e + 1 + 1 ≤ (e + 1) + (e + 1) by omega) ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul ha hb

variable {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ}


variable (Y n) in
abbrev Lvl (e : ℕ) : Type :=
  {p : (Σ D : Fin (n + 1) → (Y e).left.Opens, ∀ i, Fin (n + 1) → Γ((Y e).left, D i)) //
    ∀ i, IsAffineOpen (p.1 i)}


variable (β) in
def Lifts (e : ℕ) (q : Lvl Y n e) (q' : Lvl Y n (e + 1)) : Prop :=
  ∃ h : ∀ i, β e ⁻¹ᵁ q'.1.1 i = q.1.1 i,
    ∀ i j, ((β e).appLE (q'.1.1 i) (q.1.1 i) (h i).ge).hom (q'.1.2 i j) = q.1.2 i j

theorem exists_lifts {e : ℕ} (hsq : IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q : Lvl Y n e) : ∃ q' : Lvl Y n (e + 1), Lifts β e q q' := by
  have hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (by omega)
  have hsurj : Function.Surjective (Ideal.Quotient.factor hle) := Ideal.Quotient.factor_surjective hle
  have hD := fun i => GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent _ _
    (Ideal.Quotient.factor hle) hsurj (isNilpotent_ker_factor e hle) _ _ (Y (e + 1)).hom (Y e).hom
    (β e) hsq (q.1.1 i) (q.2 i)
  choose D' hD' hpre using hD
  haveI : IsClosedImmersion (β e) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip
      (IsClosedImmersion.spec_of_surjective _ hsurj)
  have hs : ∀ i, Function.Surjective ((β e).appLE (D' i) (q.1.1 i) (hpre i).ge).hom := by
    intro i y
    obtain ⟨x, hx⟩ := (β e).app_surjective (D' i) (hD' i) (rs _ (hpre i).le y)
    refine ⟨x, ?_⟩
    change rs _ (hpre i).ge (((β e).app (D' i)).hom x) = y
    rw [hx, rs_rs, rs_self]
  choose ρ' hρ' using fun i j => hs i (q.1.2 i j)
  exact ⟨⟨⟨D', ρ'⟩, hD'⟩, hpre, hρ'⟩


variable (β) in
def seq (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lvl Y n e :=
  Nat.rec (motive := Lvl Y n) q₀ (fun e q => Classical.choose (exists_lifts (hsq e) q)) e

theorem seq_lifts (hsq : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (q₀ : Lvl Y n 0) (e : ℕ) : Lifts β e (seq β hsq q₀ e) (seq β hsq q₀ (e + 1)) :=
  Classical.choose_spec (exists_lifts (hsq e) (seq β hsq q₀ e))

end Tower

end GlobalTheory.FormalAlg.ChartsEx


open GlobalTheory.FormalAlg.ChartsEx in
theorem GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ C : Charts I Y β n, (∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m) := by
  intro R _ I Y β hsq H₀ n s₀ _ hva
  obtain ⟨hcov, hloc⟩ := hva
  choose haff r hrel hsurj using hloc
  let q₀ : Lvl Y n 0 := ⟨⟨fun i => nonzeroLocus (s₀ i), r⟩, haff⟩
  have hsurjβ : ∀ e, Surjective (β e) := fun e =>
    MorphismProperty.of_isPullback (P := @Surjective) (hsq e).flip (surjective_thickTrans e)
  have hcover : ∀ e, ⨆ i, (seq β hsq q₀ e).1.1 i = ⊤ := by
    intro e
    induction e with
    | zero => exact hcov
    | succ e ih =>
      obtain ⟨hpre, -⟩ := seq_lifts hsq q₀ e
      refine top_unique fun y _ => ?_
      obtain ⟨x, rfl⟩ := (hsurjβ e).surj y
      have hx : x ∈ β e ⁻¹ᵁ (⨆ i, (seq β hsq q₀ (e + 1)).1.1 i) := by
        rw [Scheme.Hom.preimage_iSup]
        simp only [hpre]
        rw [ih]
        trivial
      exact hx
  refine ⟨{ D := fun e => (seq β hsq q₀ e).1.1
            aff := fun e => (seq β hsq q₀ e).2
            cover := hcover
            pre := fun e => (seq_lifts hsq q₀ e).1
            ρ := fun e => (seq β hsq q₀ e).1.2
            ρ_pull := fun e => (seq_lifts hsq q₀ e).2
            ρ_self := fun i => ratio_self (s₀ i) le_rfl (r i i) (hrel i i)
            basic := fun i j => basicOpen_ratio s₀ r hrel i j
            cocycle := fun i j l => ratio_cocycle s₀ r hrel i j l
            surj := hsurj }, fun i => rfl, hrel⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCrossPowersOfPullbackPowers
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.CrossIso

variable {X Y Z : Scheme.{0}}

theorem gm_pw_g (L : LB X) (t : ℤ) (f : Y ⟶ X) (y : Y) (i j : L.ι) :
    gm f y ((GlobalTheory.AbLaw.pw L t).U i ⊓ (GlobalTheory.AbLaw.pw L t).U j) ((GlobalTheory.AbLaw.pw L t).g i j) =
      gm f y (L.U i ⊓ L.U j) (L.g i j) ^ t :=
  map_zpow (gm f y (L.U i ⊓ L.U j)) (L.g i j) t

theorem gm_pull_g (L : LB X) (F : Y ⟶ X) (f : Z ⟶ Y) (z : Z) (J J' : PUnit → L.ι)
    (hj : F (f z) ∈ L.U (J PUnit.unit)) (hj' : F (f z) ∈ L.U (J' PUnit.unit)) :
    gm f z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (f ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) := by
  have hp : f z ∈ (L.pull F).U J ⊓ (L.pull F).U J' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f z _ (∏ _k : PUnit, (res _ (pullU F _ (L.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f z _ hp _).trans
    (gm_pull f F z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem gw_chart {b : Y ⟶ X} {A : LB X} {N : LB Y} {p : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) (k k' : A.ι) (l l' : N.ι) (hk : b (r z) ∈ A.U k) (hk' : b (r z) ∈ A.U k')
    (hl : r z ∈ N.U l) (hl' : r z ∈ N.U l') :
    gw w r z k l = gm (r ≫ b) z _ (A.g k k') * (gm r z _ (N.g l l') ^ p)⁻¹ * gw w r z k' l' := by
  have := (isGen_iff w).1 hw Z r z k k' l l' hk hk' hl hl'
  rw [gm_pw_g] at this
  exact this

theorem cross_alg {G : Type} [CommGroup G] (p q : ℤ) (a a' n u u' : G) :
    (a' * (n ^ q)⁻¹ * u') ^ p * ((a * (n ^ p)⁻¹ * u) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ * (u' ^ p * (u ^ q)⁻¹) := by
  simp only [mul_zpow, inv_zpow, ← zpow_mul, mul_comm q p, mul_inv, inv_inv]
  generalize n ^ (p * q) = m
  generalize a' ^ p = A'
  generalize a ^ q = A
  generalize u' ^ p = U'
  generalize u ^ q = U
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cross_chart {b : Y ⟶ X} {A A' : LB X} {N : LB Y} {p q : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)) (hw : w.IsGen) (hw' : w'.IsGen) (r : Z ⟶ Y) (z : Z)
    (k₁ k₂ : A.ι) (j₁ j₂ : A'.ι) (l₁ l₂ : N.ι) (hk₁ : b (r z) ∈ A.U k₁) (hk₂ : b (r z) ∈ A.U k₂)
    (hj₁ : b (r z) ∈ A'.U j₁) (hj₂ : b (r z) ∈ A'.U j₂) (hl₁ : r z ∈ N.U l₁) (hl₂ : r z ∈ N.U l₂) :
    gw w' r z j₁ l₁ ^ p * (gw w r z k₁ l₁ ^ q)⁻¹ =
      gm (r ≫ b) z _ (A'.g j₁ j₂) ^ p * (gm (r ≫ b) z _ (A.g k₁ k₂) ^ q)⁻¹ *
        (gw w' r z j₂ l₂ ^ p * (gw w r z k₂ l₂ ^ q)⁻¹) := by
  rw [gw_chart w hw r z k₁ k₂ l₁ l₂ hk₁ hk₂ hl₁ hl₂, gw_chart w' hw' r z j₁ j₂ l₁ l₂ hj₁ hj₂ hl₁ hl₂]
  exact cross_alg _ _ _ _ _ _ _

end GlobalTheory.FormalAlg.CrossIso

namespace GlobalTheory.FormalAlg
open CrossIso

theorem exists_crossIso : ∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (A A' : LB X) (N : LB Y) (p q : ℤ) (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b)) (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)), A.IsLB → A'.IsLB → N.IsLB → w.IsGen → w'.IsGen → ∃ c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b), c.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : A'.ι) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U k' → r z ∈ N.U l → Geo.Tor.gw c r z k' (fun _ => k) = Geo.Tor.gw w' r z k' l ^ p * (Geo.Tor.gw w r z k l ^ q)⁻¹ := by
  intro X Y b A A' N p q w w' hA hA' hN hw hw'
  have glue : ∀ (j : A'.ι) (k : A.ι), ∃ s : Γ(Y, ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
      ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U j → r z ∈ N.U l →
        gm r z _ s = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : N.ι → Y.Opens, ∀ l x, x ∈ W l ↔ b x ∈ A.U k ∧ b x ∈ A'.U j ∧ x ∈ N.U l :=
      ⟨fun l => b ⁻¹ᵁ A.U k ⊓ (b ⁻¹ᵁ A'.U j ⊓ N.U l), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ l, W l ≤ ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
        ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k) := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, mem_pull.2 ((hW l x).1 hx).1⟩
    have l₁ : ∀ l, W l ≤ (A'.pull b).U (fun _ => j) ⊓ (GlobalTheory.AbLaw.pw N q).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, ((hW l x).1 hx).2.2⟩
    have l₂ : ∀ l, W l ≤ (A.pull b).U (fun _ => k) ⊓ (GlobalTheory.AbLaw.pw N p).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).1, ((hW l x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), r z ∈ W l →
        gm r z (W l) (u l) = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ :=
      ⟨fun l => res (l₁ l) (w'.s (fun _ => j, l)) ^ p * (res (l₂ l) (w.s (fun _ => k, l)) ^ q)⁻¹,
        fun Z r z l hy => (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((map_zpow _ _ _).trans (congrArg (· ^ p) (gm_res r z (l₁ l) hy _)))
          ((map_inv _ _).trans (congrArg (·⁻¹)
            ((map_zpow _ _ _).trans (congrArg (· ^ q) (gm_res r z (l₂ l) hy _))))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨l, hl⟩ := exists_chart hN x
        exact Opens.mem_iSup.2 ⟨l, (hW l x).2 ⟨mem_pull.1 hx.2, mem_pull.1 hx.1, hl⟩⟩) u (fun l l' x hx => by
        have h₁ := (hW l x).1 hx.1
        have h₂ := (hW l' x).1 hx.2
        have e := cross_chart w w' hw hw' (𝟙 Y) x k k j j l l' h₁.1 h₁.1 h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2
        rw [gm_self hA (𝟙 Y ≫ b) x h₁.1, gm_self hA' (𝟙 Y ≫ b) x h₁.2.1, one_zpow, one_zpow, inv_one, one_mul,
          one_mul] at e
        exact (hu _ (𝟙 Y) x l hx.1).trans (e.trans (hu _ (𝟙 Y) x l' hx.2).symm))
    refine ⟨s, fun Z r z l hk hj hl => ?_⟩
    have hy := (hW l (r z)).2 ⟨hk, hj, hl⟩
    exact (gm_res r z (l₀ l) hy s).symm.trans ((congrArg (gm r z (W l)) (hs l)).trans (hu Z r z l hy))
  choose s hs using glue
  let c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b) :=
    ⟨fun P => s (P.1 PUnit.unit) (P.2 PUnit.unit)⟩
  have hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (K : PUnit → A.ι) (j : A'.ι) (l : N.ι),
      b (r z) ∈ A.U (K PUnit.unit) → b (r z) ∈ A'.U j → r z ∈ N.U l →
      gw c r z j K = gw w' r z j l ^ p * (gw w r z (K PUnit.unit) l ^ q)⁻¹ :=
    fun Z r z K j l hk hj hl => hs j (K PUnit.unit) Z r z l hk hj hl
  refine ⟨c, (isGen_iff c).2 ?_, fun Z r z k j l hk hj hl => hc Z r z (fun _ => k) j l hk hj hl⟩
  intro Z r z j j' K K' hj hj' hK hK'
  obtain ⟨l, hl⟩ := exists_chart hN (r z)
  have hk := mem_pull.1 hK
  have hk' := mem_pull.1 hK'
  have e := cross_chart w w' hw hw' r z (K PUnit.unit) (K' PUnit.unit) j j' l l hk hk' hj hj' hl hl
  refine (hc Z r z K j l hk hj hl).trans (e.trans ?_)
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw_g A' p _ z j j').symm (congrArg (·⁻¹) ?_))
    (hc Z r z K' j' l hk' hj' hl).symm
  exact ((gm_pull_g (GlobalTheory.AbLaw.pw A q) b r z K K' hk hk').trans (gm_pw_g A q _ z _ _)).symm

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsoLocalUnitsCompOfPullbackSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem gs_comp_stalkMap {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U)
    (a : Γ(X, U)) :
    gs (r ≫ F) z U a = (Scheme.Hom.stalkMap r z).hom (gs F (r z) U a) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem gm_val_stalkMap {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : r z ∈ V) (u : Γ(Y, V)ˣ) :
    ((gm r z V u : (Z.presheaf.stalk z)ˣ) : Z.presheaf.stalk z) =
      (Scheme.Hom.stalkMap r z).hom ((gm (𝟙 Y) (r z) V u : (Y.presheaf.stalk (r z))ˣ) : Y.presheaf.stalk (r z)) := by
  rw [← gs_unit r z V h, ← gs_unit (𝟙 Y) (r z) V h, gs_stalkMap r z V h]

theorem gw_comp_of_rel : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  intro X Y' Y b' β b hb A H' H w' v w ι s s' s'' h₁ h₂ h₃ hc z k k' k'' hk hk' hk''
  subst hb

  have hz : z ∈ ⨆ j, nonzeroLocus (s'' j) := by rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  obtain ⟨k₀, hk₀, hu₀⟩ := (mem_nonzeroLocus (s'' j) z).1 hj
  have hu : IsUnit (gs (𝟙 Y) z (H.U k'') ((s'' j).f k'')) := by
    rw [gs_compat (s'' j) (𝟙 Y) z hk'' hk₀]
    exact (Units.isUnit _).mul hu₀
  have hkb : b' (β z) ∈ A.U k := hk
  have e₁ := h₁ j (β z) k k' hkb hk'
  have e₂ := h₂ j z k' k'' hk' hk''
  have e₃ := h₃ j z k k'' hk hk''
  have hV : β z ∈ (A.pull b').U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hkb, hk'⟩
  have e₁' := congrArg (Scheme.Hom.stalkMap β z).hom e₁
  rw [map_mul, ← gs_comp_stalkMap β b' z _ hkb, ← gs_stalkMap β z _ hk'] at e₁'
  have hw' : ((Geo.Tor.gw w' β z k k' : (Y.presheaf.stalk z)ˣ) : Y.presheaf.stalk z) =
      (Scheme.Hom.stalkMap β z).hom ((Geo.Tor.gw w' (𝟙 _) (β z) k k' : (Y'.presheaf.stalk (β z))ˣ) :
        Y'.presheaf.stalk (β z)) :=
    gm_val_stalkMap β z _ hV _
  rw [← hw', e₂] at e₁'
  rw [e₃, ← _root_.mul_assoc, ← Units.val_mul] at e₁'
  exact Units.ext (hu.mul_left_inj.1 e₁')

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoZpowLocalUnitsPow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

open ReciprocityTheory.ChartRestriction.G.Semi

theorem commGroup_mul_inv_zpow {G : Type} [CommGroup G] (x y : G) (a : ℤ) : (x * y⁻¹) ^ a = x ^ a * (y ^ a)⁻¹ := by
  rw [mul_zpow, inv_zpow]

theorem div_pull_pw_g {X Y : Scheme.{0}} (A : LB X) (H : LB Y) (φ : Y ⟶ X) (a : ℤ) (p q : (PUnit → A.ι) × H.ι) :
    (LB.div ((GlobalTheory.AbLaw.pw A a).pull φ) (GlobalTheory.AbLaw.pw H a)).g p q =
      (((LB.div (A.pull φ) H).g p q) ^ a : Γ(Y, (LB.div (A.pull φ) H).U p ⊓ (LB.div (A.pull φ) H).U q)ˣ) := by
  show res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _ ^ a)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2 ^ a))⁻¹ =
    (res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2))⁻¹) ^ a
  simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact (commGroup_mul_inv_zpow _ _ a).symm

theorem lbIso_pw_pull_gw : ∀ (X Y : Scheme.{0}) (φ : Y ⟶ X) (A : LB X) (H : LB Y) (w : LB.Iso H (A.pull φ)), w.IsGen → ∀ a : ℤ, ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw H a) ((GlobalTheory.AbLaw.pw A a).pull φ), wa.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : H.ι), φ (r z) ∈ A.U k → r z ∈ H.U k' → Geo.Tor.gw wa r z k k' = Geo.Tor.gw w r z k k' ^ a := by
  intro X Y φ A H w hw a
  refine ⟨⟨fun p => w.s p ^ a⟩, ?_, ?_⟩
  · intro p q
    have e := congrArg (· ^ a) (hw p q)
    simp only [mul_zpow, ← map_zpow] at e
    exact e.trans (congrArg (· * res _ (w.s q ^ a)) (div_pull_pw_g A H φ a p q).symm)
  · intro Z r z k k' _ _
    exact map_zpow _ _ a

end GlobalTheory.FormalAlg
end
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

private theorem pw_tw {X : Scheme.{0}} (M H : LB X) (t a : ℤ) : AbLaw.pw (tw M H t) a = tw (AbLaw.pw M a) H (t * a) := by
  have : (AbLaw.pw (tw M H t) a).g = (tw (AbLaw.pw M a) H (t * a)).g := by
    funext p q
    change (res _ (M.g p.1 q.1) * (res _ (H.g p.2 q.2 ^ (-t)))⁻¹) ^ a =
      res _ (M.g p.1 q.1 ^ a) * (res _ (H.g p.2 q.2 ^ (-(t * a))))⁻¹
    simp only [map_zpow, map_inv, zpow_neg, inv_inv, zpow_mul]
    exact mul_zpow _ _ _
  exact congrArg (fun g => (⟨(tw M H t).ι, (tw M H t).U, g⟩ : LB X)) this

private theorem lbIso_tw_congr_right {X : Scheme.{0}} {A H H' : LB X} (hA : A.IsLB) (t : ℤ) (h : LBIso H H') :
    LBIso (tw A H t) (tw A H' t) := by
  obtain ⟨w, hw⟩ := h
  have l₁ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ A.U p.1.1 ⊓ A.U p.2.1 :=
    fun p x hx => ⟨hx.1.1, hx.2.1⟩
  have l₂ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ H'.U p.1.2 ⊓ H.U p.2.2 :=
    fun p x hx => ⟨hx.1.2, hx.2.2⟩
  have v : ∀ (x : X) (p : (A.ι × H'.ι) × (A.ι × H.ι)), x ∈ (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t) =
        gm (𝟙 X) x _ (A.g p.1.1 p.2.1) * gm (𝟙 X) x (H'.U p.1.2 ⊓ H.U p.2.2) (w.s (p.1.2, p.2.2)) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t)
    ?_
  intro x p q h₁ h₂ h₃ h₄
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (GlobalTheory.LBAlg.gm_tw A H' t (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩) (congrArg (·⁻¹) (GlobalTheory.LBAlg.gm_tw A H t (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩)))
    (v x q ⟨h₃, h₄⟩)).symm)
  rw [GlobalTheory.LBAlg.germs_of_isGen hw x (p.1.2, p.2.2) (q.1.2, q.2.2) h₁.2 h₂.2 h₃.2 h₄.2,
    ← gm_cocycle hA (𝟙 X) x h₁.1 h₂.1 h₃.1, ← gm_cocycle hA (𝟙 X) x h₂.1 h₃.1 h₄.1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

private theorem cancel_pw_aux :
    (∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (H M : LB X) (N : LB Y) (a : ℤ), H.IsLB → M.IsLB → N.IsLB →
      LBIso (GlobalTheory.AbLaw.pw N a) (H.pull b) → LBIso (GlobalTheory.AbLaw.pw N (a + 1)) (M.pull b) →
      LBIso N ((GlobalTheory.AbLaw.tw M H (-1)).pull b)) ∧
    ∀ (X : Scheme.{0}) (H M : LB X) (a : ℤ), H.IsLB → M.IsLB →
      LBIso (GlobalTheory.AbLaw.pw H (a + 1)) (GlobalTheory.AbLaw.pw M a) →
      LBIso H (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M H (-1)) a) := by
  refine ⟨fun X Y b H M N a hH hM hN e₁ e₂ => ?_, fun X H M a hH hM e => ?_⟩
  · have hP : (M.pull b).IsLB := pull_isLB hM b
    have hQ : (H.pull b).IsLB := pull_isLB hH b
    have k₁ : LBIso N (tw (tw N (H.pull b) 1) (H.pull b) (-1)) := GlobalTheory.LBAlg.lbIso_tw_tw hN hQ 1
    have k₂ : LBIso (tw N (H.pull b) 1) (tw N (AbLaw.pw N a) 1) := lbIso_tw_congr_right hN 1 e₁.symm
    have k₃ : tw N (AbLaw.pw N a) 1 = tw N N a := by
      simp only [tw, GlobalTheory.Algebraise.pw_pw]
      congr 2
      ring
    have k₄ : LBIso (tw N N a) (M.pull b) :=
      LBIso.trans (isLB_tw hN hN a) (isLB_pw hN (a + 1)) hP (GlobalTheory.Algebraise.lbIso_tw hN a).symm e₂
    have k₅ : LBIso (tw N (H.pull b) 1) (M.pull b) :=
      LBIso.trans (isLB_tw hN hQ 1) (isLB_tw hN (isLB_pw hN a) 1) hP k₂ (k₃ ▸ k₄)
    have k₆ : LBIso (tw (tw N (H.pull b) 1) (H.pull b) (-1)) (tw (M.pull b) (H.pull b) (-1)) :=
      GlobalTheory.LBAlg.lbIso_tw_congr hQ (-1) k₅
    have k₇ : LBIso (tw (M.pull b) (H.pull b) (-1)) ((tw M H (-1)).pull b) :=
      LBIso.chartPull (GlobalTheory.LBAlg.chartPullTw (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M b b rfl)
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull H b b rfl) (-1))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (tw M H (-1)) b b rfl) (GlobalTheory.LBAlg.lbIso_self (isLB_tw hM hH (-1)))
    exact LBIso.trans hN (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₁
      (LBIso.trans (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (isLB_tw hP hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₆ k₇)
  · have h₁ : LBIso (tw H H a) (AbLaw.pw M a) :=
      LBIso.trans (isLB_tw hH hH a) (isLB_pw hH (a + 1)) (isLB_pw hM a) (GlobalTheory.Algebraise.lbIso_tw hH a).symm e
    have h₂ : LBIso (tw (tw H H a) H (-a)) (tw (AbLaw.pw M a) H (-a)) := GlobalTheory.LBAlg.lbIso_tw_congr hH (-a) h₁
    have h₃ : AbLaw.pw (tw M H (-1)) a = tw (AbLaw.pw M a) H (-a) := by
      rw [pw_tw]
      congr 1
      ring
    rw [h₃]
    exact LBIso.trans hH (isLB_tw (isLB_tw hH hH a) hH (-a)) (isLB_tw (isLB_pw hM a) hH (-a))
      (GlobalTheory.LBAlg.lbIso_tw_tw hH hH a) h₂

private theorem lbIso_of_compatible_reductions_aux :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
      ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
        (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) →
        (∀ e, β e ≫ b (e + 1) = b e) → ∀ (A A' : LB X.left), A.IsLB → A'.IsLB →
        ∀ c : ∀ e, LB.Iso (A.pull (b e)) (A'.pull (b e)), (∀ e, (c e).IsGen) →
        (∀ e z k k', b e z ∈ A.U k → b e z ∈ A'.U k' →
          Geo.Tor.gw (c (e + 1)) (β e) z k' (fun _ => k) = Geo.Tor.gw (c e) (𝟙 _) z k' (fun _ => k)) →
        LBIso A A' := by
  intro R _ _ I hI X hX Y β b hpb hβ A A' hA hA' c hc hcomp
  have hle : ∀ e (p : (LB.div A' A).ι), b e ⁻¹ᵁ (LB.div A' A).U p ≤
      (LB.div (A'.pull (b e)) (A.pull (b e))).U (fun _ => p.1, fun _ => p.2) :=
    fun e p x hx => ⟨Set.mem_iInter.2 fun _ => hx.1, Set.mem_iInter.2 fun _ => hx.2⟩
  let s : ∀ e (i : (LB.div A' A).ι), Γ((Y e).left, b e ⁻¹ᵁ (LB.div A' A).U i)ˣ :=
    fun e p => res (hle e p) ((c e).s (fun _ => p.1, fun _ => p.2))
  have hs : ∀ e (z : (Y e).left) (p : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      gm (𝟙 _) z _ (s e p) = gw (c e) (𝟙 _) z p.1 (fun _ => p.2) :=
    fun e z p h => gm_res (𝟙 (Y e).left) z (hle e p) (by simpa using h) _
  have hg : ∀ e (z : (Y e).left) (p p' : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      b e z ∈ (LB.div A' A).U p' →
      gm (b e) z _ ((LB.div A' A).g p p') =
        gm (b e) z _ (A'.g p.1 p'.1) * (gm (b e) z _ (A.g p.2 p'.2))⁻¹ := by
    intro e z p p' h h'
    have hm : b e z ∈ (LB.div A' A).U p ⊓ (LB.div A' A).U p' := ⟨h, h'⟩
    show gm (b e) z _ (res _ (A'.g p.1 p'.1) * (res _ (A.g p.2 p'.2))⁻¹) = _
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ _ _ hm _)
      ((map_inv _ _).trans (congrArg _ (gm_res _ _ _ hm _))))
  have hpg : ∀ e (z : (Y e).left) (k k' : A.ι), b e z ∈ A.U k → b e z ∈ A.U k' →
      gm (𝟙 (Y e).left) z _ ((A.pull (b e)).g (fun _ => k) (fun _ => k')) =
        gm (b e) z _ (A.g k k') := by
    intro e z k k' hk hk'
    have hp : (𝟙 (Y e).left) z ∈ (A.pull (b e)).U (fun _ => k) ⊓ (A.pull (b e)).U (fun _ => k') :=
      ⟨mem_pull.2 hk, mem_pull.2 hk'⟩
    show gm _ z _ (∏ _k : PUnit, (res _ (pullU (b e) _ (A.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z _ hp _).trans ((gm_pull (𝟙 _) (b e) z (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans
      (by rw [Category.id_comp]))
  refine (GlobalTheory.FormalAlg.exists_isGen_of_reductions R I hI X hX Y β b hpb hβ (LB.div A' A) (LB.isLB_div hA' hA) s ?_ ?_ :
    ∃ t : LB.Gen (LB.div A' A), t.IsGen)
  · intro e z p p' h h'
    rw [hs e z p h, hs e z p' h', hg e z p p' h h']
    have := (isGen_iff (c e)).1 (hc e) _ (𝟙 _) z p.1 p'.1 (fun _ => p.2) (fun _ => p'.2) h.1 h'.1
      (mem_pull.2 h.2) (mem_pull.2 h'.2)
    rw [this, hpg e z p.2 p'.2 h.2 h'.2, Category.id_comp]
  · intro e z p h
    have h1 : b (e + 1) (β e z) = b e z := by rw [← hβ e]; rfl
    have hz : β e z ∈ b (e + 1) ⁻¹ᵁ (LB.div A' A).U p := show b (e + 1) (β e z) ∈ _ from h1 ▸ h
    rw [show gm (β e) z _ (s (e + 1) p) = gw (c (e + 1)) (β e) z p.1 (fun _ => p.2) from
      gm_res _ z (hle (e + 1) p) hz _, hcomp e z p.2 p.1 h.2 h.1, hs e z p h]

private theorem cross_cancel_aux {G : Type} [CommGroup G] (a a' g : G) (p q : ℤ) :
    (a' * g ^ q) ^ p * ((a * g ^ p) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ := by
  rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm q p]
  group

private theorem lbIso_pw_cross_aux :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
      ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
        (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) →
        (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))),
        (∀ e, (N e).IsLB) → ∀ (p q : ℤ) (A A' : LB X.left), A.IsLB → A'.IsLB →
        ∀ (w : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) p) (A.pull (b e)))
          (w' : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) q) (A'.pull (b e))),
        (∀ e, (w e).IsGen ∧ (w' e).IsGen) →
        (∀ e z k l' l, b e z ∈ A.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
          Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ p) →
        (∀ e z k l' l, b e z ∈ A'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
          Geo.Tor.gw (w' e) (𝟙 _) z k l = Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ q) →
        LBIso (GlobalTheory.AbLaw.pw A q) (GlobalTheory.AbLaw.pw A' p) := by
  intro R _ _ I hI X hX Y β b hb hβ N v hN p q A A' hA hA' w w' hg hv hv'
  choose c hc hcg using fun e =>
    GlobalTheory.FormalAlg.exists_crossIso X.left (Y e).left (b e) A A' (N e) p q (w e) (w' e) hA hA' (hN e) (hg e).1 (hg e).2
  refine lbIso_of_compatible_reductions_aux R I hI X hX Y β b hb hβ (pw A q) (pw A' p) (isLB_pw hA q) (isLB_pw hA' p) c hc ?_
  intro e z k k' hk hk'
  obtain ⟨l, hl⟩ := exists_chart (hN e) z
  obtain ⟨l', hl'⟩ := exists_chart (hN (e + 1)) (β e z)
  have hz : b (e + 1) (β e z) = b e z := by
    rw [← Scheme.Hom.comp_apply, hβ e]
  have h1 := hcg (e + 1) (Y e).left (β e) z k k' l' (hz ▸ hk) (hz ▸ hk') hl'
  have h0 := hcg e (Y e).left (𝟙 _) z k k' l hk hk' hl
  rw [h1, h0, hv e z k l' l hk hl' hl, hv' e z k' l' l hk' hl' hl]
  exact (cross_cancel_aux _ _ _ p q).symm

private theorem exists_lb_of_generated_system_proper_aux :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
      ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
        (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) →
        (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))),
        (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)),
        (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → (∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤) →
        ∃ (M : LB X.left) (s' : Fin (n + 1) → LB.Sec M) (w : ∀ e, LB.Iso (H e) (M.pull (b e))),
          M.IsLB ∧ ∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j) := by
  intro R _ _ I hcI X hX Y β b hb hbb H v hH n s hs hgen
  obtain ⟨P, f, O, t, hO, hva, hP⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose c w hc' hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy R P f O n t hO hva _
    ((Y e).hom ≫ thick R I e) (H e) (s e) (hH e).1 (hgen e) (fun d F hF h k => by
      obtain ⟨m, hm⟩ := (hP d F hF).1 h 0
      have : F = 0 := by
        rw [Ideal.mem_bot] at hm
        exact ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1)))).pow m).left (by simpa using hm)
      rw [this, map_zero])
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← (hb (e + 1)).w, ← Category.assoc, hbb, (hb e).w]
  have hcc : ∀ e, β e ≫ c (e + 1) = c e := fun e => by
    have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hO (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections R P f O n t hO hva _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hc', hc', c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
  haveI hPp : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R P f ⟨O, hO, n, t, hva⟩
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.formalAlgebraisation_morphisms' R I hcI X (Over.mk f) hX (inferInstanceAs (IsSeparated f))
    (inferInstanceAs (LocallyOfFiniteType f)) (inferInstanceAs (QuasiCompact f)) Y β b hb hbb
    c hc' hcc
  have hM : (O.pull g.left).IsLB := LB.isLB_pull hO _
  obtain ⟨s', hs'⟩ := GlobalTheory.MorAlg.exists_isPull g.left hO t
  have key : ∀ e, GlobalTheory.MorAlg.IsPull (b e) s' (s e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hO hM (hH e).1 hs' (by rw [hg e]; exact ⟨w e, hw e, hr e⟩)
  choose w' hw' cw using key
  exact ⟨O.pull g.left, s', w', hM, fun e => ⟨hw' e, fun j => cw e j⟩⟩

private theorem exists_lift_sections_tower_aux :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
      ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left),
        (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) →
        ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ →
        ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))),
          (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw H₀ k) →
          ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e) := by
  intro R _ _ I Y β hY H₀ n s₀ hH hva
  obtain ⟨C, hC⟩ := GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy R I Y β hY H₀ n s₀ hH hva
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.FormalAlg.towerCech_h1_uniform R I Y β hY n C
  refine ⟨k₀, fun k hk L u hL hL0 σ₀ => ?_⟩
  let γ : ∀ e, (Y 0).left ⟶ (Y e).left := fun e =>
    Nat.rec (motive := fun e => (Y 0).left ⟶ (Y e).left) (𝟙 _) (fun e g => g ≫ β e) e
  have hγs : ∀ e, γ e ≫ β e = γ (e + 1) := fun e => rfl
  have hP : (GlobalTheory.AbLaw.pw H₀ k).IsLB := isLB_pw hH _
  have hiso : ∀ e, LBIso ((L e).pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) := by
    intro e
    induction e with
    | zero => exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (L 0) (𝟙 _) (𝟙 _) rfl) (chartPullId _) hL0
    | succ e ih =>
      refine LBIso.trans (pull_isLB (hL (e + 1)).1 _) (pull_isLB (hL e).1 _) hP ?_ ih
      exact LBIso.chartPull (chartPullSame (L (e + 1)) (fun _ => γ (e + 1)) (fun _ => β e) (fun _ => 1) (γ e)
        (fun _ => rfl)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (L e) (γ e) (γ e) rfl) (LBIso.symm ⟨u e, (hL e).2⟩)
  have step : ∀ e (σ : LB.Sec (L e)), ∃ σ' : LB.Sec (L (e + 1)), Rel (β e) (u e) σ' σ := fun e σ =>
    GlobalTheory.FormalAlg.lift_step R I Y β hY n C H₀ s₀ hH hC γ rfl hγs e k (hk₀ k hk (e + 1)) (L e) (L (e + 1)) (u e)
      (hL e).1 (hL (e + 1)).1 (hL e).2 (hiso (e + 1)) σ
  choose f hf using step
  let σ : ∀ e, LB.Sec (L e) := fun e => Nat.rec (motive := fun e => LB.Sec (L e)) σ₀ (fun e s => f e s) e
  exact ⟨σ, rfl, fun e => hf e (σ e)⟩

private theorem exists_compatible_of_lift_aux (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (N : ∀ e, LB (Y e).left) (hN : ∀ e, (N e).IsLB) (p k c : ℕ) (hk : 1 ≤ k) (hc : (c : ℤ) = (p : ℤ) * (k : ℤ))
    (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N 0) p))
    (hs : VeryAmpleBy (Y 0).hom (GlobalTheory.AbLaw.pw (N 0) p) s)
    (hlift : ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))),
      (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k) →
        ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e))
    (v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e))) (hv : ∀ e, (v e).IsGen) :
    ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)),
      (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  have hEq : GlobalTheory.AbLaw.pw (N 0) c = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k := by
    rw [hc]
    exact congrArg (fun g => (⟨(N 0).ι, (N 0).U, g⟩ : LB (Y 0).left))
      (funext fun i => funext fun j => zpow_mul ((N 0).g i j) _ _)
  have h0 : ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N 0) c)),
      VeryAmpleBy (Y 0).hom (GlobalTheory.AbLaw.pw (N 0) c) s' := by
    rw [hEq]
    exact GlobalTheory.AbLaw.veryAmpleBy_pw _ _ _ _ n s (isLB_pw (hN 0) _) hs k hk
  obtain ⟨n', s0, hs0⟩ := h0
  have hL : ∀ e, (GlobalTheory.AbLaw.pw (N e) c).IsLB ∧ (v e).IsGen := fun e => ⟨isLB_pw (hN e) _, hv e⟩
  have hiso : LBIso (GlobalTheory.AbLaw.pw (N 0) c) (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k) :=
    hEq ▸ lbIso_refl (isLB_pw (hN 0) _)
  choose σ hσ0 hσ using fun j => hlift (fun e => GlobalTheory.AbLaw.pw (N e) c) v hL hiso (s0 j)
  refine ⟨n', fun e j => σ j e, fun e j => hσ j e, ?_⟩
  rintro (_ | e)
  · show VeryAmpleBy _ _ (fun j => σ j 0)
    simp only [hσ0]
    exact hs0
  · obtain ⟨j₀, hj, w, hw, hr⟩ := tower I Y β hβ (fun e => GlobalTheory.AbLaw.pw (N e) c) v hL (fun e j => σ j e)
      (fun e j => hσ j e) e
    simp only [hσ0] at hr
    exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
      (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _) _ _ _ _ j₀ hj _ _ w n' _ _ (hL _).1 (hL _).1
      ((isGen_iff _).2 hw) hr hs0

private theorem exists_veryAmple_compatible_aux :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
      ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left),
        (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) →
        ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → RelAmple (Y 0) (N 0) →
        ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ, c = a ∨ c = a + 1 →
          ∀ v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)),
            (∀ e, (v e).IsGen) →
            ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)),
              (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧
                ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  intro R _ _ I Y β hβ N hN hamp
  obtain ⟨d, hd1, hd⟩ := GlobalTheory.FormalAlg.ConsecPowers.exists_veryAmpleBy_pw_and_succ (R ⧸ I ^ (0 + 1)) (Y 0) (N 0) (hN 0) hamp
  obtain ⟨n₁, s₁, hs₁⟩ := hd d (Or.inl rfl)
  obtain ⟨n₂, s₂, hs₂⟩ := hd (d + 1) (Or.inr rfl)
  obtain ⟨k₁, hk₁⟩ := exists_lift_sections_tower_aux R I Y β hβ _ n₁ s₁ (isLB_pw (hN 0) _) hs₁
  obtain ⟨k₂, hk₂⟩ := exists_lift_sections_tower_aux R I Y β hβ _ n₂ s₂ (isLB_pw (hN 0) _) hs₂
  refine ⟨d * (1 + (d + 1) * max k₁ k₂), Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  have ht1 : ∀ m t : ℕ, 1 ≤ m → t ≤ 1 + m * t := fun m t hm => by nlinarith
  rintro c (rfl | rfl) v hv
  · exact exists_compatible_of_lift_aux R I Y β hβ N hN d (1 + (d + 1) * max k₁ k₂) _ (by omega) (by push_cast; ring)
      n₁ s₁ hs₁ (hk₁ _ (le_trans (le_max_left _ _) (ht1 _ _ (by omega)))) v hv
  · exact exists_compatible_of_lift_aux R I Y β hβ N hN (d + 1) (1 + d * max k₁ k₂) _ (by omega) (by push_cast; ring)
      n₂ s₂ hs₂ (hk₂ _ (le_trans (le_max_right _ _) (ht1 _ _ hd1))) v hv

private theorem isClosedImmersion_lift_id_aux {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : 𝟙 X ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R))) :
    IsClosedImmersion (pullback.lift (𝟙 X) f h) := by
  have hi : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]
    infer_instance
  have e : pullback.lift (𝟙 X) f h = inv (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id R)))) :=
    IsIso.eq_inv_of_inv_hom_id (pullback.lift_fst _ _ _)
  rw [e]
  infer_instance

private theorem veryAmpleBy_of_lbIso_aux {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {H H'' : LB X} (hH : H.IsLB) (hH'' : H''.IsLB) (hI : LBIso H H'') {n : ℕ} {s : Fin (n + 1) → LB.Sec H}
    (hs : VeryAmpleBy f H s) : ∃ s'' : Fin (n + 1) → LB.Sec H'', VeryAmpleBy f H'' s'' := by
  obtain ⟨w, hw⟩ := LBIso.trans hH'' hH (pull_isLB hH _) (LBIso.symm hI) (LBIso.symm (GlobalTheory.lbIso_pull_id hH))
  choose s'' hs'' using fun j => (GlobalTheory.SecPullIso.section_pull X X (𝟙 X) H H'' w hH hH'' hw (s j)).1.exists
  exact ⟨s'', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R (RingHom.id R) X f (𝟙 X)
    (by rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]; simp)
    (isClosedImmersion_lift_id_aux f _) H'' w s'' hH'' hw fun j => hs'' j⟩

private theorem formalAlgebraisation_schemes_aux : GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro R _ _ I hI Y β hβ hY N hN hNN hA
  choose v hv using hNN
  obtain ⟨a, ha1, hlift⟩ := exists_veryAmple_compatible_aux R I Y β hβ N hN hA
  have hpw : ∀ (c : ℤ) (e : ℕ), ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)),
      wa.IsGen ∧ ∀ (z : (Y e).left) (k : (N (e + 1)).ι) (k' : (N e).ι), β e z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        Geo.Tor.gw wa (𝟙 _) z k k' = Geo.Tor.gw (v e) (𝟙 _) z k k' ^ c := fun c e => by
    obtain ⟨wa, h1, h2⟩ := GlobalTheory.FormalAlg.lbIso_pw_pull_gw (Y (e + 1)).left (Y e).left (β e) (N (e + 1)) (N e) (v e) (hv e) c
    exact ⟨wa, h1, fun z k k' hk hk' => h2 (Y e).left (𝟙 _) z k k' hk hk'⟩
  choose va hva hvaw using hpw (a : ℤ)
  choose vb hvb hvbw using hpw ((a + 1 : ℕ) : ℤ)
  obtain ⟨n, s, hsRel, hsVA⟩ := hlift a (Or.inl rfl) va hva
  obtain ⟨n₂, s₂, hs₂Rel, hs₂VA⟩ := hlift (a + 1) (Or.inr rfl) vb hvb
  obtain ⟨B, H', s', b, w, hH', hVA', hpb, hcomp, hw, -⟩ := GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete R I hI Y β hβ
    (fun e => GlobalTheory.AbLaw.pw (N e) a) va (fun e => ⟨isLB_pw (hN e) _, hva e⟩) n s hsRel (hsVA 0)
  have hBp : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy R B.left B.hom ⟨H', hH', n, s', hVA'⟩
  obtain ⟨M₂, s₂', w', hM₂, hw'⟩ := exists_lb_of_generated_system_proper_aux R I hI B hBp Y β b hpb hcomp
    (fun e => GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) vb (fun e => ⟨isLB_pw (hN e) _, hvb e⟩) n₂ s₂ hs₂Rel
    (fun e => (hs₂VA e).1)
  have c1 : ∀ e z k l' l, b e z ∈ H'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ (a : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvaw e z l' l h2 h3]
    exact GlobalTheory.FormalAlg.gw_comp_of_rel B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) H'
      (GlobalTheory.AbLaw.pw (N (e + 1)) a) (GlobalTheory.AbLaw.pw (N e) a) (w (e + 1)) (va e) (w e) (Fin (n + 1)) s' (s (e + 1)) (s e)
      (fun j => (hw (e + 1)).2 j) (fun j => hsRel e j) (fun j => (hw e).2 j) (hsVA e).1 z k l' l h1 h2 h3
  have c2 : ∀ e z k l' l, b e z ∈ M₂.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w' e) (𝟙 _) z k l =
        Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ ((a + 1 : ℕ) : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvbw e z l' l h2 h3]
    exact GlobalTheory.FormalAlg.gw_comp_of_rel B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) M₂
      (GlobalTheory.AbLaw.pw (N (e + 1)) ((a + 1 : ℕ) : ℤ)) (GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) (w' (e + 1)) (vb e) (w' e)
      (Fin (n₂ + 1)) s₂' (s₂ (e + 1)) (s₂ e)
      (fun j => (hw' (e + 1)).2 j) (fun j => hs₂Rel e j) (fun j => (hw' e).2 j) (hs₂VA e).1 z k l' l h1 h2 h3
  have hiso := lbIso_pw_cross_aux R I hI B hBp Y β b hpb hcomp N v hN (a : ℤ) ((a + 1 : ℕ) : ℤ) H' M₂ hH' hM₂ w w'
    (fun e => ⟨(hw e).1, (hw' e).1⟩) c1 c2
  have hcast : ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1 := by push_cast; rfl
  rw [hcast] at hiso
  have hM : (GlobalTheory.AbLaw.tw M₂ H' (-1)).IsLB := isLB_tw hM₂ hH' _
  have hH'M : LBIso H' (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M₂ H' (-1)) a) := cancel_pw_aux.2 B.left H' M₂ a hH' hM₂ hiso
  have hNM : ∀ e, LBIso (N e) ((GlobalTheory.AbLaw.tw M₂ H' (-1)).pull (b e)) := fun e =>
    cancel_pw_aux.1 B.left (Y e).left (b e) H' M₂ (N e) a hH' hM₂ (hN e) ⟨w e, (hw e).1⟩
      (hcast ▸ ⟨w' e, (hw' e).1⟩)
  obtain ⟨s'', hs''⟩ := veryAmpleBy_of_lbIso_aux B.hom hH' (isLB_pw hM _) hH'M hVA'
  exact ⟨B, GlobalTheory.AbLaw.tw M₂ H' (-1), b, hBp, hM,
    (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B _ hM).2 ⟨a, ha1, n, s'', hs''⟩, hpb, hcomp, hNM⟩

end GlobalTheory.FormalAlg
end
end

namespace GlobalTheory

theorem formalAlgebraisation : GlobalTheory.Published.FormalAlgebraisation :=
  ⟨GlobalTheory.T.formalAlgebraisation_morphisms', GlobalTheory.FormalAlg.formalAlgebraisation_schemes_aux⟩

end GlobalTheory

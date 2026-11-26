module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.JPMemAwayP
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ProdMemSpan
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

theorem prod_mem_span {O Y ι : Type} [CommRing O] [CommRing Y] [Algebra O Y] (t : Finset ι) (A : ι → Set Y) (x : ι → Y)
    (hx : ∀ i ∈ t, x i ∈ Submodule.span O (A i)) :
    ∏ i ∈ t, x i ∈ Submodule.span O {y | ∃ a : ι → Y, (∀ i ∈ t, a i ∈ A i) ∧ y = ∏ i ∈ t, a i} := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    apply Submodule.subset_span
    exact ⟨fun _ => 1, by simp, by simp⟩
  | insert j t hj ih =>
    have h1 : x j ∈ Submodule.span O (A j) := hx j (Finset.mem_insert_self j t)
    have h2 := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert hj]
    have h3 := Submodule.mul_mem_mul h1 h2
    rw [Submodule.span_mul_span] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨b, hb, y, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨Function.update a j b, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simpa using hb
      · have hne : i ≠ j := fun h => hj (h ▸ hi)
        simpa [Function.update_apply, hne] using ha i hi
    · rw [Finset.prod_insert hj]
      simp only [Function.update_apply, if_pos rfl]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ j := fun h => hj (h ▸ hi)
      simp [hne]

theorem tens_span {O Y ι : Type} [CommRing O] [CommRing Y] [Algebra O Y] [Fintype ι] {X : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module O (X i)] (φ : ∀ i, X i →ₗ[O] Y) (M : ∀ i, Submodule O (X i))
    (R : ∀ i, X i → Prop) (h : ∀ i, M i ≤ Submodule.span O {x | x ∈ M i ∧ R i x}) (F : ∀ i, X i)
    (hF : ∀ i, F i ∈ M i) :
    ∏ i, φ i (F i) ∈
      Submodule.span O {y | ∃ F' : ∀ i, X i, (∀ i, F' i ∈ M i ∧ R i (F' i)) ∧ y = ∏ i, φ i (F' i)} := by
  classical
  have key := prod_mem_span (O := O) Finset.univ (fun i => φ i '' {x | x ∈ M i ∧ R i x})
    (fun i => φ i (F i)) (by
      intro i _
      rw [Submodule.span_image]
      exact Submodule.mem_map_of_mem (h i (hF i)))
  refine Submodule.span_mono ?_ key
  rintro y ⟨a, ha, rfl⟩
  have hex : ∀ i, ∃ z, (z ∈ M i ∧ R i z) ∧ φ i z = a i := fun i => ha i (Finset.mem_univ i)
  choose F' hF' hF'' using hex
  exact ⟨F', hF', by simp [hF'']⟩

section One

variable {O Kf LL : Type} [CommRing O] [Field Kf] [Algebra O Kf] [Field LL] (e : LL →+* Kf)

theorem rowAct_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {k n : ℕ}
    (U : Matrix (Fin k) (Fin k) R) (f : MvPolynomial (Fin k × Fin n) R) :
    rowAct S (U.map φ) (map φ f) = map φ (rowAct R U f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [rowAct, map_sum, Matrix.map_apply]

theorem glMap_inv {k : ℕ} (g : GL (Fin k) LL) :
    ((g : Matrix (Fin k) (Fin k) LL).map e)⁻¹ = ((g⁻¹ : GL (Fin k) LL) : Matrix (Fin k) (Fin k) LL).map e := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul]
  simp

theorem glMap_det {k : ℕ} (g : GL (Fin k) LL) : IsUnit ((g : Matrix (Fin k) (Fin k) LL).map e).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := ((g⁻¹ : GL (Fin k) LL) : Matrix (Fin k) (Fin k) LL).map e)
  rw [← Matrix.map_mul]
  simp

theorem dl_rat (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : GL (Fin (m + 1)) LL) :
    Dl0 O m lam (colSpan O ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) ≤
      Submodule.span O {F | F ∈ Dl0 O m lam (colSpan O ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) ∧
        ∃ Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL, map e Q = F} := by
  set gK : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := (g : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e with hgK
  have hdet : IsUnit gK.det := glMap_det e g
  rw [dw_eq hinj m lam hlam gK hdet]
  let T : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O →ₗ[O] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf :=
    ((LinearMap.lsmul Kf _ (gK.det ^ (-(lam (Fin.last m))))).restrictScalars O) ∘ₗ
      ((rowAct Kf (n := m + 1) gK⁻¹).toLinearMap.restrictScalars O) ∘ₗ
        (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
  have hT : ∀ x, T x = gK.det ^ (-(lam (Fin.last m))) • rowAct Kf gK⁻¹ (map (algebraMap O Kf) x) := fun x => rfl
  have hmem : ∀ f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam), T f ∈ deltaLTw O Kf m lam gK := by
    intro f hf
    refine ⟨rowAct Kf gK⁻¹ (map (algebraMap O Kf) f), ⟨f, hf, ?_⟩, rfl⟩
    change map (algebraMap O Kf) f = rowAct Kf gK (rowAct Kf gK⁻¹ (map (algebraMap O Kf) f))
    rw [ldlat_rowAct_inv_left rowActMul gK hdet]
  have key : weyl O (m + 1) (m + 1) le_rfl (nuOf lam) ≤
      (Submodule.span O {F | F ∈ deltaLTw O Kf m lam gK ∧
        ∃ Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL, map e Q = F}).comap T := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨wd, rfl⟩
    apply Submodule.subset_span
    refine ⟨hmem _ (Submodule.subset_span ⟨wd, rfl⟩), ?_⟩
    refine ⟨C ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ (-(lam (Fin.last m)))) *
      rowAct LL ((g⁻¹ : GL (Fin (m + 1)) LL) : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)
        (applyWord LL wd (hw LL le_rfl (nuOf lam))), ?_⟩
    rw [hT, map_mul, map_C, ← rowAct_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map, ← lclosedeq_applyWord_map,
      lclosedeq_hw_map, ← glMap_inv, map_zpow₀, ← smul_eq_C_mul]
    congr 2
    rw [RingHom.map_det]; rfl
  rintro _ ⟨F0, ⟨f, hf, hfe⟩, rfl⟩
  have hfe' : map (algebraMap O Kf) f = rowAct Kf gK F0 := hfe
  have hF0 : F0 = rowAct Kf gK⁻¹ (map (algebraMap O Kf) f) := by
    rw [hfe', ldlat_rowAct_inv_right rowActMul gK hdet]
  have := key hf
  rw [Submodule.mem_comap, hT, ← hF0] at this
  exact this

theorem htenW_rat (hinj : Function.Injective (algebraMap O Kf)) {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hdom : ∀ s, Antitone (lamAt lam0 s)) (g : Fin n' → GL (Fin (m + 1)) LL) :
    HtenW O lam0 (fun s => colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) ≤
      Submodule.span O {z | z ∈ HtenW O lam0 (fun s => colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) ∧
        ∃ Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL, map e Q = z} := by
  have hdef : HtenW O lam0 (fun s => colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) =
      Submodule.span O {P | ∃ F : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
        (∀ s, F s ∈ Dl0 O m (lamAt lam0 s) (colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e))) ∧
          P = ∏ s, blockEmb Kf s (F s)} := rfl
  conv_lhs => rw [hdef]
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  have h1 := tens_span (O := O) (Y := MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
    (X := fun _ : Fin n' => MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (fun s => (blockEmb Kf s).toLinearMap.restrictScalars O)
    (fun s => Dl0 O m (lamAt lam0 s) (colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)))
    (fun _ x => ∃ Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL, map e Q = x)
    (fun s => dl_rat e hinj m (lamAt lam0 s) (hdom s) (g s)) F hF
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨F', hF', rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hdef]
    exact Submodule.subset_span ⟨F', fun s => (hF' s).1, rfl⟩
  · choose Q hQ using fun s => (hF' s).2
    refine ⟨∏ s, blockEmb LL s (Q s), ?_⟩
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    show map e (rename _ (Q s)) = rename _ (F' s)
    rw [map_rename, hQ]

end One

section All

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def RatBasisAt (L : G.P.Tup) : Prop :=
  ∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)), ∃ g : GL (Fin (G.P.m + 1)) LL,
    extO G.O (G.P.ι v) (G.P.σ v) s.val (L v) =
      colSpan G.O ((g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) LL).map e)

def RatBasis : Prop := ∀ L : G.P.Tup, G.P.IsLatTup L → RatBasisAt G e L

theorem htupW_rat (L : G.P.Tup) (hB : RatBasisAt G e L) :
    G.P.HtupW L ≤ Submodule.span G.O {ξ | ξ ∈ G.P.HtupW L ∧ RatX G e ξ} := by
  choose g hg using hB
  have hdef : G.P.HtupW L = Submodule.span G.O {X | ∃ F : ∀ v, Pol G v,
      (∀ v, F v ∈ HtenW G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v)) ∧
        X = ∏ v, G.P.vEmb v (F v)} := rfl
  conv_lhs => rw [hdef]
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  have hv : ∀ v, (HtenW G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v)) ≤
      Submodule.span G.O {z | (z ∈ HtenW G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v)) ∧
        ∃ Q : MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL, map e Q = z} := by
    intro v
    have e1 : (fun s : Fin (G.P.n' v) => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v)) =
        fun s => colSpan G.O ((g v s : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) LL).map e) := funext (hg v)
    rw [e1]
    exact htenW_rat e (lb_inj G v) (G.P.lam0 v) (je_dom G v) (g v)
  have h1 := tens_span (O := G.O) (Y := G.P.Xsp) (X := fun v => Pol G v)
    (fun v => (G.P.vEmb v).toLinearMap.restrictScalars G.O)
    (fun v => HtenW G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v))
    (fun v x => ∃ Q : MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL, map e Q = x)
    hv F hF
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨F', hF', rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hdef]
    exact Submodule.subset_span ⟨F', fun v => (hF' v).1, rfl⟩
  · choose Q hQ using fun v => (hF' v).2
    refine ⟨∏ v, rename (fun x => (⟨v, x⟩ : Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1)))) (Q v), ?_⟩
    rw [map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    show map e (rename _ (Q v)) = rename _ (F' v)
    rw [map_rename, hQ]

end All

end Formalism.L2.G.Cmp
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmApply
section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsFib
namespace Formalism.L2.G.Cmp

open Formalism.UG

structure Fib {G Gp : Type} [Group G] [Group Gp] (K K' : Subgroup G) (Kp : Subgroup Gp) where
  j : Gp →* G
  pr : G →* Gp
  pr_j : ∀ g, pr (j g) = g
  j_mem : ∀ g, j g ∈ K'
  K_iff : ∀ x, x ∈ K ↔ x ∈ K' ∧ pr x ∈ Kp

namespace Fib

variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)

def mkC (S : Subgroup G) (a : G) : ClassSet H S :=
  Quotient.mk'' a

theorem mk_eq_iff (S : Subgroup G) (a b : G) :
    (mkC H S a = mkC H S b) ↔ ∃ h ∈ H, ∃ κ ∈ S, b = h * a * κ := by
  unfold mkC
  exact @DoubleCoset.eq _ _ _ _ a b

theorem K'_split (x : G) (hx : x ∈ K') : (X.j (X.pr x))⁻¹ * x ∈ K := by
  rw [X.K_iff]
  refine ⟨K'.mul_mem (K'.inv_mem (X.j_mem _)) hx, ?_⟩
  rw [map_mul, map_inv, X.pr_j, inv_mul_cancel]
  exact Kp.one_mem

variable (y : ClassSet H K' → G) (hy : ∀ i, mkC H K' (y i) = i) (hp : ∀ i, X.pr (y i) = 1)


include hy hp in
theorem cls_iff (i i' : ClassSet H K') (g g' : Gp)
    (hy : ∀ i, mkC H K' (y i) = i) (hp : ∀ i, X.pr (y i) = 1) :
    mkC H K (y i * X.j g) = mkC H K (y i' * X.j g') ↔
      i = i' ∧ ∃ γ ∈ H, (y i)⁻¹ * γ * y i ∈ K' ∧ g'⁻¹ * (X.pr γ * g) ∈ Kp := by
  rw [mk_eq_iff]
  constructor
  · rintro ⟨h, hh, κ, hκ, he⟩
    have hκ' := (X.K_iff κ).1 hκ
    have hi : i = i' := by
      rw [← hy i, ← hy i', mk_eq_iff]
      refine ⟨h, hh, X.j g * κ * (X.j g')⁻¹,
        K'.mul_mem (K'.mul_mem (X.j_mem g) hκ'.1) (K'.inv_mem (X.j_mem g')), ?_⟩
      calc y i' = (y i' * X.j g') * (X.j g')⁻¹ := by group
        _ = h * (y i * X.j g) * κ * (X.j g')⁻¹ := by rw [he]
        _ = h * y i * (X.j g * κ * (X.j g')⁻¹) := by group
    subst hi
    have hh' : h = (y i * X.j g') * κ⁻¹ * (y i * X.j g)⁻¹ := by rw [he]; group
    have hz : (y i)⁻¹ * h * y i = X.j g' * κ⁻¹ * (X.j g)⁻¹ := by rw [hh']; group
    refine ⟨rfl, h, hh, ?_, ?_⟩
    · rw [hz]
      exact K'.mul_mem (K'.mul_mem (X.j_mem _) (K'.inv_mem hκ'.1)) (K'.inv_mem (X.j_mem _))
    · rw [hh']
      simp only [map_mul, map_inv, X.pr_j, hp]
      convert Kp.inv_mem hκ'.2 using 1
      group
  · rintro ⟨rfl, γ, hγ, hz, hg⟩
    refine ⟨γ, hγ, (y i * X.j g)⁻¹ * γ⁻¹ * (y i * X.j g'), ?_, by group⟩
    rw [X.K_iff]
    have e : (y i * X.j g)⁻¹ * γ⁻¹ * (y i * X.j g') =
        (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i)⁻¹ * X.j g' := by group
    rw [e]
    refine ⟨K'.mul_mem (K'.mul_mem (K'.inv_mem (X.j_mem _)) (K'.inv_mem hz)) (X.j_mem _), ?_⟩
    simp only [map_mul, map_inv, X.pr_j, hp]
    convert Kp.inv_mem hg using 1
    group


include hy in
theorem cls_surj (x : G) (hy : ∀ i, mkC H K' (y i) = i) :
    ∃ i g, mkC H K (y i * X.j g) = mkC H K x := by
  obtain ⟨h, hh, κ, hκ, he⟩ := (mk_eq_iff H K' (y (mkC H K' x)) x).1 (hy _)
  refine ⟨mkC H K' x, X.pr κ, (mk_eq_iff H K _ _).2
    ⟨h, hh, (X.j (X.pr κ))⁻¹ * κ, X.K'_split κ hκ, ?_⟩⟩
  conv_lhs => rw [he]
  group


include hp in
theorem stab_iff (i : ClassSet H K') (g : Gp) (γ : G)
    (hp : ∀ i, X.pr (y i) = 1) :
    (y i * X.j g)⁻¹ * γ * (y i * X.j g) ∈ K ↔ (y i)⁻¹ * γ * y i ∈ K' ∧ g⁻¹ * (X.pr γ * g) ∈ Kp := by
  have hz : (y i * X.j g)⁻¹ * γ * (y i * X.j g) = (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g := by
    group
  rw [hz, X.K_iff]
  have hjg := X.j_mem g
  have h1 : (X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g ∈ K' ↔ (y i)⁻¹ * γ * y i ∈ K' := by
    constructor
    · intro h
      have h2 := K'.mul_mem (K'.mul_mem hjg h) (K'.inv_mem hjg)
      have e : X.j g * ((X.j g)⁻¹ * ((y i)⁻¹ * γ * y i) * X.j g) * (X.j g)⁻¹ =
          (y i)⁻¹ * γ * y i := by group
      rwa [e] at h2
    · intro h
      exact K'.mul_mem (K'.mul_mem (K'.inv_mem hjg) h) hjg
  rw [h1]
  simp only [map_mul, map_inv, X.pr_j, hp, inv_one, one_mul, mul_one, mul_assoc]

end Fib

end Formalism.L2.G.Cmp
end

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

def bcE {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (e : A ≃+* B) : GL n A ≃* GL n B :=
  Units.mapEquiv (RingEquiv.mapMatrix e).toMulEquiv

theorem bcE_symm_apply {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (e : A ≃+* B) (g : GL n B)
    (a b : n) : ((bcE e).symm g : Matrix n n A) a b = e.symm ((g : Matrix n n B) a b) := rfl

theorem castGL_symm_apply {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin b) R) (x y : Fin a) :
    ((castGL h R).symm g : Matrix (Fin a) (Fin a) R) x y = (g : Matrix (Fin b) (Fin b) R) (Fin.cast h x) (Fin.cast h y) := by
  first
  | rfl
  | (subst h; rfl)
  | simp [castGL]

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

abbrev fstV (I : LocId L p nV W Qq) (v : Fin nV) : E ⊗[F] (I.plc v).adicCompletion F →+* (I.plc v).adicCompletion F :=
  (RingHom.fst _ _).comp (I.spl (I.plc v) (I.pl v).2).toRingHom

abbrev frV (I : LocId L p nV W Qq) (v : Fin nV) : GL (Fin R.k) ((I.plc v).adicCompletion F) := I.fr (I.plc v) (I.pl v).2

def toF (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (v : Fin nV) :
    GL (Fin (m + 1)) Qq ≃* GL (Fin R.k) ((I.plc v).adicCompletion F) :=
  ((castGL hk Qq).trans (bcE (I.eQ v))).trans (MulAut.conj (frV I v))

theorem toF_symm (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (v : Fin nV)
    (X : GL (Fin R.k) ((I.plc v).adicCompletion F)) :
    (toF I hk v).symm X = (castGL hk Qq).symm ((bcE (I.eQ v)).symm ((frV I v)⁻¹ * X * frV I v)) := rfl

abbrev GA (sp : Spaces R F E) : Type := UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)

def prP (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) : GA sp →* (Fin nV → GL (Fin (m + 1)) Qq) :=
  MonoidHom.pi fun v => (toF I hk v).symm.toMonoidHom.comp
    ((bc (fstV I v)).comp ((bc (prV (E := E) (I.plc v))).comp (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subtype))

theorem prP_apply (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (x : GA sp) (v : Fin nV) :
    prP I hk x v = (toF I hk v).symm (bc (fstV I v) (bc (prV (E := E) (I.plc v)) (x : GL (Fin R.k) _))) := rfl

def jQ (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) {m : ℕ} (hk : m + 1 = R.k) :
    (Fin nV → GL (Fin (m + 1)) Qq) →* GA sp :=
  (jP I hdet).comp (MonoidHom.pi fun v => (toF I hk v).toMonoidHom.comp (Pi.evalMonoidHom _ v))

theorem prP_jQ (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) {m : ℕ} (hk : m + 1 = R.k)
    (g : Fin nV → GL (Fin (m + 1)) Qq) : prP I hk (jQ I hdet hk g) = g := by
  funext v
  rw [prP_apply]
  have := jP_at I hdet (fun v => toF I hk v (g v)) v
  show (toF I hk v).symm (bc (fstV I v) (bc (prV (E := E) (I.plc v)) (jP I hdet (fun v => toF I hk v (g v)) : GL (Fin R.k) _))) = g v
  rw [this, MulEquiv.symm_apply_apply]

def HypAtP (I : LocId L p nV W Qq) : Prop :=
  ∀ (v : Fin nV) (x : GL (Fin R.k) (E ⊗[F] (I.plc v).adicCompletion F)),
    x ∈ UPts sp.cm.sig sp.gram0 ((I.plc v).adicCompletion F) →
    (x ∈ L.Uloc (I.plc v) ↔
      (∀ a b, (((frV I v)⁻¹ * bc (fstV I v) x * frV I v : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F) ∧
      ∀ a b, ((((frV I v)⁻¹ * bc (fstV I v) x * frV I v)⁻¹ : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F)

theorem toF_symm_stab (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (v : Fin nV)
    (X : GL (Fin R.k) ((I.plc v).adicCompletion F)) :
    (toF I hk v).symm X ∈ stabStd (k := m + 1) (Qq := Qq) W ↔
      (∀ a b, (((frV I v)⁻¹ * X * frV I v : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F) ∧
      ∀ a b, ((((frV I v)⁻¹ * X * frV I v)⁻¹ : GL (Fin R.k) _) : Matrix (Fin R.k) (Fin R.k) _) a b ∈
        (I.plc v).adicCompletionIntegers F := by
  rw [stabStd_iff, ← map_inv, toF_symm, toF_symm]
  have key : ∀ M : GL (Fin R.k) ((I.plc v).adicCompletion F),
      (∀ a b, ((castGL hk Qq).symm ((bcE (I.eQ v)).symm M) : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b ∈
        (algebraMap W Qq).range) ↔ ∀ a b, (M : Matrix (Fin R.k) (Fin R.k) _) a b ∈ (I.plc v).adicCompletionIntegers F := by
    intro M
    have h1 : ∀ a b, ((castGL hk Qq).symm ((bcE (I.eQ v)).symm M) : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b ∈
        (algebraMap W Qq).range ↔ (M : Matrix (Fin R.k) (Fin R.k) _) (Fin.cast hk a) (Fin.cast hk b) ∈
          (I.plc v).adicCompletionIntegers F := by
      intro a b
      rw [castGL_symm_apply, bcE_symm_apply]
      have := I.completion_integers_iff v ((I.eQ v).symm ((M : Matrix (Fin R.k) (Fin R.k) _) (Fin.cast hk a) (Fin.cast hk b)))
      rw [RingEquiv.apply_symm_apply] at this
      exact this
    constructor
    · intro h a b
      have := (h1 (Fin.cast hk.symm a) (Fin.cast hk.symm b)).1 (h _ _)
      simpa using this
    · intro h a b
      exact (h1 a b).2 (h _ _)
  have e : (frV I v)⁻¹ * X⁻¹ * frV I v = ((frV I v)⁻¹ * X * frV I v)⁻¹ := by group
  rw [key, e, key]

def fibP (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) {m : ℕ} (hk : m + 1 = R.k) (hH : HypAtP I) :
    Fib (L.U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      ((Formalism.L2.Herm.awayFrom₂ L p).subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      (stabTup (nV := nV) (k := m + 1) (Qq := Qq) W) where
  j := jQ I hdet hk
  pr := prP I hk
  pr_j := prP_jQ I hdet hk
  j_mem := fun g => Subgroup.mem_subgroupOf.2 (jP_mem_awayP I hdet _)
  K_iff := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, L.U_eq, mem_stabTup]
    have hloc : ∀ v : Fin nV, bc (prV (E := E) (I.plc v)) (x : GL (Fin R.k) _) ∈ L.Uloc (I.plc v) ↔
        prP I hk x v ∈ stabStd (k := m + 1) (Qq := Qq) W := by
      intro v
      rw [prP_apply, toF_symm_stab]
      exact hH v _ (Formalism.UG.P.afsplit_bc_mem sp.cm.sig sp.gram0 (I.plc v) _ x.2)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Subgroup.mem_inf.2 ⟨h1, ?_⟩, fun v => (hloc v).1 (h2 _)⟩
      simp only [Subgroup.mem_iInf]
      intro v _
      exact h2 v
    · rintro ⟨h1, h2⟩
      obtain ⟨h3, h4⟩ := Subgroup.mem_inf.1 h1
      refine ⟨h3, fun v => ?_⟩
      by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
      · obtain ⟨v', rfl⟩ : ∃ v', I.plc v' = v := ⟨I.pl.symm ⟨v, hv⟩, by simp [LocId.plc]⟩
        exact (hloc v').2 (h2 v')
      · simp only [Subgroup.mem_iInf] at h4
        exact h4 v hv

end Formalism.L2.G.Cmp
end
end

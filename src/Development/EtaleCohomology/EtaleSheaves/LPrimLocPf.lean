module

public import Development.EtaleCohomology.EtaleSheaves.HensCut
public import Development.EtaleCohomology.EtaleSheaves.TorEtPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LPrimLocPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_prim_locPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

section Alg
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A]

theorem prim_pow_q (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  obtain ⟨r, hr⟩ := h
  have h2 := congrArg (Polynomial.aeval ζ.1) hr
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one] at h2
  exact sub_eq_zero.1 h2

theorem prim_isPrim {B : Type} [CommRing B] [IsDomain B] (φ : A →+* B) (ζ : Prim q A) :
    IsPrimitiveRoot (φ ζ.1) q := by
  have hq : IsUnit (q : B) := by simpa using ζ.2.1.map φ
  haveI : NeZero (q : B) := ⟨hq.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := (Prim.map φ ζ).2.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h
  exact h

theorem unit_sub (ζ : Prim q A) {j : ℕ} (hj0 : 0 < j) (hjq : j < q) : IsUnit (ζ.1 ^ j - 1) := by
  by_contra h
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits h
  have hp := prim_isPrim (Ideal.Quotient.mk m) ζ
  have h0 : Ideal.Quotient.mk m (ζ.1 ^ j - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
  rw [map_sub, map_pow, map_one, sub_eq_zero] at h0
  exact hp.pow_ne_one_of_pos_of_lt (Nat.pos_iff_ne_zero.1 hj0) hjq h0

end Alg

section Idem
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (x : A)

def yy (a : ℕ) : A := x * ζ.1 ^ (a * (q - 1))
def ee (a : ℕ) : A := (ζ.2.1.unit⁻¹ : Aˣ) * ∑ j ∈ Finset.range q, (yy ζ x a) ^ j

theorem zeta_mul_yy (a : ℕ) : ζ.1 ^ a * yy ζ x a = x := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  have hz : ζ.1 ^ (k + 1) = 1 := by rw [show k + 1 = q by omega]; exact prim_pow_q ζ
  unfold yy
  rw [show q - 1 = k by omega]
  calc ζ.1 ^ a * (x * ζ.1 ^ (a * k)) = x * ζ.1 ^ (a + a * k) := by rw [pow_add]; ring
    _ = x * (ζ.1 ^ (k + 1)) ^ a := by rw [← pow_mul]; ring_nf
    _ = x := by rw [hz, one_pow, mul_one]

theorem ee_kill (hx : x ^ q = 1) (a : ℕ) : ee ζ x a * (x - ζ.1 ^ a) = 0 := by
  have h1 : x - ζ.1 ^ a = ζ.1 ^ a * (yy ζ x a - 1) := by
    rw [mul_sub, zeta_mul_yy, mul_one]
  have hy : (yy ζ x a) ^ q = 1 := by
    unfold yy
    rw [mul_pow, hx, ← pow_mul, mul_comm (a * (q - 1)) q, pow_mul, prim_pow_q, one_pow, one_mul]
  unfold ee
  rw [h1]
  calc _ = ((ζ.2.1.unit⁻¹ : Aˣ) : A) * ζ.1 ^ a * ((∑ j ∈ Finset.range q, (yy ζ x a) ^ j) * (yy ζ x a - 1)) := by ring
    _ = 0 := by rw [geom_sum_mul, hy, sub_self, mul_zero]

theorem inner_sum {j : ℕ} (hj0 : 0 < j) (hjq : j < q) :
    ∑ a ∈ Finset.range q, (ζ.1 ^ ((q - 1) * j)) ^ a = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hz : ζ.1 ^ (k + 1) = 1 := by rw [show k + 1 = q by omega]; exact prim_pow_q ζ
  have hik : i < k := by omega
  have e1 : (q - 1) * (i + 1) = (k + 1) * i + (k - i) := by
    rw [show q - 1 = k by omega]; zify [hik.le]; ring
  have hw : ζ.1 ^ ((q - 1) * (i + 1)) = ζ.1 ^ (k - i) := by
    rw [e1, pow_add, pow_mul, hz, one_pow, one_mul]
  have hu : IsUnit (ζ.1 ^ (k - i) - 1) := unit_sub ζ (by omega) (by omega)
  have hwq : (ζ.1 ^ (k - i)) ^ q = 1 := by rw [← pow_mul, mul_comm, pow_mul, prim_pow_q, one_pow]
  rw [hw]
  have h2 := geom_sum_mul (ζ.1 ^ (k - i)) q
  rw [hwq, sub_self] at h2
  exact (hu.mul_left_eq_zero).1 h2

theorem ee_sum : ∑ a ∈ Finset.range q, ee ζ x a = 1 := by
  unfold ee yy
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hterm : ∀ j ∈ Finset.range q, ∑ a ∈ Finset.range q, (x * ζ.1 ^ (a * (q - 1))) ^ j =
      x ^ j * ∑ a ∈ Finset.range q, (ζ.1 ^ ((q - 1) * j)) ^ a := by
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [inner_sum ζ (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.pos_of_ne_zero (NeZero.ne q))) h

end Idem

theorem ee_nil {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : ℕ) (ha : ¬ a.Coprime q) :
    IsNilpotent (ee ζ ξ.1 a) := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  intro p hp
  haveI : Ideal.IsPrime p := hp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  by_contra hne
  have hk := congrArg (Ideal.Quotient.mk p) (ee_kill ζ ξ.1 (prim_pow_q ξ) a)
  rw [map_mul, map_zero, map_sub, map_pow] at hk
  have he : Ideal.Quotient.mk p ξ.1 = (Ideal.Quotient.mk p ζ.1) ^ a :=
    sub_eq_zero.1 ((mul_eq_zero.1 hk).resolve_left hne)
  have hξ := prim_isPrim (Ideal.Quotient.mk p) ξ
  have hζ := prim_isPrim (Ideal.Quotient.mk p) ζ
  rw [he] at hξ
  exact ha ((hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) a).1 hξ)

theorem algPow : AlgPow := by
  intro q _ A _ ζ ξ
  refine ⟨Set.range fun a : Fin q => ee ζ ξ.1 a, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one, ← ee_sum ζ ξ.1, Finset.sum_range]
    exact Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨a, rfl⟩
  · rintro f ⟨a, rfl⟩
    by_cases hc : (a : ℕ).Coprime q
    · refine ⟨ZMod.unitOfCoprime a hc, 1, ?_⟩
      have hv : ((ZMod.unitOfCoprime (a : ℕ) hc : (ZMod q)ˣ) : ZMod q).val = a := by
        rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt a.2]
      rw [hv, pow_one]
      exact ee_kill ζ ξ.1 (prim_pow_q ξ) a
    · obtain ⟨n, hn⟩ := ee_nil ζ ξ a hc
      exact ⟨1, n, by rw [hn, zero_mul]⟩

theorem loc_of_span {U : Scheme.{0}} (s : Set Γ(U, ⊤)) (hs : Ideal.span s = ⊤) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ f ∈ s, ∀ (V : Scheme.{0}) (g : V ⟶ U), IsUnit (g.appTop.hom f) → P V g) : Loc U P := by
  let O : s → U.Opens := fun f => U.basicOpen f.1
  have hO : TopologicalSpace.IsOpenCover O := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, U.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := U.openCoverOfIsOpenCover O hO
  let S : Sieve U := {
    arrows := fun V g => ∃ f ∈ s, IsUnit (g.appTop.hom f)
    downward_closed := by
      rintro V W g ⟨f, hf, hu⟩ k
      exact ⟨f, hf, (show IsUnit (k.appTop.hom (g.appTop.hom f)) from hu.map _)⟩ }
  have hgen : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ≤ S := by
    rintro W g ⟨Y, k, _, ⟨i⟩, rfl⟩
    refine (S.downward_closed ?_ k)
    refine ⟨i.1, i.2, ?_⟩
    have hle : (O i).ι ''ᵁ ⊤ ≤ U.basicOpen i.1 := by simp [O]
    have := (U.toRingedSpace.isUnit_res_basicOpen i.1).map (U.presheaf.map (homOfLE hle).op).hom
    have e : U.presheaf.map (homOfLE (x := (O i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        U.presheaf.map (homOfLE (U.basicOpen_le i.1)).op ≫ U.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    show IsUnit ((O i).ι.appTop.hom i.1)
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  refine ⟨S, Scheme.etaleTopology.superset_covering hgen
    (Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩)), ?_⟩
  rintro V g ⟨f, hf, hu⟩
  exact h f hf V g hu

theorem eq_of_unit_kill {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {f x y : A} {n : ℕ}
    (hn : f ^ n * (x - y) = 0) (hu : IsUnit (φ f)) : φ x = φ y := by
  have h0 : φ (f ^ n * (x - y)) = 0 := by rw [hn, map_zero]
  rw [map_mul, map_pow, map_sub] at h0
  exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)

theorem loc_mono' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem c2 (hA : AlgPow) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) :
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
  obtain ⟨s, hs, hf⟩ := hA q Γ(U, ⊤) ζ ξ
  refine loc_of_span s hs fun f hfs V g hu => ?_
  obtain ⟨a, n, hn⟩ := hf f hfs
  exact ⟨a, by rw [eq_of_unit_kill g.appTop.hom hn hu, map_pow]⟩

end LateralTheory.E.L_prim_locPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CechSqPf
section -- merged from Development.EtaleCohomology.TateTwists.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts
section -- merged from Development.EtaleCohomology.TateTwists.EtaleCechConerveImageIsoCechNerveOfPreservesWide
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts : Prop :=
  ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ),
    (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V),
    ∃ e : ((Arrow.mk g).cechConerve ⋙ Ψ).leftOp ≅ (Arrow.mk (Ψ.map g).unop).cechNerve,
      lev Ψ (coAug g) = e.hom ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom
end

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ConerveIsomorphism

variable {T : Type 1} [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ)
  {U V : T} (g : U ⟶ V)

noncomputable def phi (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ⟶
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) :=
  WidePullback.lift (Ψ.map (WidePushout.head _)).unop (fun j => (Ψ.map (WidePushout.ι _ j)).unop)
    (fun j => by
      have h := WidePushout.arrow_ι (fun _ : Fin (n+1) => g) j
      rw [← unop_comp, ← Ψ.map_comp, h])

lemma phi_π (n : ℕ) (j : Fin (n+1)) :
    phi Ψ g n ≫ WidePullback.π _ j = (Ψ.map (WidePushout.ι _ j)).unop := by
  unfold phi; erw [WidePullback.lift_π]

lemma phi_base (n : ℕ) :
    phi Ψ g n ≫ WidePullback.base _ = (Ψ.map (WidePushout.head _)).unop := by
  unfold phi; erw [WidePullback.lift_base]

lemma aux (n : ℕ) (j : Fin (n+1)) :
    Ψ.map g ≫ (WidePullback.π (fun _ : Fin (n+1) => (Ψ.map g).unop) j).op =
      (WidePullback.base (fun _ : Fin (n+1) => (Ψ.map g).unop)).op := by
  rw [← WidePullback.π_arrow (fun _ : Fin (n+1) => (Ψ.map g).unop) j]
  rfl

noncomputable def cocone (n : ℕ) : Cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g) ⋙ Ψ) where
  pt := op (widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop))
  ι :=
    { app := fun j => match j with
        | none => (WidePullback.base _).op
        | some j => (WidePullback.π _ j).op
      naturality := by
        rintro X Y (_ | j)
        · rw [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
            Category.id_comp, Category.comp_id]
        · exact (aux Ψ g n j).trans (Category.comp_id _).symm }

lemma natural (a b : ℕ) (σ : Fin (a+1) → Fin (b+1)) :
    (Ψ.map (WidePushout.desc (WidePushout.head (fun _ : Fin (b+1) => g))
      (fun i => WidePushout.ι (fun _ : Fin (b+1) => g) (σ i))
      (fun i => WidePushout.arrow_ι (fun _ : Fin (b+1) => g) (σ i)))).unop ≫ phi Ψ g a =
    phi Ψ g b ≫ WidePullback.lift (WidePullback.base (fun _ : Fin (b+1) => (Ψ.map g).unop))
      (fun i => WidePullback.π (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i))
      (fun i => WidePullback.π_arrow (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i)) := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, Category.assoc, phi_π, WidePullback.lift_π, phi_π, ← unop_comp, ← Ψ.map_comp,
      WidePushout.ι_desc]
  · rw [Category.assoc, Category.assoc, phi_base, WidePullback.lift_base, phi_base, ← unop_comp,
      ← Ψ.map_comp, WidePushout.head_desc]

variable (hΨ : ∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ)

noncomputable def hc (n : ℕ) :
    IsColimit (Ψ.mapCocone (colimit.cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g)))) :=
  haveI := hΨ n
  isColimitOfPreserves Ψ (colimit.isColimit _)

noncomputable def psi (n : ℕ) :
    widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) ⟶
      (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop :=
  ((hc Ψ g hΨ n).desc (cocone Ψ g n)).unop

lemma desc_phi (n : ℕ) : (hc Ψ g hΨ n).desc (cocone Ψ g n) ≫ (phi Ψ g n).op = 𝟙 _ := by
  apply (hc Ψ g hΨ n).hom_ext
  rintro (_ | j)
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)).trans (Quiver.Hom.unop_inj (phi_base Ψ g n)))
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))).trans (Quiver.Hom.unop_inj (phi_π Ψ g n j)))

noncomputable def levelIso (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ≅
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) where
  hom := phi Ψ g n
  inv := psi Ψ g hΨ n
  hom_inv_id := congrArg Quiver.Hom.unop (desc_phi Ψ g hΨ n)
  inv_hom_id := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, phi_π, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))
    · rw [Category.assoc, phi_base, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)

end LateralTheory.EtaleFoundations.ConerveIsomorphism

open LateralTheory.EtaleFoundations.ConerveIsomorphism in
theorem LateralTheory.EtaleFoundations.etale_cech_conerve_image_iso_cech_nerve_of_preserves_wide_pushouts : LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts := by
  intro T _ _ Ψ hΨ U V g
  refine ⟨NatIso.ofComponents (fun n => levelIso Ψ g hΨ n.unop.len) ?_, ?_⟩
  · intro m n h
    exact natural Ψ g _ _ h.unop.toOrderHom
  · ext n : 1
    exact (phi_base Ψ g (unop n).len).symm
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf

namespace LateralTheory.E.CechSqPf

abbrev Ψ : CommRingCat.{0} ⥤ PShᵒᵖ := (Scheme.Spec ⋙ yoneda).rightOp

instance (n : ℕ) : PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ :=
  preservesColimitsOfShape_rightOp _ _

abbrev Sg {C D : CommRingCat.{0}} (g : C ⟶ D) : Spc := ((Arrow.mk g).cechConerve ⋙ Ψ).leftOp

abbrev ag {C D : CommRingCat.{0}} (g : C ⟶ D) : Sg g ⟶ sch.obj (Spec C) := lev Ψ (coAug g)

def sqHom {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') : Arrow.mk g ⟶ Arrow.mk (pushout.inr g φ') :=
  Arrow.homMk (u := φ') (v := pushout.inl g φ') pushout.condition.symm

theorem eqv_comp (R : Type) [CommRing R] (F : Shv R) {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'')
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := fun n => by
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = (pull R f F n) ∘ (pull R g F n) := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

def IntegralSurjectiveRingCechAugmentationEtaleEqv : Prop := B4 → ∀ (q : ℕ) (i : ℤ) {C D : CommRingCat.{0}} (g : C ⟶ D), g.hom.IsIntegral → SpS g →
  IsUnit (q : C) → Eqv _ (cechAug (Spec.map g)) (tw q i)

def BaseChange : Prop := ∀ {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y'), g.hom.IsIntegral → SpS g →
  (pushout.inr g φ').hom.IsIntegral ∧ SpS (pushout.inr g φ')

def LevelPush : Prop := ∀ {A Y C D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y') (φ' : C ⟶ Y')
  (g : C ⟶ D), IsPushout φ c w φ' → ∀ n : SimplexCategory,
  IsPushout φ (c ≫ (coAug g).app n) (w ≫ (coAug (pushout.inr g φ')).app n) ((Arrow.mapCechConerve (sqHom g φ')).app n)

def LevelP : Prop := ∀ {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop), PushClosed P →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → ∀ n : SimplexCategory,
  P _ (c ≫ (coAug g).app n)

def Level0 : Prop := ∀ (q : ℕ) (i : ℤ) {A Y C D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y')
  (φ' : C ⟶ Y') (g : C ⟶ D), IsPushout φ c w φ' →
  ∃ (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : D ⟶ Z), IsPushout φ (c ≫ g) wz ψ ∧
    ∀ m, RelZ q i m ψ → RelZ q i m ((Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0))

theorem ag_eqv (q : ℕ) (i : ℤ) {C D : CommRingCat.{0}} (g : C ⟶ D)
    (h : Eqv _ (cechAug (Spec.map g)) (tw q i)) : Eqv _ (ag g) (tw q i) := by
  obtain ⟨e, he⟩ := LateralTheory.EtaleFoundations.etale_cech_conerve_image_iso_cech_nerve_of_preserves_wide_pushouts CommRingCat.{0} Ψ (fun n => inferInstance) C D g
  have h1 : (ag g) = e.hom ≫ cechAug (Spec.map g) := he
  rw [h1]
  exact eqv_comp _ _ _ _ (eqv_of_iso _ _ e) h

abbrev uMap {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') : Sg (pushout.inr g φ') ⟶ Sg g :=
  NatTrans.leftOp (Functor.whiskerRight (Arrow.mapCechConerve (sqHom g φ')) Ψ)

theorem u_sq {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') :
    uMap g φ' ≫ ag g = ag (pushout.inr g φ') ≫ sch.map (Spec.map φ') := by
  refine NatTrans.ext (funext fun n => ?_)
  have key : (coAug g).app n.unop ≫ (Arrow.mapCechConerve (sqHom g φ')).app n.unop =
      φ' ≫ (coAug (pushout.inr g φ')).app n.unop := by
    simp [coAug, sqHom]
    apply WidePushout.head_desc
  change (Ψ.map ((Arrow.mapCechConerve (sqHom g φ')).app n.unop)).unop ≫ (Ψ.map ((coAug g).app n.unop)).unop =
    (Ψ.map ((coAug (pushout.inr g φ')).app n.unop)).unop ≫ (Ψ.map φ').unop
  rw [← unop_comp, ← unop_comp, ← Ψ.map_comp, ← Ψ.map_comp, key]

theorem CechSq_of (h1 : IntegralSurjectiveRingCechAugmentationEtaleEqv) (h2 : BaseChange) (h3 : LevelPush) (h4 : LevelP) (h5 : Level0) : CechSq := by
  intro hH q _ i A Y φ hq P hP C D c g hCc hDc hgi hgs Y' w φ' hpo
  have hB4 : B4 := hH.2.2.2.2.2.2.2.2.1
  obtain ⟨hgi', hgs'⟩ := h2 g φ' hgi hgs
  have hqC : IsUnit (q : C) := by simpa using hq.map c.hom
  have hqY : IsUnit (q : Y') := by simpa using hqC.map φ'.hom
  refine ⟨_, _, uMap g φ', ag (pushout.inr g φ'), ag g, u_sq g φ', ag_eqv q i g (h1 hB4 q i g hgi hgs hqC),
    ag_eqv q i _ (h1 hB4 q i _ hgi' hgs' hqY), fun p => ?_, ?_⟩
  · exact ⟨_, c ≫ (coAug g).app (SimplexCategory.mk p), _, w ≫ (coAug (pushout.inr g φ')).app (SimplexCategory.mk p),
      _, h4 P hP c g hCc hDc _, h3 φ c w φ' g hpo _, fun m hm => hm⟩
  · obtain ⟨Z, wz, ψ, hpo0, hrel⟩ := h5 q i φ c w φ' g hpo
    exact ⟨Z, wz, ψ, hpo0, fun m hm => hrel m hm⟩

end LateralTheory.E.CechSqPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IterBCPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterBCPf

theorem iterLine_of_isPullback {S P : Scheme.{0}} {q : P ⟶ S} (hq : IterLine q) :
    ∀ {X P' : Scheme.{0}} {a : P' ⟶ P} {q' : P' ⟶ X} {g : X ⟶ S}, IsPullback a q' q g → IterLine q' := by
  induction hq with
  | iso e he =>
    intro X P' a q' g w
    exact IterLine.iso _ (w.isIso_snd_of_isIso he)
  | comp l k hl hk ih =>
    intro X P' a q' g w
    have hb : IsPullback (pullback.fst k g) (pullback.snd k g) k g := IsPullback.of_hasPullback k g
    let m : P' ⟶ pullback k g := pullback.lift (a ≫ l) q' (by rw [Category.assoc]; exact w.w)
    have hm : q' = m ≫ pullback.snd k g := (pullback.lift_snd _ _ _).symm
    have ht : IsPullback a m l (pullback.fst k g) := by
      refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm hb
      rw [← hm]; exact w
    rw [hm]
    exact IterLine.comp m _ (IsLine.bc hl ht) (ih hb)

theorem IterBC_of : IterBC := by
  intro P S X q g hq
  exact iterLine_of_isPullback hq (IsPullback.of_hasPullback g q).flip

end LateralTheory.E.IterBCPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.MonicSplitsPf
open Polynomial

namespace LateralTheory.E.MonicSplitsPf

theorem selfDualLattice_projection_mem_of_unit_length (R : Type) [CommRing R] [IsDomain R] (hA : GlobalTheory.EtC.AIC R) :
    ∀ n : ℕ, ∀ p : Polynomial R, p.Monic → p.natDegree = n →
      ∃ s : Multiset R, p = (s.map fun a => X - C a).prod := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    refine ⟨0, ?_⟩
    simpa using hp.natDegree_eq_zero.mp hn
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := hA p hp (by omega)
    have hroot : IsRoot p a := ha
    have hmul := (mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hmul]; exact hp)
    have hqd : q.natDegree = n := by
      rw [hq, natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C, hn]; omega
    obtain ⟨s, hs⟩ := ih q hqm hqd
    refine ⟨a ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

theorem MonicSplits_of : LateralTheory.E.HensCut.MonicSplits := by
  intro R _ _ hA p hp
  exact selfDualLattice_projection_mem_of_unit_length R hA p.natDegree p hp rfl

end LateralTheory.E.MonicSplitsPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IdemPartPf
namespace LateralTheory.E.IdemPartPf

open Finset

theorem prod_erase_mul_prod_erase {A : Type} [CommRing A] {n : ℕ} (y : Fin n → A)
    (h0 : ∏ l, y l = 0) {l m : Fin n} (hlm : l ≠ m) :
    (∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k) = 0 := by
  have hl : l ∈ (univ : Finset (Fin n)).erase m := mem_erase.2 ⟨hlm, mem_univ l⟩
  rw [← mul_prod_erase _ y hl, ← mul_assoc, mul_comm (∏ k ∈ univ.erase l, y k) (y l),
    mul_prod_erase _ y (mem_univ l), h0, zero_mul]

theorem IdemPart_of : LateralTheory.E.HensCut.IdemPart := by
  intro A _ n y h0 hu
  obtain ⟨u, hu⟩ := hu
  let e : Fin n → A := fun l => (↑u⁻¹ : A) * ∏ m ∈ univ.erase l, y m
  have horth : ∀ l m, l ≠ m → e l * e m = 0 := by
    intro l m hlm
    have := prod_erase_mul_prod_erase y h0 hlm
    calc e l * e m = (↑u⁻¹ : A) * ↑u⁻¹ * ((∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k)) := by
          simp only [e]; ring
      _ = 0 := by rw [this, mul_zero]
  have hsum : ∑ l, e l = 1 := by
    simp only [e]
    rw [← mul_sum, ← hu, Units.inv_mul]
  refine ⟨e, ?_, horth, hsum, ?_⟩
  · intro l
    unfold IsIdempotentElem
    calc e l * e l = e l * ∑ m, e m := by
          rw [mul_sum, sum_eq_single l]
          · intro m _ hml; exact horth l m (Ne.symm hml)
          · intro h; exact absurd (mem_univ l) h
      _ = e l := by rw [hsum, mul_one]
  · intro l
    simp only [e]
    rw [mul_assoc, mul_comm (∏ m ∈ univ.erase l, y m) (y l), mul_prod_erase _ y (mem_univ l), h0, mul_zero]

end LateralTheory.E.IdemPartPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocalizationIntegralClosure
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LocalizationIntegralClosure

theorem aic_loc (B : Type) [CommRing B] [IsDomain B] (M : Submonoid B) (hB : AIC B) :
    AIC (Localization M) := by
  classical
  intro p hp hd
  set L := Localization M
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (R := B) M
    ((Finset.range (p.natDegree + 1)).image p.coeff) (S := L)
  set t : L := algebraMap B L (s : B) with ht
  have hlift : scaleRoots p t ∈ lifts (algebraMap B L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_or_ge i p.natDegree with hi | hi
    · obtain ⟨c, hc⟩ := hs (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      refine ⟨c * (s : B) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, hc, pow_succ, Algebra.smul_def, ← ht]
      ring
    · rcases eq_or_lt_of_le hi with h | h
      · subst h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
      · rw [coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).2 hp)
  obtain ⟨b, hb⟩ := hB q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  obtain ⟨u, hu⟩ := IsLocalization.map_units L s
  refine ⟨algebraMap B L b * ((u⁻¹ : Lˣ) : L), ?_⟩
  have h1 : (scaleRoots p t).eval (algebraMap B L b) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, hb, map_zero]
  have h2 : (scaleRoots p t).eval (t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L))) =
      t ^ p.natDegree * p.eval (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) :=
    scaleRoots_eval₂_mul (p := p) (RingHom.id L) (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) t
  have h3 : t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) = algebraMap B L b := by
    rw [ht, ← hu, mul_comm (algebraMap B L b), ← mul_assoc, Units.mul_inv, one_mul]
  rw [h3, h1] at h2
  have hunit : IsUnit (t ^ p.natDegree) := (hu ▸ u.isUnit).pow _
  exact (hunit.mul_right_eq_zero).1 h2.symm

theorem LocAIC_of : LateralTheory.E.HensCut.LocAIC := by
  intro B _ _ M h0 hB
  have hle : M ≤ nonZeroDivisors B := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero (fun h => h0 (h ▸ hx))
  exact ⟨IsLocalization.isDomain_localization hle, aic_loc B M hB⟩

end LateralTheory.E.LocalizationIntegralClosure
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LineExPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineExPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℤ

lemma zero_surj : Function.Surjective (algebraMap ℤ (𝒜 0)) := by
  rintro ⟨x, hx⟩
  refine ⟨AddMonoidAlgebra.coeff x 0, ?_⟩
  apply Subtype.ext
  have h : MvPolynomial.IsHomogeneous x 0 := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hx
  by_cases h0 : x = 0
  · subst h0; simp
  · have := h.totalDegree h0
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at this
    change ((algebraMap ℤ (𝒜 0) _ : 𝒜 0) : MvPolynomial (Fin 2) ℤ) = x
    refine Eq.trans ?_ this.symm
    simp
    rfl

instance ft : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin 2) ℤ) :=
  Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝒜 0) (MvPolynomial (Fin 2) ℤ)

lemma proj_proper : IsProper (Proj.toSpecZero 𝒜) := inferInstance

lemma projective_line_over_integers_isProper : IsProper (terminal.from P1) := by
  have h1 : IsProper (Proj.toSpecZero 𝒜) := proj_proper
  have h2 : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0)))) :=
    IsClosedImmersion.spec_of_surjective _ zero_surj
  have e : terminal.from P1 = Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0))) ≫
      terminal.from (Spec (CommRingCat.of ℤ)) := terminal.hom_ext _ _
  have : IsIso (terminal.from (Spec (CommRingCat.of ℤ))) :=
    ⟨⟨specZIsTerminal.from _, specZIsTerminal.hom_ext _ _, terminal.hom_ext _ _⟩⟩
  have h3 : IsProper (terminal.from (Spec (CommRingCat.of ℤ))) := by
    have : IsClosedImmersion (terminal.from (Spec (CommRingCat.of ℤ))) := inferInstance
    infer_instance
  have h2' : IsProper (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0)))) := inferInstance
  rw [e]
  exact MorphismProperty.comp_mem @IsProper _ _ h1 (MorphismProperty.comp_mem @IsProper _ _ h2' h3)

theorem LineEx_of : LateralTheory.E.ChowLCut.LineEx := by
  intro S
  refine ⟨pullback (terminal.from P1) (terminal.from S), pullback.snd _ _, ?_, pullback.fst _ _,
    IsPullback.of_hasPullback _ _⟩
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) projective_line_over_integers_isProper

end LateralTheory.E.LineExPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EmptyVan2
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.EmptyVan₂

theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    Subsingleton (G.obj.obj (op X)) := by
  have h := Sheaf.isTerminalOfBotCover G X (Scheme.bot_mem_grothendieckTopology X)
  constructor
  intro a b
  have e := h.hom_ext (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ a))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ b))
  have := congrArg (fun f => f.hom (1 : ULift.{1} R)) e
  simpa using this

theorem free_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  ext U x
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · have := sec_subsingleton (R := R) ((free R).obj (yoneda.obj X)) U.unop
    exact @Subsingleton.elim _ this _ _
  · have : IsEmpty ((yoneda.obj X).obj U) := ⟨fun (f : U.unop ⟶ X) => IsEmpty.false (f.base (Classical.arbitrary U.unop))⟩
    have hx : x = 0 := Subsingleton.elim (α := ULift.{1} ((yoneda.obj X).obj U) →₀ ULift.{1} R) x 0
    rw [hx, map_zero, map_zero]

theorem chains_X_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (m : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X m) := by
  rcases le_or_gt m 0 with h | h
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, m = -(p : ℤ) := ⟨(-m).toNat, by omega⟩
    exact (free_isZero (R := R) X).of_iso (chainsXIso R _ p)
  · exact HomologicalComplex.isZero_extend_X _ _ m (fun i => by
      change -(i : ℤ) ≠ m; omega)

theorem cc_subsingleton {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ}
    (hK : ∀ m, IsZero (K.X m)) (n : ℤ) : Subsingleton (CohomologyClass K L n) := by
  have : Subsingleton (Cochain K L n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hK p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle K L n) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

theorem EmptyVan_of : LateralTheory.E.CoverPf.EmptyVan := by
  intro _ q _ i n S _ hS x
  have : IsEmpty (Spec (CommRingCat.of S)) :=
    ⟨fun p => (p : PrimeSpectrum S).isPrime.ne_top (Subsingleton.elim _ _)⟩
  have := cc_subsingleton (L := res (ZMod q) (tw q i)) (chains_X_isZero (R := ZMod q) (Spec (CommRingCat.of S))) (n + 1)
  exact Subsingleton.elim _ _

end LateralTheory.E.EmptyVan₂
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LimIntPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.CoverCut

namespace LateralTheory.E.LimIntPf

theorem key {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hw : f ≫ g = h) (U : Z.Opens) (V₁ : Y.Opens)
    (W₁ W : X.Opens) (e1 : V₁ ≤ g ⁻¹ᵁ U) (e2 : W₁ ≤ f ⁻¹ᵁ V₁) (e3 : W ≤ W₁) (e : W ≤ h ⁻¹ᵁ U) (x : Γ(Z, U)) :
    X.presheaf.map (homOfLE e3).op (f.appLE V₁ W₁ e2 (g.appLE U V₁ e1 x)) = h.appLE U W e x := by
  subst hw
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_map]

theorem app_surj {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (hc : IsLimit c)
    [∀ {i k : J} (f : i ⟶ k), IsAffineHom (D.map f)] (hC : ∀ {i k : J} (f : i ⟶ k), IsClosedImmersion (D.map f))
    (j : J) (U : (D.obj j).Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((c.π.app j).app U) := by
  intro s
  have (k : Over j) : IsAffine ((opensDiagram D j U).obj k) := hU.preimage (D.map _)
  obtain ⟨k, t, hk⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc j U)
    (c.pt.presheaf.map (homOfLE (show (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ c.π.app j ⁻¹ᵁ U by simp)).op s)
  have := hC k.hom
  obtain ⟨u, hu⟩ := (D.map k.hom).app_surjective U hU
    ((D.obj k.left).presheaf.map (homOfLE (show D.map k.hom ⁻¹ᵁ U ≤ (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp)).op t)
  refine ⟨u, ?_⟩
  simp only [opensCone_π_app, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at hk hu ⊢
  have e1 : ∀ {X : Scheme.{0}} {V W : X.Opens} (h1 : V ≤ W) (h2 : W ≤ V) (x : Γ(X, W)),
      X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op x) = x := by
    intro X V W h1 h2 x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have : (homOfLE h1).op ≫ (homOfLE h2).op = 𝟙 (Opposite.op W) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]; rfl
  have hs := e1 (X := c.pt) (show (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ c.π.app j ⁻¹ᵁ U by simp)
    (show c.π.app j ⁻¹ᵁ U ≤ (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp) s
  rw [← hk] at hs
  have ht := e1 (X := D.obj k.left) (show D.map k.hom ⁻¹ᵁ U ≤ (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp)
    (show (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ D.map k.hom ⁻¹ᵁ U by simp) t
  rw [← hu] at ht
  rw [← hs, ← ht]
  have cg : ∀ {X Y : Scheme.{0}} (f g : X ⟶ Y) (h : f = g) (U : Y.Opens) (V : X.Opens) e e',
      f.appLE U V e = g.appLE U V e' := by
    intro X Y f g h U V e e'; subst h; rfl
  erw [Scheme.Hom.resLE_appLE]
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
  exact (key _ _ _ (c.w k.hom) _ _ _ _ _ _ _ _ u).symm

theorem LimInt_of : LateralTheory.E.BuildCut.LimInt := by
  intro Y y J _ _ D c ι hsys j
  obtain ⟨⟨hl⟩, h2, h3⟩ := hsys
  have hA : ∀ {i k : J} (f : i ⟶ k), IsAffineHom (D.map f) := fun f => (h3 f).2
  have hC : ∀ {i k : J} (f : i ⟶ k), IsClosedImmersion (D.map f) := by
    intro i k f
    have : IsClosedImmersion (ι k) := (h2 k).2.1
    have : IsClosedImmersion (D.map f ≫ ι k) := by rw [(h3 f).1]; exact (h2 i).2.1
    exact IsClosedImmersion.of_comp (D.map f) (ι k)
  have : IsClosedImmersion (ι j) := (h2 j).2.1
  have : IsIntegralHom (c.π.app j) :=
    { toIsAffineHom := isAffineHom_π_app D c hl j
      isIntegral_app := fun U hU =>
        (RingHom.Finite.of_surjective _ (app_surj D c hl hC j U hU)).to_isIntegral }
  infer_instance

end LateralTheory.E.LimIntPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ProdACFField
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut

namespace LateralTheory.E.PtsPf

attribute [local instance] PrimeSpectrum.isPrime

lemma prodACF_field (K : Type) [Field K] [IsAlgClosed K] : ProdACF K := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p (by
      rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hd.ne')
    exact ⟨x, hx⟩
  · by_cases ha : a = 0
    · exact ⟨0, 1, IsIdempotentElem.zero, isUnit_one, by simp [ha]⟩
    · exact ⟨1, a, IsIdempotentElem.one, isUnit_iff_ne_zero.mpr ha, by simp⟩

lemma prodACF_pi {ι : Type} (W : ι → Type) [∀ i, CommRing (W i)] (h : ∀ i, ProdACF (W i)) :
    ProdACF (∀ i, W i) := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · have hr : ∀ i, ∃ x, (p.map (Pi.evalRingHom W i)).eval x = 0 := by
      intro i
      rcases subsingleton_or_nontrivial (W i) with hs | hs
      · exact ⟨0, Subsingleton.elim _ _⟩
      · exact (h i).1 _ (hp.map _) (by rw [hp.natDegree_map]; exact hd)
    choose x hx using hr
    refine ⟨x, funext fun i => ?_⟩
    have := Polynomial.hom_eval₂ p (RingHom.id _) (Pi.evalRingHom W i) x
    simp only [RingHom.comp_id] at this
    simp only [Polynomial.eval_map] at hx
    change (Pi.evalRingHom W i) (Polynomial.eval₂ (RingHom.id _) x p) = 0
    rw [this]
    exact hx i
  · have hr := fun i => (h i).2 (a i)
    choose e u he hu hau using hr
    refine ⟨e, u, ?_, Pi.isUnit_iff.mpr hu, funext hau⟩
    exact funext fun i => he i

abbrev WA (R : CommRingCat.{0}) : Type :=
  ∀ p : PrimeSpectrum R, AlgebraicClosure p.asIdeal.ResidueField

def phiA (R : CommRingCat.{0}) : R →+* WA R :=
  RingHom.pi fun p => (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField)

lemma surj_phiA (R : CommRingCat.{0}) : Surjective (Spec.map (CommRingCat.ofHom (phiA R))) := by
  refine ⟨fun p' => ?_⟩
  obtain ⟨p, rfl⟩ : ∃ p : PrimeSpectrum R, (p : Spec R) = p' := ⟨p', rfl⟩
  let ev : WA R →+* AlgebraicClosure p.asIdeal.ResidueField := Pi.evalRingHom _ p
  have hq : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  refine ⟨⟨RingHom.ker ev, hq⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (phiA R) (RingHom.ker ev) = p.asIdeal
  rw [RingHom.comap_ker]
  have : ev.comp (phiA R) = (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField) := rfl
  rw [this, RingHom.ker_comp_of_injective _ (RingHom.injective (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField))), Ideal.ker_algebraMap_residueField]

theorem Pts_of : Pts := by
  intro P _ _
  let 𝒰 := P.affineCover.finiteSubcover
  let I := 𝒰.I₀
  have hA : ∀ i : I, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (P.affineCover.X _); infer_instance
  let R : I → CommRingCat.{0} := fun i => Γ(𝒰.X i, ⊤)
  let f : ∀ i, Spec (R i) ⟶ P := fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  let S : I → CommRingCat.{0} := fun i => CommRingCat.of (WA (R i))
  let g : ∀ i, Spec (S i) ⟶ P := fun i => Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ f i
  refine ⟨∀ i, S i, inferInstance, inv (sigmaSpec S) ≫ Sigma.desc g, ?_, ?_⟩
  · exact prodACF_pi _ fun i => prodACF_pi _ fun p => prodACF_field _
  · have : Surjective (Sigma.desc g) := by
      apply Surjective.sigmaDesc_of_union_range_eq_univ
      have hr : ∀ i, Set.range (g i) = Set.range (𝒰.f i) := fun i => by
        have := surj_phiA (R i)
        rw [range_eq_range_of_surjective (g i) (𝒰.f i) (Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ (𝒰.X i).isoSpec.inv)
          (by simp [g, f])]
      simp_rw [hr]
      exact 𝒰.iUnion_range
    infer_instance

end LateralTheory.E.PtsPf
end
end

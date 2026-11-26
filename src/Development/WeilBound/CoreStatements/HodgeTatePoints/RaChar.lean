module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull
public import ReciprocityTheory.DualLattices.LinPairStatement

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RaChar
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

theorem charmem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA ψ
  obtain ⟨B, hB, hAA⟩ := AA.lat
  rw [hAA, ← dualLat_dualLat_spanCols B hB, ← hAA]
  intro u hu
  obtain ⟨r, hr⟩ := hv.exists_of_le_one
    (valuation_fourier_le_one v hv (fun _ : Unit => ψ) AA hu ())
  refine ⟨r, hr.trans ?_⟩
  rw [fourier_apply']
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end PositivityTheory.HtPt.Ra
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcTors
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

section
variable {S Y : Scheme.{0}} {G : Over S} [GrpObj G]

theorem mul_congr {a b : Y ⟶ S} (h : a = b) (g k : Over.mk a ⟶ G) (g' k' : Over.mk b ⟶ G) (e : g.left = g'.left)
    (e' : k.left = k'.left) : (g * k).left = (g' * k').left := by
  subst h
  rw [Over.OverMorphism.ext e, Over.OverMorphism.ext e']

theorem comp_pow_pt {A B : Over S} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) : ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
  {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

theorem tors_of_pt (h : Γ.IsTorsionAlong G x N i) (v : Y ⟶ Γ.G.left) {c : Y ⟶ S} (g : Over.mk c ⟶ G)
    (e : g.left = v ≫ i) : g ^ N = 1 := by
  have hc : c = (v ≫ Γ.G.hom) ≫ x := by
    rw [Category.assoc, ← h.isOver, ← Category.assoc, ← e]; exact (Over.w g).symm
  subst hc
  exact (h.kernel (Over.mk (v ≫ Γ.G.hom)) g).2 ⟨Over.homMk v rfl, e.symm⟩

theorem pt_of_tors (h : Γ.IsTorsionAlong G x N i) (b : Y ⟶ Spec (CommRingCat.of R)) {c : Y ⟶ S} (hc : c = b ≫ x)
    (g : Over.mk c ⟶ G) (hg : g ^ N = 1) : ∃ v : Y ⟶ Γ.G.left, v ≫ Γ.G.hom = b ∧ v ≫ i = g.left := by
  subst hc
  obtain ⟨y, hy⟩ := (h.kernel (Over.mk b) g).1 hg
  exact ⟨y.left, Over.w y, hy⟩

end

theorem torsion_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsSeparated G.hom → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N i' → ∀ (B : Type) [CommRing B] (b : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R') (σ : T → (Spec (CommRingCat.of B) ⟶ G.left)), Function.Injective j → j.comp b = algebraMap R _ → j'.comp b = (algebraMap R' _).comp φ → (∀ t, σ t ≫ G.hom = Spec.map (CommRingCat.ofHom b) ≫ x) → (∀ t, Spec.map (CommRingCat.ofHom j) ≫ σ t = (Γ.pt t).left ≫ i) → (∀ t, Spec.map (CommRingCat.ofHom j') ≫ σ t = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ φ F := by
  intro R _ _ T _ _ Γ S G _ _ x N i h hsep R' _ _ φ Γ' i' h' B _ b j j' σ hj hjb hj'b hσ hσj hσj'
  let g : Over.mk (i' ≫ G.hom) ⟶ G := Over.homMk i' rfl
  obtain ⟨F, hF1, hF2⟩ := pt_of_tors h (Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (h'.isOver.trans (Category.assoc _ _ _).symm) g (tors_of_pt h' (𝟙 _) g (Category.id_comp _).symm)
  replace hF2 : F ≫ i = i' := hF2
  refine ⟨F, hF2, ?_, fun Y y z y₀ z₀ hy hz => ?_, ?_⟩
  · have hl : ∀ c : PullbackCone Γ.G.hom (Spec.map (CommRingCat.ofHom φ)), ∃ v : c.pt ⟶ Γ'.G.left,
        v ≫ F = c.fst ∧ v ≫ Γ'.G.hom = c.snd := fun c => by
      let k : Over.mk ((c.fst ≫ i) ≫ G.hom) ⟶ G := Over.homMk (c.fst ≫ i) rfl
      obtain ⟨v, h1, h2⟩ := pt_of_tors h' c.snd
        (by rw [Category.assoc, h.isOver, ← Category.assoc, c.condition, Category.assoc]) k (tors_of_pt h c.fst k rfl)
      exact ⟨v, tors_ext h (by rw [Category.assoc, hF1, ← Category.assoc, h1, c.condition])
        (by rw [Category.assoc, hF2, h2]; rfl), h1⟩
    choose l h1 h2 using hl
    exact ⟨⟨hF1⟩, ⟨PullbackCone.IsLimit.mk hF1 l h1 h2 fun c m a1 a2 => tors_ext h' (a2.trans (h2 c).symm) (by
      rw [← hF2, ← Category.assoc, ← Category.assoc, a1, h1])⟩⟩
  · have w : ∀ {y₀ : Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G},
        (y₀.left ≫ i) ≫ G.hom = (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x := fun {y₀} => by
      rw [Category.assoc, h.isOver, ← Category.assoc, Over.w y₀]; rfl
    have w' : ∀ {y : Y ⟶ Γ'.G}, (y.left ≫ i') ≫ G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ x := fun {y} => by
      rw [Category.assoc, h'.isOver, ← Category.assoc, Over.w y]
    refine tors_ext h ?_ ?_
    · rw [Category.assoc, hF1, ← Category.assoc, Over.w (y * z)]
      exact Over.w (y₀ * z₀)
    · refine (h.mul _ y₀ z₀ (Over.homMk (y₀.left ≫ i) w) (Over.homMk (z₀.left ≫ i) w) rfl rfl).symm.trans ?_
      rw [Category.assoc, hF2]
      refine Eq.trans ?_ (h'.mul Y y z (Over.homMk (y.left ≫ i') w') (Over.homMk (z.left ≫ i') w') rfl rfl)
      refine mul_congr (Category.assoc _ _ _) _ _ _ _ ?_ ?_
      · show y₀.left ≫ i = y.left ≫ i'
        rw [hy, Category.assoc, hF2]
      · show z₀.left ≫ i = z.left ≫ i'
        rw [hz, Category.assoc, hF2]
  · have : IsDomain B := hj.isDomain j
    have : IsDominant (Spec.map (CommRingCat.ofHom j)) := ⟨by
      have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)
      exact this⟩
    have hσ' : ∀ t, ∃ v : Spec (CommRingCat.of B) ⟶ Γ.G.left,
        v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom b) ∧ v ≫ i = σ t := fun t => by
      let k : Over.mk (σ t ≫ G.hom) ⟶ G := Over.homMk (σ t) rfl
      refine pt_of_tors h _ (hσ t) k ?_
      let ψ : Over.mk (Spec.map (CommRingCat.ofHom j) ≫ σ t ≫ G.hom) ⟶ Over.mk (σ t ≫ G.hom) :=
        Over.homMk (Spec.map (CommRingCat.ofHom j)) rfl
      have h1 : ψ ≫ k ^ N = ψ ≫ 1 := by
        rw [comp_pow_pt, MonObj.comp_one]
        exact tors_of_pt h (Γ.pt t).left _ (hσj t)
      exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of B)) G.hom
        ((Over.w _).trans (Over.w _).symm) (Spec.map (CommRingCat.ofHom j)) (congrArg (·.left) h1))
    choose v h1 h2 using hσ'
    refine ⟨B, inferInstance, b, j, j', v, hj, hjb, hj'b, h1, fun t => tors_ext h ?_ ?_, fun t => tors_ext h ?_ ?_⟩
    · rw [Category.assoc, h1, Over.w, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjb]; rfl
    · rw [Category.assoc, h2, hσj]
    · rw [Category.assoc, Category.assoc, h1, hF1, ← Category.assoc, Over.w, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hj'b, CommRingCat.ofHom_comp, Spec.map_comp]; rfl
    · rw [Category.assoc, Category.assoc, h2, hF2, hσj']

end PositivityTheory.HtPt.Htat
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.FormMemLin
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

section
variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]

def formR (p : ℕ) (ι : Type) [Fintype ι] : (ι → R) →ₗ[R] ((ι → ZMod p) → R) where
  toFun l x := ∑ i, l i * ((x i).val : R)
  map_add' l l' := by ext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c l := by ext x; simp [Finset.mul_sum, mul_assoc]


variable (C) in
def toC (X : Type) : (X → R) →ₗ[R] (X → C) := (Algebra.linearMap R C).compLeft X

variable {R}

theorem mem_pInt {p : ℕ} {z : C} : z ∈ pInt (C := C) R p ↔ ∃ r : R, z = algebraMap R C r * p := by
  simp only [pInt, Submodule.mem_span_singleton, Algebra.smul_def]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

theorem afLat_eq (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R ((ι → ZMod p) → C)) :
    afLat p M = (M ⊔ pFun R p _).comap (toC (C := C) R _ ∘ₗ formR R p ι) := by
  ext l
  rw [Submodule.mem_comap, Submodule.mem_sup]
  change (∃ g ∈ M, ∀ x, g x - algebraMap R C (∑ i, l i * ((x i).val : R)) ∈ pInt R p) ↔ _
  have hf : (toC (C := C) R _ ∘ₗ formR R p ι) l = fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) := rfl
  rw [hf]
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) - g x, ?_, ?_⟩
    · rw [pFun, Submodule.mem_pi]
      intro x _
      have := neg_mem (h x)
      rwa [neg_sub] at this
    · funext x
      simp
  · rintro ⟨g, hg, z, hz, he⟩
    refine ⟨g, hg, fun x => ?_⟩
    have hx : z x ∈ pInt R p := (Submodule.mem_pi.mp hz) x (Set.mem_univ x)
    have e : g x - algebraMap R C (∑ i, l i * ((x i).val : R)) = - z x := by
      rw [← congrFun he x]
      simp
    rw [e]
    exact neg_mem hx

theorem form_mem_lin (p : ℕ) [NeZero p] {ι : Type} [Fintype ι] (l : ι → R) :
    (toC (C := C) R _ ∘ₗ formR R p ι) l ∈ linFun (C := C) R p (ι → ZMod p) := by
  rw [linFun, Submodule.mem_inf]
  have hf : (toC (C := C) R _ ∘ₗ formR R p ι) l = fun x => algebraMap R C (∑ i, l i * ((x i).val : R)) := rfl
  rw [hf]
  refine ⟨fun x => ⟨∑ i, l i * ((x i).val : R), rfl⟩, ?_⟩
  intro x y
  rw [mem_pInt]
  refine ⟨-∑ i, l i * ((((x i).val + (y i).val) / p : ℕ) : R), ?_⟩
  have key : ∀ i, (((x i + y i).val : ℕ) : R) = ((x i).val : R) + (y i).val - p * ((((x i).val + (y i).val) / p : ℕ) : R) := by
    intro i
    rw [ZMod.val_add, eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div, Nat.cast_add]
  simp only [Pi.add_apply, key]
  simp only [← map_sub, ← map_neg, ← map_natCast (algebraMap R C), ← map_mul]
  congr 1
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem add_mem_pFun {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    {h : (ι → ZMod p) → C} (hh : h ∈ addFun R p (ι → ZMod p))
    (h1 : ∀ i, h (Pi.single i 1) ∈ pInt (C := C) R p) : h ∈ pFun R p (ι → ZMod p) := by
  have h0 : h 0 ∈ pInt (C := C) R p := by
    have := neg_mem (hh 0 0)
    simpa using this
  let S : AddSubmonoid (ι → ZMod p) :=
    { carrier := {x | h x ∈ pInt (C := C) R p}
      add_mem' := by
        intro a b ha hb
        have e : h (a + b) = (h (a + b) - h a - h b) + h a + h b := by ring
        show h (a + b) ∈ pInt (C := C) R p
        rw [e]
        exact add_mem (add_mem (hh a b) ha) hb
      zero_mem' := h0 }
  have hall : ∀ x, x ∈ S := by
    intro x
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun i _ => ?_
    have e : Pi.single i (x i) = (x i).val • (Pi.single i (1 : ZMod p) : ι → ZMod p) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_apply, hj]
    rw [e]
    exact nsmul_mem (show (Pi.single i (1 : ZMod p) : ι → ZMod p) ∈ S from h1 i) _
  rw [pFun, Submodule.mem_pi]
  intro x _
  exact hall x

end

theorem aflat_fg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), (afLat p AA.carrier).FG := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : ValuationRing R :=
    { cond' := fun a b => by
        rcases le_total (v (algebraMap R C a)) (v (algebraMap R C b)) with h | h
        · obtain ⟨c, hc⟩ := hv.dvd_of_le h
          exact ⟨c, Or.inr hc.symm⟩
        · obtain ⟨c, hc⟩ := hv.dvd_of_le h
          exact ⟨c, Or.inl hc.symm⟩ }
  rw [afLat_eq, Submodule.comap_comp]
  apply comap_fg_of_valuationRing
  have hinj : Function.Injective (toC (C := C) R (ι → ZMod p)) := by
    intro f g h
    funext x
    exact hv.hom_inj (congrFun h x)
  apply Submodule.fg_of_fg_map_injective (toC (C := C) R (ι → ZMod p)) hinj
  have hle : AA.carrier ⊔ pFun R p (ι → ZMod p) ≤ LinearMap.range (toC (C := C) R (ι → ZMod p)) := by
    apply sup_le
    · intro f hf
      have hi := AA.le_int hf
      choose r hr using hi
      exact ⟨r, funext fun x => hr x⟩
    · intro f hf
      rw [pFun, Submodule.mem_pi] at hf
      choose r hr using fun x => mem_pInt.mp (hf x (Set.mem_univ x))
      refine ⟨fun x => r x * p, funext fun x => ?_⟩
      rw [hr x]
      simp [toC]
  rw [Submodule.map_comap_eq, inf_eq_right.mpr hle]
  apply Submodule.FG.sup
  · obtain ⟨B, _, hB⟩ := AA.lat
    rw [hB]
    exact Submodule.fg_span (Set.finite_range _)
  · have hP : pFun R p (ι → ZMod p) = Submodule.map ((p : R) • toC (C := C) R (ι → ZMod p)) ⊤ := by
      ext f
      simp only [Submodule.mem_map, Submodule.mem_top, true_and]
      rw [pFun, Submodule.mem_pi]
      constructor
      · intro hf
        choose r hr using fun x => mem_pInt.mp (hf x (Set.mem_univ x))
        refine ⟨r, funext fun x => ?_⟩
        rw [hr x]
        simp [toC, Algebra.smul_def, mul_comm]
      · rintro ⟨r, rfl⟩ x _
        rw [mem_pInt]
        exact ⟨r x, by simp [toC, Algebra.smul_def, mul_comm]⟩
    rw [hP]
    exact Submodule.FG.map _ Module.Finite.fg_top

theorem afquot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let φ := toC (C := C) R (ι → ZMod p) ∘ₗ formR R p ι
  let K := Submodule.comap (linFun (C := C) R p (ι → ZMod p)).subtype (afFun p AA.carrier ⊔ pFun (C := C) R p (ι → ZMod p))
  let ψ : (ι → R) →ₗ[R] linFun (C := C) R p (ι → ZMod p) := LinearMap.codRestrict _ φ (fun l => form_mem_lin p l)
  let f := K.mkQ ∘ₗ ψ
  have hpf : pFun (C := C) R p (ι → ZMod p) ≤ addFun (C := C) R p (ι → ZMod p) := by
    intro z hz x y
    rw [pFun, Submodule.mem_pi] at hz
    exact sub_mem (sub_mem (hz _ (Set.mem_univ _)) (hz _ (Set.mem_univ _))) (hz _ (Set.mem_univ _))
  have hker : afLat p AA.carrier = LinearMap.ker f := by
    ext l
    rw [LinearMap.mem_ker, afLat_eq, Submodule.mem_comap]
    change _ ↔ Submodule.Quotient.mk (ψ l) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    change φ l ∈ AA.carrier ⊔ pFun (C := C) R p _ ↔ φ l ∈ afFun p AA.carrier ⊔ pFun (C := C) R p _
    constructor
    · intro h
      obtain ⟨g, hg, z, hz, he⟩ := Submodule.mem_sup.mp h
      have hadd : φ l ∈ addFun (C := C) R p (ι → ZMod p) := (Submodule.mem_inf.mp (form_mem_lin p l)).2
      have hg' : g ∈ addFun (C := C) R p (ι → ZMod p) := by
        have : g = φ l - z := by rw [← he]; abel
        rw [this]
        exact sub_mem hadd (hpf hz)
      exact Submodule.mem_sup.mpr ⟨g, Submodule.mem_inf.mpr ⟨hg, hg'⟩, z, hz, he⟩
    · intro h
      exact (sup_le_sup_right inf_le_left _ : afFun p AA.carrier ⊔ pFun (C := C) R p _ ≤ AA.carrier ⊔ pFun (C := C) R p _) h
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.mkQ_surjective K q
    have hh' := Submodule.mem_inf.mp hh
    choose l hl using fun i => hh'.1 (Pi.single i (1 : ZMod p))
    refine ⟨l, ?_⟩
    show Submodule.Quotient.mk (ψ l) = Submodule.Quotient.mk ⟨h, hh⟩
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    apply Submodule.mem_sup_right
    change φ l - h ∈ pFun (C := C) R p (ι → ZMod p)
    apply add_mem_pFun
    · exact sub_mem (Submodule.mem_inf.mp (form_mem_lin p l)).2 hh'.2
    · intro i
      have e : φ l (Pi.single i 1) = algebraMap R C (l i) := by
        show algebraMap R C (∑ j, l j * (((Pi.single i (1 : ZMod p) : ι → ZMod p) j).val : R)) = _
        simp [Pi.single_apply, apply_ite, ZMod.val_one]
      rw [Pi.sub_apply, e, hl i, sub_self]
      exact zero_mem _
  exact ⟨((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective f hsurj)).symm⟩

end PositivityTheory.HtPt.Rh
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RdBase
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F]

theorem mem_aug {X : Type} [AddCommGroup X] {M : Submodule R (X → C)} {g : X → C} :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

section Pull

variable {X Y : Type} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

theorem eig_zero {M : Submodule R (X → C)} {χ : MulChar F R} {g : X → C} (hg : g ∈ eig M χ) :
    g 0 = 0 := by
  have := hg.2 0 0
  rwa [smul_zero, MulChar.map_zero, map_zero, zero_mul] at this

theorem eig_pull (u : X →ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g ∈ M, g ∘ u ∈ M') {χ : MulChar F R} {g : Y → C} (hg : g ∈ eig M χ) :
    g ∘ u ∈ eig M' χ :=
  ⟨h g hg.1, fun a x => by simpa using hg.2 a (u x)⟩

theorem sq_pull (u : X →ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g ∈ M, g ∘ u ∈ M') {g : Y → C} (hg : g ∈ sqIdeal (augIdeal M)) :
    g ∘ u ∈ sqIdeal (augIdeal M') := by
  have : (sqIdeal (augIdeal M)).map (LinearMap.funLeft R C u) ≤ sqIdeal (augIdeal M') := by
    rw [sqIdeal, Submodule.map_span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine Submodule.subset_span ⟨a ∘ u, ⟨h a ha.1, ?_⟩, b ∘ u, ⟨h b hb.1, ?_⟩, rfl⟩
    · show a (u 0) = 0
      rw [map_zero]; exact ha.2
    · show b (u 0) = 0
      rw [map_zero]; exact hb.2
  exact this (Submodule.mem_map_of_mem hg)

theorem hasLen_transport (e : X ≃ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g, g ∈ M ↔ g ∘ e ∈ M') {χ : MulChar F R} {x : NNReal}
    (hx : HasLen v R (OmType M' χ) x) : HasLen v R (OmType M χ) x := by
  have h1 : ∀ g ∈ M, g ∘ (e : X →ₗ[F] Y) ∈ M' := fun g hg => (h g).1 hg
  have c1 : ∀ g : X → C, (g ∘ (e.symm : Y →ₗ[F] X)) ∘ e = g := fun g => by
    funext x; simp
  have c2 : ∀ g : Y → C, (g ∘ e) ∘ (e.symm : Y →ₗ[F] X) = g := fun g => by
    funext x; simp
  have h2 : ∀ g ∈ M', g ∘ (e.symm : Y →ₗ[F] X) ∈ M := fun g hg => by
    rw [h, c1]; exact hg
  let φ : eig M χ ≃ₗ[R] eig M' χ :=
    { toFun := fun g => ⟨g.1 ∘ e, eig_pull (e : X →ₗ[F] Y) h1 g.2⟩
      invFun := fun g => ⟨g.1 ∘ (e.symm : Y →ₗ[F] X), eig_pull _ h2 g.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun g => Subtype.ext (c2 g.1)
      right_inv := fun g => Subtype.ext (c1 g.1) }
  obtain ⟨m, c, ⟨ψ⟩, hx⟩ := hx
  refine ⟨m, c, ⟨(Submodule.Quotient.equiv _ _ φ ?_).trans ψ⟩, hx⟩
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hg
    have : (g.1 ∘ (e.symm : Y →ₗ[F] X)) ∘ e ∈ sqIdeal (augIdeal M') :=
      sq_pull (e : X →ₗ[F] Y) h1 hg
    rw [c1] at this
    exact this
  · intro hg
    exact sq_pull (e.symm : Y →ₗ[F] X) h2 hg

end Pull

variable {N : Type} [AddCommGroup N] [Module F N]

theorem hasLen_trivial (hv : v.Integers R) [Subsingleton N] {M : Submodule R (N → C)}
    {χ : MulChar F R} {x : NNReal} (hx : HasLen v R (OmType M χ) x) : x = 1 := by
  have : Subsingleton (eig M χ) := ⟨fun a b => Subtype.ext (funext fun y => by
    rw [Subsingleton.elim y 0, eig_zero a.2, eig_zero b.2])⟩
  have : Subsingleton (OmType M χ) := (Submodule.Quotient.mk_surjective _).subsingleton
  refine hasLen_unique hv hx ⟨0, Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, by simp⟩

theorem quot_step (M : Submodule R (N → C)) {L K : Submodule F N} (hLK : L ≤ K) (t : N) :
    stepOrder (M.comap (LinearMap.funLeft R C (L.mkQ : N → N ⧸ L))) (K.map L.mkQ) (L.mkQ t) =
      stepOrder M K t := by
  ext h
  constructor
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    refine ⟨g ∘ L.mkQ, ⟨hg, fun x k hk => ?_⟩, ?_⟩
    · show g (L.mkQ (x + k)) = g (L.mkQ x)
      rw [map_add (f := _)]
      exact hi _ _ (Submodule.mem_map_of_mem hk)
    · funext a
      show g (L.mkQ (a • t)) = g (a • L.mkQ t)
      rw [map_smul]
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    have hsur := L.mkQ_surjective
    have key : ∀ x, g (Function.surjInv hsur (L.mkQ x)) = g x := fun x => by
      have h1 : L.mkQ (Function.surjInv hsur (L.mkQ x) - x) = 0 := by
        rw [map_sub, Function.surjInv_eq hsur, sub_self]
      have h2 : Function.surjInv hsur (L.mkQ x) - x ∈ K :=
        hLK ((Submodule.Quotient.mk_eq_zero L).1 h1)
      have := hi x _ h2
      rwa [add_sub_cancel] at this
    refine ⟨g ∘ Function.surjInv hsur, ⟨?_, ?_⟩, ?_⟩
    · show (fun x => g (Function.surjInv hsur (L.mkQ x))) ∈ M
      simpa only [key] using hg
    · rintro x _ ⟨k, hk, rfl⟩
      obtain ⟨x, rfl⟩ := hsur x
      show g (Function.surjInv hsur (L.mkQ x + L.mkQ k)) = g (Function.surjInv hsur (L.mkQ x))
      rw [← map_add (f := _), key, key]
      exact hi x k hk
    · funext a
      show g (Function.surjInv hsur (a • L.mkQ t)) = g (a • t)
      rw [← map_smul, key]

theorem sub_stepRes (M : Submodule R (N → C)) {L K : Submodule F N} (hKL : K ≤ L) (t : L) :
    stepOrderRes (M.map (LinearMap.funLeft R C (Subtype.val : L → N))) (K.comap L.subtype) t =
      stepOrderRes M K (t : N) := by
  ext h
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, e⟩
    exact ⟨g, hg, fun a k hk => e a ⟨k, hKL hk⟩ hk⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨_, ⟨g, hg, rfl⟩, fun a k hk => e a k hk⟩

theorem hasLen_line (M : Submodule R (N → C)) {t : N} (ht : t ≠ 0) {χ : MulChar F R} {x : NNReal}
    (hx : HasLen v R (OmType (stepOrder M (⊥ : Submodule F N) t) χ) x) :
    HasLen v R (OmType (M.map (LinearMap.funLeft R C
      (Subtype.val : Submodule.span F {t} → N))) χ) x := by
  refine hasLen_transport (LinearEquiv.toSpanNonzeroSingleton F N t ht) (fun g => ?_) hx
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, ⟨hg, fun x k hk => ?_⟩, rfl⟩
    obtain rfl : k = 0 := hk
    rw [add_zero]
  · rintro ⟨g', ⟨hg, -⟩, e⟩
    refine ⟨g', hg, ?_⟩
    funext y
    obtain ⟨a, rfl⟩ := (LinearEquiv.toSpanNonzeroSingleton F N t ht).surjective y
    exact congrFun e a

end PositivityTheory.HtPt.Rd
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CompMemAddFun
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
lemma comp_mem_addFun (p : ℕ) (e : X ≃+ Y) {f : Y → C} (hf : f ∈ addFun R p Y) :
    (fun x => f (e x)) ∈ addFun R p X := by
  have h : ∀ a b : Y, f (a + b) - f a - f b ∈ pInt R p := hf
  show ∀ a b : X, f (e (a + b)) - f (e a) - f (e b) ∈ pInt R p
  intro a b
  rw [map_add (f := _)]
  exact h (e a) (e b)

private theorem map_pbE_eq_of_addEquiv (e : X ≃+ Y) (SX : Submodule R (X → C)) (SY : Submodule R (Y → C))
    (h1 : ∀ f ∈ SY, (fun x => f (e x)) ∈ SX) (h2 : ∀ g ∈ SX, (fun y => g (e.symm y)) ∈ SY) :
    SY.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = SX := by
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro h
    have h3 := h1 _ h
    convert h3 using 1
    funext x
    rw [pbE_symm_apply]
    simp
  · intro h
    convert h2 g h using 1
    funext y
    exact pbE_symm_apply e g y

lemma map_addFun (p : ℕ) (e : X ≃+ Y) :
    (addFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = addFun R p X := by
  exact map_pbE_eq_of_addEquiv e _ _ (fun f hf => comp_mem_addFun p e hf) (fun g hg => comp_mem_addFun p e.symm hg)

lemma map_intFun (e : X ≃+ Y) :
    (intFun R Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = intFun R X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    have h : ∀ y : Y, ∃ r : R, algebraMap R C r = f y := hf
    show ∀ x : X, ∃ r : R, algebraMap R C r = f (e x)
    exact fun x => h (e x)
  · intro g hg
    have h : ∀ x : X, ∃ r : R, algebraMap R C r = g x := hg
    show ∀ y : Y, ∃ r : R, algebraMap R C r = g (e.symm y)
    exact fun y => h (e.symm y)

lemma map_pFun (p : ℕ) (e : X ≃+ Y) :
    (pFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = pFun R p X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hf ⊢
    exact fun x => hf (e x)
  · intro g hg
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hg ⊢
    exact fun y => hg (e.symm y)

lemma map_afFun (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (afFun p M).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      afFun p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
  show Submodule.map _ (M ⊓ addFun R p Y) = _ ⊓ addFun R p X
  rw [Submodule.map_inf, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

lemma map_linFun (p : ℕ) (e : X ≃+ Y) :
    (linFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = linFun R p X := by
  show Submodule.map _ (intFun R Y ⊓ addFun R p Y) = intFun R X ⊓ addFun R p X
  rw [Submodule.map_inf, map_intFun, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

private theorem nonempty_quotient_linearEquiv_map {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (φ : V ≃ₗ[R] W) (L A : Submodule R V) :
    Nonempty ((↥L ⧸ Submodule.comap L.subtype A) ≃ₗ[R]
      (↥(L.map (φ : V →ₗ[R] W)) ⧸ Submodule.comap (L.map (φ : V →ₗ[R] W)).subtype (A.map (φ : V →ₗ[R] W)))) := by
  refine ⟨Submodule.Quotient.equiv _ _ (φ.submoduleMap L) ?_⟩
  ext ⟨w, hw⟩
  constructor
  · rintro ⟨⟨v, hv⟩, hvA, hvw⟩
    have hw' : φ v = w := congrArg Subtype.val hvw
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hvA ⊢
    exact ⟨v, hvA, hw'⟩
  · intro h
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at h
    obtain ⟨v, hvA, rfl⟩ := h
    obtain ⟨v', hv'L, hv'⟩ := hw
    have hvv : v' = v := φ.injective hv'
    subst hvv
    exact ⟨⟨v', hv'L⟩, hvA, rfl⟩

lemma afQuot_equiv (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    Nonempty (AFQuot p M ≃ₗ[R]
      AFQuot p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)))) := by
  obtain ⟨f⟩ := nonempty_quotient_linearEquiv_map (pbE (C := C) (R := R) e) (linFun R p Y) (afFun p M ⊔ pFun R p Y)
  rw [map_linFun, Submodule.map_sup, map_afFun, map_pFun] at f
  exact ⟨f⟩

end

lemma exists_coord (p : ℕ) [Fact p.Prime] (N : Type) [AddCommGroup N] [Finite N]
    [Module (ZMod p) N] : ∃ n : ℕ, Nonempty ((Fin n → ZMod p) ≃+ N) :=
  have : Module.Finite (ZMod p) N := Module.Finite.of_finite
  ⟨_, ⟨(Module.finBasis (ZMod p) N).equivFun.symm.toAddEquiv⟩⟩

private theorem genAF_bot_of_span_monomials {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {N : Type} [AddCommGroup N] (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R (N → C))
    (y : ι → N → C) (hy : ∀ j, y j ∈ afFun p M) (S : Set (N → C))
    (hS : M = Submodule.span R S) (hgen : ∀ s ∈ S, ∃ α : ι → ℕ, s = ∏ j, y j ^ α j) :
    GenAF p M ⊥ := by
  have hinv : invFun M (⊥ : AddSubgroup N) = M := by
    ext g
    constructor
    · intro h
      exact (show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x from h).1
    · intro h
      show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x
      refine ⟨h, ?_⟩
      intro x k hk
      rw [AddSubgroup.mem_bot] at hk
      subst hk
      simp
  show invFun M ⊥ ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p (invFun M ⊥) : Set (N → C)))
  rw [hinv]
  have hsp : Submodule.span R S ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p M : Set (N → C))) := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨α, rfl⟩ := hgen s hs
    exact (Subalgebra.mem_toSubmodule _).mpr
      (Subalgebra.prod_mem _ (fun j _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (hy j)) _))
  intro g hg
  rw [hS] at hg
  exact hsp hg

theorem cnt_of (hcoord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  intro p _ C _ _ _ v R _ _ hvR hp N _ _ _ hN AA cA cN hA hC
  letI : Module (ZMod p) N := AddCommGroup.zmodModule hN
  obtain ⟨n, ⟨e⟩⟩ := exists_coord p N
  have hcard : Fintype.card (Fin n → ZMod p) = Fintype.card N := Fintype.card_congr e.toEquiv
  obtain ⟨f⟩ := afQuot_equiv (C := C) (R := R) p e AA.carrier
  have hA' : HasLen v R (AFQuot p (hopfPull e AA).carrier) cA := by
    obtain ⟨m, c, ⟨g⟩, hc⟩ := hA
    exact ⟨m, c, ⟨f.symm.trans g⟩, hc⟩
  have hC' : HasColen R v (hopfPull e AA).carrier cN := hasColen_map v e _ _ hC
  obtain ⟨hle, heq⟩ := hcoord p C v R hvR hp (Fin n) (hopfPull e AA) cA cN hA' hC'
  rw [hcard] at hle heq
  refine ⟨hle, fun hE => ?_⟩
  obtain ⟨x, hxj, hspan⟩ := heq hE
  refine genAF_bot_of_span_monomials p AA.carrier (fun j z => x j (e.symm z)) ?_
    ((⇑(pbE (C := C) (R := R) e.symm)) '' Set.range
      (fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)) ?_ ?_
  · intro j
    have hx' : x j ∈ (afFun p AA.carrier).map
        (pbE (C := C) (R := R) e : (N → C) →ₗ[R] ((Fin n → ZMod p) → C)) := by
      rw [map_afFun]
      exact hxj j
    have h2 := (Submodule.mem_map_equiv _).mp hx'
    convert h2 using 1
    funext z
    rw [pbE_symm_apply]
  · have h1 := Submodule.map_span (pbE (C := C) (R := R) e.symm : ((Fin n → ZMod p) → C) →ₗ[R] (N → C))
      (Set.range fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)
    rw [← hspan] at h1
    rw [← map_pbE_symm e AA.carrier]
    exact h1
  · rintro s ⟨_, ⟨α, rfl⟩, rfl⟩
    refine ⟨fun j => (α j).val, ?_⟩
    funext z
    rw [Finset.prod_apply]
    rfl

end PositivityTheory.HtPt.Ra
end
end

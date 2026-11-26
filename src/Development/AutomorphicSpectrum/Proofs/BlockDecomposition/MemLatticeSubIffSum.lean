module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatSpan

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B]

theorem dpE_mul (f : W →+* B) (ξ : W) (l M i j : ℕ) :
    Lat.dpE f ξ l M i * Lat.dpE f ξ l M j =
      ((i + j).choose i : B) * Lat.dpE f ξ l M (i + j) := by
  have hc : (((i + j).choose i : ℕ) : ℚ) * ((i + j).factorial : ℚ)⁻¹ =
      ((i.factorial : ℚ))⁻¹ * ((j.factorial : ℚ))⁻¹ := by
    have h := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [← Nat.choose_symm_add] at h
    have h' : (((i + j).choose i : ℕ) : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) =
        ((i + j).factorial : ℚ) := by exact_mod_cast h
    have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    rw [← h']
    have hcne : (((i + j).choose i : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
    field_simp
  unfold Lat.dpE
  rw [smul_mul_smul_comm, ← pow_add, ← hc, ← smul_smul, ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul ℚ]

theorem mem_span_of_mem_sub (f : W →+* B) (ξ : W) (l M : ℕ) (x : B) (hx : x ∈ Lat.sub f ξ l M) :
    letI : Algebra W B := f.toAlgebra;
    x ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
  letI : Algebra W B := f.toAlgebra
  have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
  have h0 : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]
  have hgen : ∀ i, Lat.dpE f ξ l M i ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have hW : ∀ w : W, f w ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro w
    have h := Submodule.smul_mem _ w (hgen 0)
    rwa [hsm, h0, mul_one] at h
  have hnat : ∀ (n : ℕ) (y : B), y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      (n : B) * y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro n y hy
    have h := Submodule.smul_mem _ (n : W) hy
    rwa [hsm, map_natCast] at h
  have hmul : ∀ a b : B, a ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      a * b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨j, rfl⟩ := hb
        rw [dpE_mul]
        exact hnat _ _ (hgen _)
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ w hy
    | zero => simp
    | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
    | smul w y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ w hy
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact hW w
    · exact hgen i
  | zero => exact Submodule.zero_mem _
  | one => rw [← h0]; exact hgen 0
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | neg y _ hy => exact Submodule.neg_mem _ hy
  | mul y z _ _ hy hz => exact hmul y z hy hz

theorem mem_sub_iff : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (x : B), x ∈ Lat.sub f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), x = ∑ i, f (c i) * Lat.dpE f ξ l M i := by
  intro W B _ _ _ f ξ l M x
  constructor
  · intro hx
    letI : Algebra W B := f.toAlgebra
    have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_of_mem_sub f ξ l M x hx)
    refine ⟨c.support.sup id + 1, fun i => c i, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M i), Finsupp.sum]
    have hsub : c.support ⊆ Finset.range (c.support.sup id + 1) := by
      intro i hi
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    rw [Finset.sum_congr rfl (fun i _ => hsm (c i) (Lat.dpE f ξ l M i))]
    refine Finset.sum_subset hsub fun i _ hi => ?_
    rw [Finsupp.notMem_support_iff.1 hi, map_zero, zero_mul]
  · rintro ⟨n, c, rfl⟩
    refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inl ⟨c i, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.LatSpan
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSumStatement
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lattice_sub_iff_sum : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (x : B), x ∈ Lat.sub f ξ l M ↔ ∃ (n : ℕ) (c : Fin n → W), x = ∑ i, f (c i) * Lat.dpE f ξ l M i := by
  first | exact @GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff | exact GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff | (intros; apply GlobalTheory.CompanionTheory.LatSpan.mem_sub_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdeal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeUnit

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem pt_of_hom {T T' : Thick (smFun X q)} (φ : T ⟶ T') :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T = pt T' := by
  have := φ.pt
  unfold pt
  rw [← this]
  rfl

theorem spec_comp {C : Type 1} [Category.{0} C] (g : C ⥤ Thick (smFun X q)) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) := by
  have hφ : (g.map (a ≫ b)).φ = (g.map b).φ.comp (g.map a).φ := by rw [g.map_comp]; rfl
  rw [← Spec.map_comp]
  congr 1
  ext x
  show Ideal.Quotient.mk _ ((g.map (a ≫ b)).φ x) = Ideal.Quotient.mk _ ((g.map b).φ ((g.map a).φ x))
  rw [hφ]
  rfl

theorem u_points (D : E.LineData X) {V : Scheme.{0}} {a a' b : V ⟶ D.Y} (ha : a = a')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b ≫ D.f) : D.u a b h = D.u a' b h' := by
  subst ha
  rfl

theorem gamma_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) :=
  congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem r_sub_mem {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D)
    {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) (hc : c = a ≫ b) :
    ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈
      (g.obj c₂).J := by
  subst hc
  have ea := pt_of_hom (g.map a)
  have eb := pt_of_hom (g.map b)
  have ec := pt_of_hom (g.map (a ≫ b))
  have h1 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₁ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ea]
  have h2 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, eb]
  have h3 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ec]
  have wa := Λ.hw a h1
  have wb := Λ.hw b h2
  have wc := Λ.hw (a ≫ b) h3
  have nat := D.nat (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle))) _ _ h1
  have h12 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f := by
    simpa only [Category.assoc] using
      congrArg (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ ·) h1
  have coc := D.coc _ _ _ h12 h2
  have uc := u_points D (show Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ
      (g.map (a ≫ b)).hle)) ≫ Λ.p c₀ = _ by rw [spec_comp, Category.assoc]) h3 (h12.trans h2)
  have A : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) =
      (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c₂).B ⧸ (g.obj c₂).J))).hom.hom
        (D.u _ _ h12).1 := by
    show Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle (Ideal.Quotient.mk (g.obj c₁).J (Λ.w a)) = _
    rw [wa, nat, ← gamma_nat]
    rfl
  have B : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) *
      Ideal.Quotient.mk (g.obj c₂).J (Λ.w b) = Ideal.Quotient.mk (g.obj c₂).J (Λ.w (a ≫ b)) := by
    rw [A, wb, wc, ← map_mul, ← Units.val_mul, coc, uc]
  rw [← Ideal.Quotient.eq, map_one, Units.val_mul, Units.val_mul, map_mul, map_mul, B, ← map_mul, Units.mul_inv, map_one]

theorem r_sub_one : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (σ : ComposableArrows C 2), ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1) ∈ (g.obj (σ.obj (Fin.last 2))).J := by
  intro K _ _ X q C _ g D Λ σ
  exact r_sub_mem Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (by
    rw [← Functor.map_comp]
    rfl)

end GlobalTheory.CompanionTheory.ConeUnit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_lift_ratio_mem_ideal : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (σ : ComposableArrows C 2), ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1) ∈ (g.obj (σ.obj (Fin.last 2))).J := by
  first | exact @GlobalTheory.CompanionTheory.ConeUnit.r_sub_one | exact GlobalTheory.CompanionTheory.ConeUnit.r_sub_one | (intros; apply GlobalTheory.CompanionTheory.ConeUnit.r_sub_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem rep_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z s - z' s ∈ b.S _) (hr : Rep a b z c) : Rep a b z' c := by
  obtain ⟨f, hf, hc, hz⟩ := hr
  exact ⟨f, hf, hc, fun s => (hz s).trans (Ideal.Quotient.eq.2 (h s))⟩

section Frame
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ} (E : Frame (Φ := Φ) d)
  (σ : ∀ T : C, E.D ⟶ T) {t : Fin d → Φ.A.obj E.D} (ht : E.Coords t) {u : Fin d → ∀ T : C, Φ.A.obj T}
  (hu : ∀ i T, (Φ.A.map (σ T)).hom (t i) = u i T)

include ht hu

theorem a_eq (i : Fin d) {T T' : C} (φ : T ⟶ T') : E.a σ i φ = u i T' - (Φ.A.map φ).hom (u i T) := by
  have e : (Φ.A.map (σ T ≫ φ)).hom (t i) = (Φ.A.map φ).hom ((Φ.A.map (σ T)).hom (t i)) := by
    rw [Functor.map_comp]; rfl
  rw [Frame.a, ht, hu, e, hu]

theorem form_eq {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C j) :
    E.form σ I x s = wz u I s * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form wz
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [a_eq E σ ht hu]

theorem form_sub_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {r : ℕ} (I : Fin r → Fin d) (x : Φ.A.obj E.D)
    (s : ComposableArrows C r) (l : Φ.A.obj (s.obj (Fin.last r)))
    (hl : (Φ.A.map (σ _)).hom x - l ∈ Φ.J.S _) :
    E.form σ I x s - wz u I s * l ∈ (Fil ((r : ℤ) + 1)).S _ := by
  have hm : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T' := fun i T T' φ => by
    rw [← a_eq E σ ht hu]
    exact E.mem _ _ _
  have h1 := wz_mem hF u hm I s
  have h2 : (Φ.A.map (σ _)).hom x - l ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    simpa [hF.one] using hl
  have h3 := hF.mul r 1 _ h1 h2
  rw [form_eq E σ ht hu, ← mul_sub]
  simpa using h3

end Frame

theorem stLoc : StFrame → KH.LocGr → KH.PolyTf → StLoc := by
  intro hFr hLoc hPoly O _ l s hb X q W d c u hu r hr
  obtain ⟨E, σ, θ, hGr, hbot, hco, hσ, hpt⟩ := hFr l s hb q c u hu
  obtain ⟨Q, hQ⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hF : IsFil (sP (SS q l s W)) (sFil (SS q l s W)) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)
  obtain ⟨-, hL⟩ := hLoc Q hF E σ hGr (r : ℤ) (fun r' h => (hQ r' (by omega)).1) r
  obtain ⟨h2, h3⟩ := hL 0 (by simp)
  have hin : ∀ T : (SS q l s W).FullSubcategory, InU W T.obj := fun T => by
    obtain ⟨-, V, hV, h⟩ := T.property
    rwa [Set.mem_singleton_iff.1 hV] at h
  have key : ∀ (y : Idx r d → Γ(X, W)) (z : ComposableArrows (SS q l s W).FullSubcategory r),
      (∑ I : Idx r d, E.form σ I.1 (θ (y I)) z) - (∑ I : Idx r d,
        wz (Φ := sP (SS q l s W)) (fun i T => u i T.obj) I.1 z *
          (show (sP (SS q l s W)).A.obj (z.obj (Fin.last r)) from lft W (z.obj (Fin.last r)).obj (y I))) ∈
        (sFil (SS q l s W) ((r : ℤ) + 1)).S _ := by
    intro y z
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    refine form_sub_mem E σ hco (u := fun i T => u i T.obj) (fun i T => hσ i T) hF I.1 _ z _ ?_
    have h := hpt _ (hin (z.obj (Fin.last r))) (y I)
    rw [← lft_spec _ (hin (z.obj (Fin.last r))) (y I)] at h
    exact Ideal.Quotient.eq.1 h
  refine ⟨fun cl => ?_, fun x hx => ?_⟩
  · obtain ⟨x, -, hx⟩ := h2 cl
    refine ⟨fun I => θ.symm (x I), ?_⟩
    refine rep_congr (fun z => ?_) hx
    have := key (fun I => θ.symm (x I)) z
    simpa using this
  · have h4 := h3 (fun I => θ (x I)) (fun I => by
      rw [hF.top _ (by simp)]
      trivial) (rep_congr (fun z => by
        have := Ideal.neg_mem_iff _ |>.2 (key x z)
        simpa using this) hx)
    funext I
    have h5 := h4 I
    have e : (sFil (SS q l s W) (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥ := by
      simpa using hbot 1 one_ne_zero
    rw [e] at h5
    exact θ.injective ((Ideal.mem_bot.1 h5).trans (map_zero θ).symm)

end GlobalTheory.CompanionTheory.GrForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrameStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_local_of_frame : GlobalTheory.CompanionTheory.GrForm.StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → GlobalTheory.CompanionTheory.GrForm.StLoc := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stLoc | exact GlobalTheory.CompanionTheory.GrForm.stLoc | (intros; apply GlobalTheory.CompanionTheory.GrForm.stLoc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem rep_add {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' z'' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : ∀ s, z'' s - (z s + z' s) ∈ b.S _) (hc : Rep a b z c) (hc' : Rep a b z' c') :
    Rep a b z'' (c + c') := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  obtain ⟨f', hf', rfl, e'⟩ := hc'
  refine ⟨f + f', by rw [map_add (f := _), hf, hf', add_zero], rfl, fun s => ?_⟩
  change (show sqM a b _ from f s).1 + (show sqM a b _ from f' s).1 = _
  rw [e s, e' s, ← map_add (f := _)]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem rep_neg {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z' s - (-z s) ∈ b.S _) (hc : Rep a b z c) : Rep a b z' (-c) := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  refine ⟨-f, by rw [map_neg, hf, neg_zero], rfl, fun s => ?_⟩
  change -(show sqM a b _ from f s).1 = _
  rw [e s, ← map_neg]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem sum_wz_sub {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    {ι : Type} [Fintype ι] (I : ι → Fin j → Fin d) (s : ComposableArrows C j)
    (y y' : ι → Φ.A.obj (s.obj (Fin.last j))) (h : ∀ i, y i - y' i ∈ Φ.J.S _) :
    ∑ i, wz u (I i) s * y i - ∑ i, wz u (I i) s * y' i ∈ (Fil ((j : ℤ) + 1)).S _ := by
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← mul_sub]
  have h1 : y i - y' i ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    exact h i
  have := hF.mul j 1 _ (wz_mem hF u hu (I i) s) h1
  rwa [Nat.cast_add, Nat.cast_one] at this

end Abstract

section Forms
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lft_add_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T (f + g) - (lft W T f + lft W T g) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), lft_spec T h, lft_spec T h, lft_spec T h, map_add (f := _), sub_self]

theorem lft_neg_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f : Γ(X, W)) :
    lft W T (-f) - (-lft W T f) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, lft_spec T h, lft_spec T h, map_neg, sub_self]

theorem lift_cocycle {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (i : Fin d)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' := by
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hu i _ (hP _ T'.property), ev_nat φ.hom (hP _ T.property) (hP _ T'.property),
    ← hu i _ (hP _ T.property)]
  exact sub_eq_zero.2 rfl

end Forms

theorem stAdd : StAdd := by
  intro O _ X q W d t u hu P hP r x x' c c' hc hc'
  have hF : IsFil (sP P) (sFil P) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hcoc := fun i {T T' : P.FullSubcategory} (φ : T ⟶ T') => lift_cocycle hu P hP i φ
  constructor
  · refine rep_add (fun s => ?_) hc hc'
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((x + x') I)))
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) +
        (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x' I)))
      (fun I => lft_add_sub _ (hP _ (s.obj (Fin.last r)).property) _ _)
    simpa only [mul_add, Finset.sum_add_distrib] using this
  · refine rep_neg (fun s => ?_) hc
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((-x) I)))
      (fun I => -(show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)))
      (fun I => lft_neg_sub _ (hP _ (s.obj (Fin.last r)).property) _)
    simpa only [mul_neg, Finset.sum_neg_distrib] using this

end GlobalTheory.CompanionTheory.GrForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAddStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_add : GlobalTheory.CompanionTheory.GrForm.StAdd := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stAdd | exact GlobalTheory.CompanionTheory.GrForm.stAdd | (intros; apply GlobalTheory.CompanionTheory.GrForm.stAdd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

def mulSq (a b : IdF A) (T : C) (y : A.obj T) : sqM a b T →ₗ[R] sqM a b T where
  toFun x := ⟨Ideal.Quotient.mk _ y * x.1, Ideal.mul_mem_left ((a.S T).map (Ideal.Quotient.mk (b.S T))) _ x.2⟩
  map_add' x x' := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_smul_comm _ _ _)

def mulMor (a b c : IdF A) (y : ∀ T : C, A.obj T)
    (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (A.map φ).hom (y T) ∈ c.S T')
    (hc : ∀ (T : C) {v w : A.obj T}, v ∈ c.S T → w ∈ a.S T → v * w ∈ b.S T) :
    CH.Mor (sq a b) (sq a b) (RingHom.id R) where
  G := 𝟭 C
  τ T := mulSq a b T (y T)
  nat {T T'} φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have key : ∀ w : A.obj T, w ∈ a.S T → Ideal.Quotient.mk (b.S T') (y T') * Ideal.Quotient.mk (b.S T') ((A.map φ).hom w) =
        Ideal.Quotient.mk (b.S T') ((A.map φ).hom (y T * w)) := by
      intro w hw
      rw [← map_mul, map_mul (A.map φ).hom, Ideal.Quotient.eq, ← sub_mul]
      exact hc _ (hy φ) (a.map_mem φ hw)
    exact Subtype.ext (key w hw)

end Abstract

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem sub_mem_of_lift {W : X.Opens} {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') (f : Γ(X, W))
    (v : T.B) (v' : T'.B) (hv : Ideal.Quotient.mk T.J v = ev T h f) (hv' : Ideal.Quotient.mk T'.J v' = ev T' h' f) :
    v' - φ.φ v ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [hv', ev_nat φ h h', ← hv]
  rfl

theorem lft_mul_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T f * lft W T g - lft W T (f * g) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, lft_spec T h, lft_spec T h, lft_spec T h, map_mul]

theorem J_mul_sFil (P : ObjectProperty (Thick (LL q))) (r : ℕ) (T : P.FullSubcategory) {v w : (sP P).A.obj T}
    (hv : v ∈ (sP P).J.S T) (hw : w ∈ (sFil P r).S T) : v * w ∈ (sFil P ((r : ℤ) + 1)).S T := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have h1 : v ∈ (sFil P 1).S T := by
    have e := hF.one T
    rw [e]
    exact hv
  have := hF.mul 1 r T (x := v) (y := w) h1 hw
  have e : (((1 + r : ℕ)) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  rwa [e] at this

def mulZ {W : X.Opens} (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (z : Γ(X, W)) :
    CH.Mor (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (RingHom.id O) :=
  mulMor (sFil P r) (sFil P ((r : ℤ) + 1)) (sP P).J (fun T => lft W T.obj z)
    (fun {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) z _ _
      (lft_spec _ (hP _ T.property) z) (lft_spec _ (hP _ T'.property) z))
    (fun T _ _ hv hw => J_mul_sFil P r T hv hw)

theorem units_mul_relation_rearrange_commRing {S : Type} [CommRing S] (y w l l' : S) : y * (w * l) - w * l' = (y * l - l') * w := by ring

theorem stAct : StAct := by
  intro O _ X q W P hP r z
  refine ⟨((mulZ P hP r z).pull r).toAddMonoidHom, ?_⟩
  intro d t u hu x c hc
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulZ P hP r z).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj z) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have hd := lft_mul_sub _ (hP _ (s.obj (Fin.last r)).property) z (x I)
    have := J_mul_sFil P r _ hd hw
    have e := units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (lft W (s.obj (Fin.last r)).obj z) (wz uu I.1 s) (lft W (s.obj (Fin.last r)).obj (x I))
      (lft W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

end GlobalTheory.CompanionTheory.GrForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormActionStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_action : GlobalTheory.CompanionTheory.GrForm.StAct := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stAct | exact GlobalTheory.CompanionTheory.GrForm.stAct | (intros; apply GlobalTheory.CompanionTheory.GrForm.stAct <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicative
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.PlogMul

open Polynomial

variable {B : Type} [CommRing B]

noncomputable def logPoly (c : ℕ → B) (s : ℕ) : B[X] :=
  ∑ k ∈ Finset.range s, C ((-1) ^ k * c k) * X ^ (k + 1)

theorem derivative_logPoly (c : ℕ → B) (hc : ∀ k : ℕ, c k * ((k : B) + 1) = 1) (s : ℕ) :
    derivative (logPoly c s) = ∑ k ∈ Finset.range s, (-X) ^ k := by
  unfold logPoly
  rw [derivative_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (C (c k) : B[X]) * ((k : B[X]) + 1) = 1 := by
    have := congrArg (C : B →+* B[X]) (hc k)
    simpa using this
  rw [derivative_C_mul, derivative_X_pow, neg_pow (X : B[X]) k]
  simp only [Nat.add_sub_cancel, map_mul, map_pow, map_neg, map_one, Nat.cast_add, Nat.cast_one]
  calc _ = (-1) ^ k * (C (c k) * ((k : B[X]) + 1)) * X ^ k := by
        simp only [map_add (f := _), map_natCast, map_one]; ring
    _ = _ := by rw [h1, mul_one]

theorem one_add_mul_geom {R : Type} [CommRing R] (u : R) (s : ℕ) :
    (1 + u) * ∑ k ∈ Finset.range s, (-u) ^ k = 1 - (-u) ^ s := by
  have := mul_neg_geom_sum (-u) s
  simpa using this

theorem geom_comp (s : ℕ) (u : B[X]) :
    (∑ k ∈ Finset.range s, (-X : B[X]) ^ k).comp u = ∑ k ∈ Finset.range s, (-u) ^ k := by
  induction s with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih]

theorem eval_logPoly_zero (c : ℕ → B) (s : ℕ) : (logPoly c s).eval 0 = 0 := by
  simp [logPoly, eval_finsetSum]

theorem eval_logPoly_mul (c : ℕ → B) (hc : ∀ k : ℕ, c k * ((k : B) + 1) = 1)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) (s : ℕ) {x y : B}
    (hxy : ∀ a b : ℕ, s ≤ a + b → x ^ a * y ^ b = 0) :
    (logPoly c s).eval ((1 + x) * (1 + y) - 1) = (logPoly c s).eval x + (logPoly c s).eval y := by
  set a : B[X] := C x * X with ha
  set Z : B[X] := (1 + a) * (1 + C y) - 1 with hZ
  set G : B[X] := (logPoly c s).comp Z - (logPoly c s).comp a - C ((logPoly c s).eval y) with hG
  have has : a ^ s = 0 := by
    have h := hxy s 0 (by simp)
    have h' : x ^ s = 0 := by simpa using h
    rw [ha, mul_pow, ← C_pow, h']
    simp
  have hZs : Z ^ s = 0 := by
    have hZ' : Z = a * (1 + C y) + C y := by rw [hZ]; ring
    rw [hZ', add_pow]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h0 := hxy i (s - i) (by omega)
    have : (a * (1 + C y)) ^ i * (C y) ^ (s - i) = C (x ^ i * y ^ (s - i)) * (X ^ i * (1 + C y) ^ i) := by
      rw [ha, C_mul, C_pow, C_pow, mul_pow, mul_pow]; ring
    rw [this, h0]
    simp
  have hderiv : derivative G = 0 := by
    have hda : derivative a = C x := by rw [ha]; simp
    have hdZ : derivative Z = C x * (1 + C y) := by
      rw [hZ]; simp [hda]
    have hD : derivative G = C x * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k)
        - C x * (∑ k ∈ Finset.range s, (-a) ^ k) := by
      rw [hG, derivative_sub, derivative_sub, derivative_C, sub_zero, derivative_comp, derivative_comp,
        derivative_logPoly c hc, hdZ, hda]
      rw [geom_comp, geom_comp]
    have h1 : (1 + a) * (∑ k ∈ Finset.range s, (-a) ^ k) = 1 := by
      rw [one_add_mul_geom, neg_pow, has]; simp
    have h2 : (1 + a) * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k) = 1 := by
      have := one_add_mul_geom Z s
      rw [neg_pow, hZs] at this
      have e : 1 + Z = (1 + a) * (1 + C y) := by rw [hZ]; ring
      rw [← e, this]; simp
    have h3 : (1 + a) * derivative G = 0 := by
      rw [hD]
      linear_combination (C x) * h2 - (C x) * h1
    have h4 : derivative G = (∑ k ∈ Finset.range s, (-a) ^ k) * ((1 + a) * derivative G) := by
      linear_combination (- derivative G) * h1
    rw [h4, h3, mul_zero]
  have hG0 : G.eval 0 = 0 := by
    simp [hG, hZ, ha, eval_comp, eval_logPoly_zero]
  have hGC : G = C (G.eval 0) := by
    ext n
    cases n with
    | zero => simp [coeff_zero_eq_eval_zero]
    | succ n =>
      have h := congrArg (fun (p : B[X]) => p.coeff n) hderiv
      simp only [coeff_derivative, coeff_zero] at h
      have hn : IsUnit ((n : B) + 1) := by
        have := hu (n + 1) (by omega)
        simpa using this
      have : G.coeff (n + 1) = 0 := hn.mul_left_eq_zero.1 h
      simp [this, coeff_C]
  have hG1 : G.eval 1 = 0 := by
    rw [hGC, hG0]; simp
  have : (logPoly c s).eval ((1 + x) * (1 + y) - 1) - (logPoly c s).eval x - (logPoly c s).eval y = 0 := by
    simpa [hG, hZ, ha, eval_comp] using hG1
  linear_combination this

theorem plogK_mul {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ)
    (hs : pdP δ s = ⊥) (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) {x y : B} (hx : x ∈ J) (hy : y ∈ J) :
    plogK δ s ((1 + x) * (1 + y) - 1) = plogK δ s x + plogK δ s y := by
  have hunit : ∀ k : ℕ, IsUnit ((k : B) + 1) := fun k => by
    have := hu (k + 1) (by omega)
    simpa using this
  choose c hc using fun k : ℕ => (hunit k).exists_left_inv
  have hlog : ∀ {z : B}, z ∈ J → plogK δ s z = (logPoly c s).eval z := by
    intro z hz
    simp only [plogK, logPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := δ.factorial_mul_dpow_eq_pow (n := k + 1) hz
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    rw [← h]
    linear_combination (-(-1 : B) ^ k * (k.factorial : B) * δ.dpow (k + 1) z) * hc k
  have hxy : ∀ a b : ℕ, s ≤ a + b → x ^ a * y ^ b = 0 := by
    intro a b hab
    have hmem : δ.dpow a x * δ.dpow b y ∈ pdP δ s := by
      refine Ideal.subset_span ⟨[(a, x), (b, y)], ?_, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hx
        · exact hy
      · simpa using hab
      · simp
    rw [hs, Ideal.mem_bot] at hmem
    rw [← δ.factorial_mul_dpow_eq_pow hx, ← δ.factorial_mul_dpow_eq_pow hy]
    linear_combination ((a.factorial : B) * (b.factorial : B)) * hmem
  have hz : (1 + x) * (1 + y) - 1 ∈ J := by
    have e : (1 + x) * (1 + y) - 1 = x + y + x * y := by ring
    rw [e]
    exact J.add_mem (J.add_mem hx hy) (J.mul_mem_right y hx)
  rw [hlog hz, hlog hx, hlog hy]
  exact eval_logPoly_mul c hc hu s hxy

end GlobalTheory.CompanionTheory.PlogMul
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicativeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_log_multiplicative : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ), pdP δ s = ⊥ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ {x y : B}, x ∈ J → y ∈ J → plogK δ s ((1 + x) * (1 + y) - 1) = plogK δ s x + plogK δ s y := by
  first | exact @GlobalTheory.CompanionTheory.PlogMul.plogK_mul | exact GlobalTheory.CompanionTheory.PlogMul.plogK_mul | (intros; apply GlobalTheory.CompanionTheory.PlogMul.plogK_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeXiMulDpowSucc
set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatDp

theorem mul_divPow_succ {B : Type} [CommRing B] [Algebra ℚ B] (c η : B) (i : ℕ) :
    (c * η) * (((i.factorial : ℚ)⁻¹) • η ^ i) =
      (c * ((i : B) + 1)) * ((((i + 1).factorial : ℚ)⁻¹) • η ^ (i + 1)) := by
  have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have key : ((i : B) + 1) * ((((i + 1).factorial : ℚ)⁻¹) • η ^ (i + 1)) =
      ((i.factorial : ℚ)⁻¹) • η ^ (i + 1) := by
    have h1 : ((i : B) + 1) = algebraMap ℚ B ((i : ℚ) + 1) := by simp
    rw [h1, ← Algebra.smul_def, smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [mul_assoc c ((i : B) + 1), key, mul_assoc c η]
  simp only [Algebra.mul_smul_comm, pow_succ]
  congr 2
  ring

theorem natPow_mul_inv_smul {B : Type} [CommRing B] [Algebra ℚ B] (x : B) (l M : ℕ) (hl : l ≠ 0) :
    (l : B) ^ M * ((((l : ℚ) ^ M)⁻¹) • x) = x := by
  have h0 : ((l : ℚ) ^ M) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl)
  have h1 : ((l : B) ^ M) = algebraMap ℚ B ((l : ℚ) ^ M) := by simp
  rw [h1, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem mul_divPow_eq_elem {B : Type} [CommRing B] [Algebra ℚ B] (x : B) (l M : ℕ) (hl : l ≠ 0) (i : ℕ) :
    x * (((i.factorial : ℚ)⁻¹) • ((((l : ℚ) ^ M)⁻¹) • x) ^ i) =
      ((l : B) ^ M * ((i : B) + 1)) *
        ((((i + 1).factorial : ℚ)⁻¹) • ((((l : ℚ) ^ M)⁻¹) • x) ^ (i + 1)) := by
  have h := mul_divPow_succ ((l : B) ^ M) ((((l : ℚ) ^ M)⁻¹) • x) i
  rwa [natPow_mul_inv_smul x l M hl] at h

theorem mul_divPow_eq : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ), l ≠ 0 → ∀ i : ℕ,
    f ξ * Lat.dpE f ξ l M i = ((l : B) ^ M * ((i : B) + 1)) * Lat.dpE f ξ l M (i + 1) := by
  intro W B _ _ _ f ξ l M hl i
  simp only [Lat.dpE, Lat.η]
  exact mul_divPow_eq_elem (f ξ) l M hl i

end GlobalTheory.CompanionTheory.LatDp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPow
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPow
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFiltration

theorem dpow_mem_span_pow {B : Type} [CommRing B] [Algebra ℚ B] {x : B}
    (δ : DividedPowers (Ideal.span {x})) (k : ℕ) {y : B} (hy : y ∈ Ideal.span {x}) :
    δ.dpow k y ∈ Ideal.span {x ^ k} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ δ hy, Algebra.smul_def, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem list_prod_dpow_mem {B : Type} [CommRing B] [Algebra ℚ B] {x : B}
    (δ : DividedPowers (Ideal.span {x})) (l : List (ℕ × B))
    (hl : ∀ q ∈ l, q.2 ∈ Ideal.span {x}) :
    (l.map fun q => δ.dpow q.1 q.2).prod ∈ Ideal.span {x ^ (l.map Prod.fst).sum} := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    have h1 := dpow_mem_span_pow δ q.1 (hl q (by simp))
    have h2 := ih (fun q' hq' => hl q' (by simp [hq']))
    rw [Ideal.mem_span_singleton] at h1 h2 ⊢
    exact mul_dvd_mul h1 h2

theorem dividedPowerFiltration_span_singleton {B : Type} [CommRing B] [Algebra ℚ B] (x : B)
    (δ : DividedPowers (Ideal.span {x})) (r : ℕ) :
    CrystallineSemistableComparison.Pb.pdP δ r = Ideal.span {x ^ r} := by
  apply le_antisymm
  · unfold CrystallineSemistableComparison.Pb.pdP
    rw [Ideal.span_le]
    rintro z ⟨l, hl, hr, rfl⟩
    have h := list_prod_dpow_mem δ l hl
    rw [Ideal.mem_span_singleton] at h
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    exact (pow_dvd_pow x hr).trans h
  · rw [Ideal.span_singleton_le_iff_mem]
    unfold CrystallineSemistableComparison.Pb.pdP
    apply Ideal.subset_span
    refine ⟨List.replicate r (1, x), ?_, ?_, ?_⟩
    · intro q hq
      rw [List.eq_of_mem_replicate hq]
      exact Ideal.mem_span_singleton_self x
    · simp
    · simp [δ.dpow_one (Ideal.mem_span_singleton_self x)]

theorem pdP_γB {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (r : ℕ) :
    pdP (Lat.γB f ξ) r = Ideal.span {f ξ ^ r} :=
  dividedPowerFiltration_span_singleton (f ξ) (Lat.γB f ξ) r

end GlobalTheory.CompanionTheory.DPFiltration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPowStatement
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_filtration_span_pow : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (r : ℕ), pdP (Lat.γB f ξ) r = Ideal.span {f ξ ^ r} := by
  first | exact @GlobalTheory.CompanionTheory.DPFiltration.pdP_γB | exact GlobalTheory.CompanionTheory.DPFiltration.pdP_γB | (intros; apply GlobalTheory.CompanionTheory.DPFiltration.pdP_γB <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeNatDividesLPow
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatticeUnit

theorem natCast_dvd_pow :
    ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
      Lat.Hyp f ξ l m → ∀ n : ℕ, n ≠ 0 →
        ∃ (k : ℕ) (u : Lat.A f ξ l M), (n : Lat.A f ξ l M) * u = (l : Lat.A f ξ l M) ^ k := by
  intro W B _ _ _ f ξ l M m h n hn
  obtain ⟨k, u, hu⟩ := h.unit n hn
  refine ⟨k, Lat.ofW f ξ l M u, ?_⟩
  rw [← map_natCast (Lat.ofW f ξ l M) n, ← map_mul, hu, map_pow, map_natCast]

end GlobalTheory.CompanionTheory.LatticeUnit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotallyComplexOfRingEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotallyComplexOfRingEquiv
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem isTotallyComplex_of_ringEquiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F']
    [NumberField F'] (e : F ≃+* F'), IsTotallyComplex F → IsTotallyComplex F' := by
  intro F F' _ _ _ _ e h
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have hr : (w.comap (e : F →+* F')).IsReal := (InfinitePlace.isReal_comap_iff e).2 hw
  exact InfinitePlace.not_isReal_iff_isComplex.2 (h.isComplex _) hr

end GlobalTheory.CompanionTheory.PTIso
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotallyComplexOfRingEquivStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_complex_of_ring_equiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), IsTotallyComplex F → IsTotallyComplex F' := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | exact GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfCubWeilOrthogonal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.OrthKer

theorem fibreDescent_transport' {X : Scheme.{0}} {m m' : X ⟶ X} (e : m = m')
    (P : (X ⟶ X) → Prop)
    (H : ∀ (V : X.Opens) (a : Γ(X, m' ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m' ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m' ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m'.app V).hom a' = a) :
    ∀ (V : X.Opens) (a : Γ(X, m ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m.app V).hom a' = a := by
  subst e; exact H


open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Chart in
theorem descends_fibre (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (hN : (N : K) ≠ 0)
    (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V))
    (ha : ∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤
      (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ
        ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V),
      ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) :
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a := by
  let A : Over (Spec (CommRingCat.of K)) := (Over.pullback f).obj G
  let ρ : ∀ (T : Over (Spec (CommRingCat.of K))) (t : T.left ⟶ S) (ht : T.hom ≫ f = t),
      (T ⟶ A) ≃* (Over.mk t ⟶ G) := fun T t ht => TorsionLift.ptsEquiv f G T t ht
  have hρ : ∀ T t ht x, (ρ T t ht x).left = x.left ≫ Limits.pullback.fst G.hom f :=
    fun T t ht x => TorsionLift.ptsEquiv_left f G T t ht x
  have hA : A.hom ≫ f = (G ⊗ Over.mk f).hom := Limits.pullback.condition.symm
  have hid : ρ A _ hA (𝟙 A) = fst G (Over.mk f) := Over.OverMorphism.ext (by
    rw [hρ]; exact Category.id_comp _)
  have ext : ∀ (u : A ⟶ A) (v : G ⊗ Over.mk f ⟶ G ⊗ Over.mk f),
      v ≫ fst _ _ = ρ A _ hA u → v ≫ snd _ _ = snd _ _ → v.left = u.left := by
    intro u v h1 h2
    apply Limits.pullback.hom_ext
    · exact (congrArg (·.left) h1).trans (hρ _ _ _ _)
    · exact (congrArg (·.left) h2).trans (Over.w u).symm
  have hm : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left = ((𝟙 A) ^ N : A ⟶ A).left := by
    refine ext _ _ ?_ (whiskerRight_snd _ _)
    rw [map_pow, hid, whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have hAb : IsAbelianScheme A := TLinPf.isAb_pullback f G hG
  have hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤)) := by
    simpa using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, h3, h1, h2⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hAb hu
  refine fibreDescent_transport' hm (fun t => ∃ y : Over.mk f ⟶ G, y ^ N = 1 ∧
    t = (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) ?_ V a ?_
  · intro V a ha
    refine existsUnique_descend_of_torsion_invariant A N V a fun y hy => ?_
    refine ha _ ⟨ρ (𝟙_ _) f (Category.id_comp _) y, by rw [← map_pow, hy, map_one], ?_⟩
    refine (ext _ _ ?_ (lift_snd _ _)).symm
    rw [lift_fst, map_mul, hid, _root_.mul_comm]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hρ, hρ, Over.comp_left, Category.assoc]
    rfl
  · rintro _ ⟨y, hy, rfl⟩
    exact ha y hy

theorem mem_kernel_of_cubWeil_orthogonal : ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) (p : Sp K ⟶ S) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ), (N : K) ≠ 0 → ∀ x : Over.mk p ⟶ B, x ^ N = 1 → (∀ y : Over.mk p ⟶ B, y ^ N = 1 → CubWeil c N x y 1) → Triv (translDiff B L.L x) := by
  intro K _ _ S t A _ _ hA L c n hn x hx hp
  let T : Over S := Over.mk t
  let m : A ⊗ T ⟶ A ⊗ T := ((𝟙 A) ^ n : A ⟶ A) ▷ T
  have m₁ : m ≫ fst A T = fst A T ^ n := by
    rw [whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have m₂ : m ≫ snd A T ≫ x = snd A T ≫ x := by rw [whiskerRight_snd_assoc]
  let ψ : Fin 4 → ((A ⊗ T).left ⟶ A.left) :=
    ![(fst A T * (snd A T ≫ x)).left, (fst A T).left, (snd A T ≫ x).left, (1 : A ⊗ T ⟶ A).left]
  obtain ⟨σ, hσ, hv⟩ := CubNondeg.exists_sigma c n (fst A T) (snd A T ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (fun k => m.left ≫ ψ k) (by
      funext k
      fin_cases k
      · show (m ≫ (fst A T * (snd A T ≫ x))).left = (fst A T ^ n * (snd A T ≫ x)).left
        rw [MonObj.comp_mul, m₁, m₂]
      · exact congrArg (fun q => q.left) m₁
      · exact congrArg (fun q => q.left) m₂
      · exact congrArg (fun q : A ⊗ T ⟶ A => q.left) (MonObj.comp_one m))
  obtain ⟨u, hu⟩ := CubNondeg.descend_linComb m.left (T := {y : T ⟶ A // y ^ n = 1})
    (fun y => (lift (fst A T * (snd A T ≫ y.1)) (snd A T)).left) (fun y => by
      rw [← Over.comp_left]
      congr 1
      ext1
      · rw [Category.assoc, m₁, MonObj.comp_pow, lift_fst, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one,
          _root_.mul_one]
      · simp [m])
    (fun V a ha => descends_fibre S A hA K t n hn V a (fun y hy => ha ⟨y, hy⟩)) L.L L.isLB ψ _ σ hσ
    (fun y z J hJ => by
      have e₁ := hv _ (lift (fst A T * (snd A T ≫ y.1)) (snd A T)) z J hJ
      have e₂ := hv _ (𝟙 (A ⊗ T)) z J hJ
      rw [lift_fst, lift_snd_assoc] at e₁
      rw [Category.id_comp, Category.id_comp] at e₂
      have w := (hp y.1 y.2).comp (snd A T)
      have w' := w.2.2 z J hJ
      rw [map_one, map_one, _root_.one_mul] at w'
      exact e₁.trans ((CubNondeg.ratio_translate (isCub_cubV c hJ) n _ _ _ w.1 w.2.1 w').trans e₂.symm))
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) L.L L.isLB (![x.left, (1 : T ⟶ A).left] : Fin 2 → _) ![1, -1]
  let s : T ⊗ A ⟶ A ⊗ T := lift (snd T A) (fst T A)
  have s₀ : s.left ≫ ψ 0 = (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left := by
    show (s ≫ (fst A T * (snd A T ≫ x))).left = ((fst T A ≫ x) * snd T A).left
    rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, mul_comm]
  have s₁ : s.left ≫ ψ 1 = (snd T A).left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_fst _ _)
  have s₂ : s.left ≫ ψ 2 = (fst T A).left ≫ x.left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_snd_assoc _ _ x)
  have s₃ : s.left ≫ ψ 3 = (fst T A).left ≫ (1 : T ⟶ A).left :=
    congrArg (fun q : T ⊗ A ⟶ A => q.left) ((MonObj.comp_one s).trans (MonObj.comp_one (fst T A)).symm)
  obtain ⟨w, hw, -⟩ := exists_gen L.isLB
    (φ' := (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (s.left ≫ ψ 0) ^ (1 : ℤ) * h (s.left ≫ ψ 1) ^ (-1 : ℤ) * h (s.left ≫ ψ 2) ^ (-1 : ℤ) *
        h (s.left ≫ ψ 3) ^ (1 : ℤ) * (h ((fst T A).left ≫ x.left) ^ (1 : ℤ) *
        h ((fst T A).left ≫ (1 : T ⟶ A).left) ^ (-1 : ℤ)) =
        h (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left ^ (1 : ℤ) * h (snd T A).left ^ (-1 : ℤ)
      rw [s₀, s₁, s₂, s₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u s.left) (LB.pullGen L.L _ _ g (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hg _))
  exact ⟨w, hw⟩

end GlobalTheory.OrthKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatEnt

def QSum {G : Type} [CommGroup G] (H : Subgroup G) (F : G → ℂ) (a : ℂ) : Prop :=
  HasSum (fun q : G ⧸ H => F q.out) a

section Generic

variable {G : Type} [CommGroup G] {H H' : Subgroup G} {F : G → ℂ} {a : ℂ}

theorem out_mk (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (g : G) : F (QuotientGroup.mk g : G ⧸ H).out = F g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hu, hF _ _ u.2]

theorem QSum.translate (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) (t : G) :
    QSum H (fun g => F (t * g)) a := by
  unfold QSum at *
  rw [← (Equiv.mulLeft (QuotientGroup.mk t : G ⧸ H)).hasSum_iff] at h
  refine h.congr_fun fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have h2 : ∀ g, ∀ u ∈ H, F (t * (g * u)) = F (t * g) := fun g u hu => by rw [← mul_assoc, hF _ _ hu]
  exact (out_mk (F := fun g => F (t * g)) h2 g).trans (out_mk hF (t * g)).symm

theorem QSum.eq_zero (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) {t : G} {c : ℂ} (hc : c ≠ 1)
    (ht : ∀ g, F (t * g) = c * F g) : a = 0 := by
  have h1 := h.translate hF t
  unfold QSum at *
  simp only [ht] at h1
  have h2 := h1.unique (h.mul_left c)
  have : (c - 1) * a = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

theorem qsum_index (hle : H ≤ H') (hn : H.relIndex H' ≠ 0) (hF : ∀ g, ∀ u ∈ H', F (g * u) = F g) :
    QSum H' F a ↔ QSum H F (H.relIndex H' * a) := by
  unfold QSum
  haveI : (H.subgroupOf H').FiniteIndex := ⟨hn⟩
  haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')
  have hc : (Fintype.card (H' ⧸ H.subgroupOf H') : ℂ) = H.relIndex H' := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have hn' : (H.relIndex H' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  let e := Subgroup.quotientEquivProdOfLE hle
  have he : ∀ q : G ⧸ H, F q.out = (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q) := fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [out_mk fun g u hu => hF g u (hle hu)]
    show _ = F (QuotientGroup.mk g : G ⧸ H').out * 1
    rw [out_mk hF, mul_one]
  simp only [he]
  rw [show (fun q => (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q)) =
    (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) ∘ e from rfl, e.hasSum_iff]
  have h1 : HasSum (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) (H.relIndex H') := by
    simpa [hc] using hasSum_fintype (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ))
  constructor
  · intro h
    rw [mul_comm]
    have h3 := summable_mul_of_summable_norm (f := fun q : G ⧸ H' => F q.out)
      (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h.summable.norm h1.summable.norm
    exact HasSum.mul (f := fun q : G ⧸ H' => F q.out) (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h h1 h3
  · intro h
    have h2 := (h.prod_fiberwise fun q => h1.mul_left (F q.out)).mul_right (H.relIndex H' : ℂ)⁻¹
    simp only [mul_assoc, mul_inv_cancel₀ hn', mul_one] at h2
    rwa [mul_left_comm, mul_inv_cancel₀ hn', mul_one] at h2

end Generic

variable {E : Type} [Field E] [NumberField E]

def box (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Set (Af E)ˣ :=
  {z | ∀ w, Valued.v ((z : Af E) w - 1) ≤ r w}

def congr (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Subgroup (Af E)ˣ where
  carrier := {z | ∀ w, Valued.v ((z : Af E) w) = 1 ∧ Valued.v ((z : Af E) w - 1) ≤ r w}
  one_mem' := fun w => by
    have : ((1 : (Af E)ˣ) : Af E) w = 1 := rfl
    rw [this]; simp
  mul_mem' := fun {a b} ha hb w => by
    have : ((a * b : (Af E)ˣ) : Af E) w = (a : Af E) w * (b : Af E) w := rfl
    rw [this]
    refine ⟨by rw [map_mul, (ha w).1, (hb w).1, one_mul], ?_⟩
    rw [show (a : Af E) w * (b : Af E) w - 1 = (a : Af E) w * ((b : Af E) w - 1) + ((a : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (ha w).1, one_mul]; exact (hb w).2) (ha w).2
  inv_mem' := fun {a} ha w => by
    have h : (a : Af E) w * ((a⁻¹ : (Af E)ˣ) : Af E) w = 1 := (coord w a).val_inv
    have h1 : Valued.v (((a⁻¹ : (Af E)ˣ) : Af E) w) = 1 := by
      have := congrArg Valued.v h
      rwa [map_mul, (ha w).1, one_mul, map_one] at this
    refine ⟨h1, ?_⟩
    rw [show ((a⁻¹ : (Af E)ˣ) : Af E) w - 1 = -(((a⁻¹ : (Af E)ˣ) : Af E) w * ((a : Af E) w - 1)) by
      linear_combination h, Valuation.map_neg, map_mul, h1, one_mul]
    exact (ha w).2

def radN (E : Type) [Field E] [NumberField E] (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : WithZero (Multiplicative ℤ) :=
  Valued.v (N : w.adicCompletion E)

def zterm (χ : HChar E) (s : ℂ) (z : (Af E)ˣ) : ℂ := (finPart χ z : ℂ) * ((modF z : ℝ) : ℂ) ^ s

theorem zterm_mul (χ : HChar E) (s : ℂ) (z z' : (Af E)ˣ) : zterm χ s (z * z') = zterm χ s z * zterm χ s z' := by
  unfold zterm
  rw [map_mul, ObjModel.modF_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ObjModel.modF_pos _).le (ObjModel.modF_pos _).le, Units.val_mul]
  ring

theorem differentiable_zterm (χ : HChar E) (z : (Af E)ˣ) : Differentiable ℂ fun s => zterm χ s z :=
  Differentiable.const_mul (Differentiable.const_cpow differentiable_id
    (Or.inl (by exact_mod_cast (ObjModel.modF_pos z).ne'))) _

theorem modF_eq_one {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) : modF u = 1 := by
  unfold modF
  exact finprod_eq_one_of_forall_eq_one fun v => by simp [hu v]

theorem zterm_unit (χ : HChar E) (s : ℂ) {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) :
    zterm χ s u = finPart χ u := by
  simp [zterm, modF_eq_one hu]

theorem norm_zterm {χ : HChar E} (h : IsUnitary χ) (s : ℂ) (z : (Af E)ˣ) : ‖zterm χ s z‖ = modF z ^ s.re := by
  have : ‖(finPart χ z : ℂ)‖ = 1 := h _
  rw [zterm, norm_mul, this, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ObjModel.modF_pos z)]

theorem mul_mem_box {r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} {z u : (Af E)ˣ} (hu : u ∈ congr r) :
    z * u ∈ box r ↔ z ∈ box r := by
  have key : ∀ z u : (Af E)ˣ, u ∈ congr r → z ∈ box r → z * u ∈ box r := fun z u hu hz w => by
    have : ((z * u : (Af E)ˣ) : Af E) w = (z : Af E) w * (u : Af E) w := rfl
    rw [this, show (z : Af E) w * (u : Af E) w - 1 = (u : Af E) w * ((z : Af E) w - 1) + ((u : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (hu w).1, one_mul]; exact hz w) (hu w).2
  exact ⟨fun h => by simpa using key _ _ (inv_mem hu) h, key _ _ hu⟩

theorem congr_mono {r r' : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} (h : ∀ w, r w ≤ r' w) :
    congr r ≤ congr r' := fun _ hz w => ⟨(hz w).1, (hz w).2.trans (h w)⟩

theorem mem_hatO_of_sub {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) {a z : Af E} (ha : a ∈ hatO c)
    (hz : ∀ P, Valued.v (z P - a P) ≤ radN E n P) : z ∈ hatO c := by
  have hn0 : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have key := GlobalTheory.IntDense.mem_of_isClosed E (C := {α | algebraMap E (Af E) n * α ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun a => by
      show _ ∈ hatO c
      rw [← map_mul]
      refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * a,
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩)
      simp) (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) fun P => by
      have h0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hn
      show Valued.v (algebraMap E (P.adicCompletion E) (n : E)⁻¹ * (z P - a P)) ≤ 1
      rw [map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
      exact hz P
  have e : z = algebraMap E (Af E) n * (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) + a := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, sub_add_cancel]
  rw [e]
  exact add_mem key ha

theorem congr_le_hatOUnits {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) :
    congr (radN E n) ≤ hatOUnits c := fun _ hu =>
  mem_hatOUnits.2 ⟨mem_hatO_of_sub hn hc (one_mem _) fun P => (hu P).2,
    mem_hatO_of_sub hn hc (one_mem _) fun P => (inv_mem hu P).2⟩

theorem hatOUnits_le_congr (c : Ideal (OF E)) : hatOUnits c ≤ congr (fun _ => 1) := fun u hu w => by
  have h : Valued.v ((u : Af E) w) = 1 :=
    GlobalTheory.Mem.TupHecke.valued_eq_one_of_le (coord w u) (ObjModel.hatO_integral hu.1 w) (ObjModel.hatO_integral hu.2 w)
  exact ⟨h, Valuation.map_sub_le _ h.le (by simp)⟩

end GlobalTheory.CMVal.LatEnt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapOneInjective
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj imForm imForm_apply herm_add_left herm_add_right
  herm_smul_left herm_smul_right herm_conj riemann_symm eq_zero_of_imForm det_ne_zero_of_pos colMat colMat_apply
  exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

def Tsp {O : Type} [Ring O] (bar : O → O) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) :
    Submodule ℂ (Matrix (Fin g) (Fin g) ℂ) where
  carrier := {S | Sᵀ = S ∧ ∀ a, S * (ρ (bar a)).map star = (ρ a)ᴴ * S}
  zero_mem' := ⟨by simp, fun a => by simp⟩
  add_mem' := by
    rintro S T ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [transpose_add, h1, h3], fun a => by rw [Matrix.add_mul, Matrix.mul_add, h2, h4]⟩
  smul_mem' := by
    rintro c S ⟨h1, h2⟩
    exact ⟨by rw [transpose_smul, h1], fun a => by rw [Matrix.smul_mul, Matrix.mul_smul, h2]⟩

theorem star_mulVec_map (M : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : star (M *ᵥ z) = M.map star *ᵥ star z := by
  funext i; simp [mulVec, dotProduct]

theorem herm_mulVec_left (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (A *ᵥ z) w = hermForm (Aᵀ * M) z w := by
  unfold hermForm
  rw [← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]

theorem herm_mulVec_right (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M z (A *ᵥ w) = hermForm (M * A.map star) z w := by
  unfold hermForm
  rw [star_mulVec_map, mulVec_mulVec]

theorem herm_single (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (i j : Fin g) :
    hermForm M (Pi.single i c) (Pi.single j 1) = c * M i j := by
  simp [hermForm, ← Pi.single_star, mulVec_single]

theorem sesq_ext {N N' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z w, (hermForm N z w).im = (hermForm N' z w).im) : N = N' := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have h2 := h (Pi.single i Complex.I) (Pi.single j 1)
  simp only [herm_single] at h1 h2
  simp at h1 h2
  apply Complex.ext <;> linarith

variable {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}

theorem ext_per {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) {W : Type} [AddCommGroup W] [Module ℝ W]
    {f f' : (Fin g → ℂ) →ₗ[ℝ] W} (h : ∀ x, f (P x) = f' (P x)) : f = f' :=
  LinearMap.ext_on_range hP.2.2.2.1 h

theorem relation_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P) (c : D.La →₀ ℝ)
    (hc : Finsupp.linearCombination ℝ P₀ c = 0) : Finsupp.linearCombination ℝ P c = 0 := by
  obtain ⟨M₀, -, -, h₀⟩ := hP₀.2.2.2.2
  obtain ⟨M, -, hpos, h⟩ := hP.2.2.2.2
  refine eq_zero_of_imForm hpos (ext_per hP fun y => ?_)
  have := congrArg (fun u => imForm M₀ u (P₀ y)) hc
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, imForm_apply, h, h₀, map_zero, LinearMap.zero_apply] at this ⊢
  exact this

theorem exists_colMat_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) :
    ∃ α β : Fin g → (D.La →₀ ℂ), ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D ρ P →
      ∀ x, P x = realMap (colMat α P) (colMat β P) (P₀ x) := by
  have hs : ∀ z : Fin g → ℂ, ∃ c : D.La →₀ ℝ, Finsupp.linearCombination ℝ P₀ c = z := fun z => by
    have : z ∈ Submodule.span ℝ (Set.range P₀) := by rw [hP₀.2.2.2.1]; trivial
    rwa [← Finsupp.range_linearCombination] at this
  choose r hr using fun j => hs (Pi.single j 1)
  choose r' hr' using fun j => hs (Pi.single j Complex.I)
  let k : (D.La →₀ ℝ) → (D.La →₀ ℂ) := Finsupp.mapRange (fun t => (t : ℂ)) (by simp)
  have hk : ∀ (f : D.La → Fin g → ℂ) c, Finsupp.linearCombination ℂ f (k c) = Finsupp.linearCombination ℝ f c :=
    fun f c => by
      simp only [Finsupp.linearCombination_apply, k]
      rw [Finsupp.sum_mapRange_index (by simp)]
      rfl
  refine ⟨fun j => (1 / 2 : ℂ) • k (r j) - (Complex.I / 2) • k (r' j),
    fun j => (1 / 2 : ℂ) • k (r j) + (Complex.I / 2) • k (r' j), fun P hP x => ?_⟩
  have := relation_per hP₀ hP (Finsupp.single x 1 - ∑ j, ((P₀ x j).re • r j + (P₀ x j).im • r' j)) (by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_add (f := _), map_smul, hr, hr', Finsupp.linearCombination_single, one_smul]
    funext i
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_add (f := _), map_smul, Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
  rw [this]
  funext i
  simp only [realMap_apply, Pi.add_apply, mulVec, dotProduct, colMat_apply, map_sub, map_add (f := _), map_smul, hk,
    Finset.sum_apply, ← Finset.sum_add_distrib, Pi.smul_apply, Pi.sub_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem comm_realMap_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (a : O) :
    ρ a * A = A * ρ a ∧ ρ a * B = B * (ρ a).map star := by
  refine realMap_inj (ext_per hP₀ fun x => ?_)
  have := h (a • x)
  rw [hP.1, hP₀.1, h] at this
  simp only [realMap_apply, mulVec_add, mulVec_mulVec, star_mulVec_map] at this ⊢
  exact this

theorem comm_herm_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M : Matrix (Fin g) (Fin g) ℂ}
    (hM : ∀ x y, (hermForm M (P₀ x) (P₀ y)).im = D.EF x y) (a : O) :
    (ρ a)ᵀ * M = M * (ρ (bar a)).map star := by
  have key : (imForm M).compl₁₂ (realMap (ρ a) 0) LinearMap.id =
      (imForm M).compl₁₂ LinearMap.id (realMap (ρ (bar a)) 0) := by
    refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
    simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
      ← hP₀.1, imForm_apply, hM, D.adj]
  refine sesq_ext fun z w => ?_
  have := LinearMap.congr_fun₂ key z w
  simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
    imForm_apply] at this
  rw [← herm_mulVec_left, ← herm_mulVec_right]
  exact this

theorem map_star_transpose (M : Matrix (Fin g) (Fin g) ℂ) : (M.map star)ᵀ = Mᴴ := rfl

theorem mem_Tsp_of_period {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {M₀ : Matrix (Fin g) (Fin g) ℂ} (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (hA : A.det ≠ 0) :
    (A⁻¹ * B)ᵀ * M₀ ∈ Tsp bar ρ := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨M, hM, -, hE⟩ := hP.2.2.2.2
    have key : (imForm M).compl₁₂ (realMap A B) (realMap A B) = imForm M₀ := by
      refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
      simp only [LinearMap.compl₁₂_apply, ← h, imForm_apply, hE, hM₀]
    ext i j
    rw [transpose_apply]
    refine riemann_symm (M := Aᵀ * M * A.map star) ?_ (fun z w => ?_) j i
    · have := isHermitian_conjTranspose_mul_mul (A.map star) hM
      convert this using 3
      ext i j; simp
    · rw [GlobalTheory.PeriodConn.hermForm_conj_mul]
      simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu]
      exact LinearMap.congr_fun₂ key z w
  · obtain ⟨h1, h2⟩ := comm_realMap_per hP₀ hP h a
    have h3 : ρ a * (A⁻¹ * B) = A⁻¹ * B * (ρ a).map star := by
      rw [Matrix.mul_assoc, ← h2]
      have : A⁻¹ * (ρ a * A) * A⁻¹ = A⁻¹ * (A * ρ a) * A⁻¹ := by rw [h1]
      rw [nonsing_inv_mul_cancel_left _ _ hu, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu] at this
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this]
    rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, h3, transpose_mul,
      map_star_transpose, Matrix.mul_assoc]

theorem comm_of_mem_Tsp {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M₀ : Matrix (Fin g) (Fin g) ℂ}
    (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y) (hdet : M₀.det ≠ 0) {C : Matrix (Fin g) (Fin g) ℂ}
    (hC : Cᵀ * M₀ ∈ Tsp bar ρ) (a : O) : ρ a * C = C * (ρ a).map star := by
  have hu : IsUnit M₀.det := isUnit_iff_ne_zero.mpr hdet
  have h := hC.2 a
  rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, ← map_star_transpose,
    ← Matrix.mul_assoc, ← transpose_mul] at h
  have := congrArg (· * M₀⁻¹) h
  simp only [mul_nonsing_inv_cancel_right _ _ hu] at this
  exact transpose_injective this

theorem realMap_one_injective {C : Matrix (Fin g) (Fin g) ℂ} (h : (1 - C * C.map star).det ≠ 0) :
    Function.Injective (realMap 1 C) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  rw [realMap_apply, one_mulVec] at hz
  have h1 : z = -(C *ᵥ star z) := eq_neg_of_add_eq_zero_left hz
  have h2 : star z = -(C.map star *ᵥ z) := by
    have := congrArg star hz
    rw [star_add, star_mulVec_map, star_star, star_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  refine eq_zero_of_mulVec_eq_zero h ?_
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← neg_neg (C.map star *ᵥ z), ← h2, mulVec_neg, ← h1, sub_self]

end

end GlobalTheory.PerCoordU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsSquareZeroPresentedScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsSquareZeroPresentedScheme
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PresCharts

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

theorem appLE_congr {A Y : Scheme.{0}} {f g : A ⟶ Y} (h : f = g) (U : Y.Opens) (W : A.Opens)
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

theorem specMap_appLE_top {A B : CommRingCat.{0}} (f : A ⟶ B) (e : (⊤ : (Spec B).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ f := by
  rw [← Scheme.ΓSpecIso_naturality]
  rfl

def chartOpen (P : S.Presents s i) (T : AffOp X₀) : X.Opens :=
  haveI := P.isOpen T
  (P.y T).opensRange

theorem preimage_chartOpen (P : S.Presents s i) (T : AffOp X₀) : P.y T ⁻¹ᵁ chartOpen P T = ⊤ := by
  haveI := P.isOpen T
  exact Scheme.Hom.preimage_opensRange _

def chartSec (P : S.Presents s i) (T : AffOp X₀) : Γ(X, chartOpen P T) ⟶ CommRingCat.of (S.F.obj T) :=
  (P.y T).appLE (chartOpen P T) ⊤ (preimage_chartOpen P T).ge ≫ (Scheme.ΓSpecIso _).hom

instance isIso_chartSec (P : S.Presents s i) (T : AffOp X₀) : IsIso (chartSec P T) := by
  haveI := P.isOpen T
  haveI : IsIso ((P.y T).app (chartOpen P T)) := Scheme.Hom.isIso_app _ _ le_rfl
  have h : homOfLE (preimage_chartOpen P T).ge = eqToHom (preimage_chartOpen P T).symm :=
    Subsingleton.elim _ _
  unfold chartSec Scheme.Hom.appLE
  rw [h]
  infer_instance

theorem chartOpen_le (P : S.Presents s i) ⦃T T' : AffOp X₀⦄ (a : T ⟶ T') : chartOpen P T' ≤ chartOpen P T := by
  haveI := P.isOpen T
  haveI := P.isOpen T'
  intro x hx
  change x ∈ ((P.y T').opensRange : Set X) at hx
  change x ∈ ((P.y T).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange] at hx ⊢
  obtain ⟨q, rfl⟩ := hx
  rw [← P.nat a, Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

theorem res_chartSec (P : S.Presents s i) ⦃T T' : AffOp X₀⦄ (a : T ⟶ T') :
    X.presheaf.map (homOfLE (chartOpen_le P a)).op ≫ chartSec P T' =
      chartSec P T ≫ CommRingCat.ofHom (mp S.F a : S.F.obj T →+* S.F.obj T') := by
  have e1 : (⊤ : (Sp (S.F.obj T')).Opens) ≤ P.y T' ⁻¹ᵁ chartOpen P T :=
    (preimage_chartOpen P T').ge.trans (Scheme.Hom.preimage_mono _ (chartOpen_le P a))
  unfold chartSec
  rw [← Category.assoc, Scheme.Hom.map_appLE _ _ (homOfLE (chartOpen_le P a)).op]
  rw [appLE_congr (P.nat a).symm _ _ e1]
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ (preimage_chartOpen P T).ge le_top]
  rw [Category.assoc, Category.assoc]
  congr 1
  exact specMap_appLE_top _ _

theorem injective_of_isPullback {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀}
    (hπ : Function.Surjective π) {s₀ : X₀ ⟶ Sp R₀} {s : X ⟶ Sp R} {i : X₀ ⟶ X}
    (h : IsPullback i s₀ s (spMap π)) : Function.Injective i := by
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
    (IsClosedImmersion.spec_of_surjective _ hπ)
  exact i.isClosedEmbedding.injective

theorem fromSpec_appLE_ΓSpecIso {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(Y, U)).hom = 𝟙 _ := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

theorem range_affPt (T : AffOp X₀) : Set.range (affPt s₀ T.unop) = T.unop.1 :=
  IsAffineOpen.range_fromSpec T.unop.2

theorem exists_of_mem_chartOpen (hI : I ^ 2 = 0) (P : S.Presents s i) (T : AffOp X₀) (x : X)
    (hx : x ∈ chartOpen P T) : ∃ x₀ ∈ T.unop.1, i x₀ = x := by
  haveI := P.isOpen T
  change x ∈ ((P.y T).opensRange : Set X) at hx
  rw [Scheme.Hom.coe_opensRange] at hx
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨q₀, rfl⟩ := (S.surjective_spMap_p hI T).surj q
  refine ⟨affPt s₀ T.unop q₀, ?_, ?_⟩
  · have : affPt s₀ T.unop q₀ ∈ Set.range (affPt s₀ T.unop) := Set.mem_range_self _
    rw [range_affPt] at this
    exact this
  · rw [← Scheme.Hom.comp_apply, ← P.red T, Scheme.Hom.comp_apply]

theorem le_preimage_chartOpen (P : S.Presents s i) (T : AffOp X₀) :
    T.unop.1 ≤ i ⁻¹ᵁ chartOpen P T := by
  haveI := P.isOpen T
  intro x₀ hx₀
  have hx' : x₀ ∈ Set.range (affPt s₀ T.unop) := by rw [range_affPt]; exact hx₀
  obtain ⟨q, rfl⟩ := hx'
  change i (affPt s₀ T.unop q) ∈ ((P.y T).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange, ← Scheme.Hom.comp_apply, ← P.red T, Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

theorem preimage_chartOpen_eq (hI : I ^ 2 = 0) (hinj : Function.Injective i) (P : S.Presents s i)
    (T : AffOp X₀) : i ⁻¹ᵁ chartOpen P T = T.unop.1 := by
  refine le_antisymm (fun x₀ hx₀ ↦ ?_) (le_preimage_chartOpen P T)
  obtain ⟨y₀, hy₀, e⟩ := exists_of_mem_chartOpen hI P T (i x₀) hx₀
  rw [← hinj e]
  exact hy₀

theorem appLE_chartSec (P : S.Presents s i) (T : AffOp X₀) (hT : T.unop.1 ≤ i ⁻¹ᵁ chartOpen P T) :
    i.appLE (chartOpen P T) T.unop.1 hT = chartSec P T ≫ CommRingCat.ofHom (S.p T) := by
  have hf : ⊤ ≤ (affPt s₀ T.unop) ⁻¹ᵁ T.unop.1 := (IsAffineOpen.fromSpec_preimage_self T.unop.2).ge
  have k : (affPt s₀ T.unop).appLE T.unop.1 ⊤ hf ≫ (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom = 𝟙 _ :=
    fromSpec_appLE_ΓSpecIso T.unop.2 hf
  have e1 : (⊤ : (Sp (Sec s₀ T.unop.1)).Opens) ≤ (affPt s₀ T.unop ≫ i) ⁻¹ᵁ chartOpen P T :=
    hf.trans (Scheme.Hom.preimage_mono _ hT)
  calc i.appLE (chartOpen P T) T.unop.1 hT
      = i.appLE (chartOpen P T) T.unop.1 hT ≫ ((affPt s₀ T.unop).appLE T.unop.1 ⊤ hf ≫
          (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom) := by rw [k, Category.comp_id]
    _ = (affPt s₀ T.unop ≫ i).appLE (chartOpen P T) ⊤ e1 ≫ (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom := by
        rw [← Scheme.Hom.appLE_comp_appLE (affPt s₀ T.unop) i _ _ _ hT hf]
        exact (Category.assoc _ _ _).symm
    _ = (spMap (S.p T) ≫ P.y T).appLE (chartOpen P T) ⊤ ((P.red T) ▸ e1) ≫
          (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom := by
        rw [appLE_congr (P.red T).symm _ _ e1]
    _ = (chartSec P T ≫ CommRingCat.ofHom (S.p T) : Γ(X, chartOpen P T) ⟶ Γ(X₀, T.unop.1)) := by
        rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ (preimage_chartOpen P T).ge le_top]
        refine (Category.assoc _ _ _).trans ?_
        unfold chartSec
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        congr 1
        exact specMap_appLE_top _ _

def chartInv (P : S.Presents s i) (T : AffOp X₀) : S.F.obj T →+* Γ(X, chartOpen P T) :=
  (RingEquiv.ofBijective (chartSec P T).hom (ConcreteCategory.bijective_of_isIso (chartSec P T))).symm.toRingHom

theorem chartSec_chartInv (P : S.Presents s i) (T : AffOp X₀) (b : S.F.obj T) :
    (chartSec P T).hom (chartInv P T b) = b :=
  (RingEquiv.ofBijective (chartSec P T).hom (ConcreteCategory.bijective_of_isIso (chartSec P T))).apply_symm_apply b

theorem chartInv_eq_iff (P : S.Presents s i) (T : AffOp X₀) (b : S.F.obj T) (c : Γ(X, chartOpen P T)) :
    chartInv P T b = c ↔ (chartSec P T).hom c = b := by
  constructor
  · rintro rfl; exact chartSec_chartInv P T b
  · rintro rfl
    exact (ConcreteCategory.bijective_of_isIso (chartSec P T)).1 (chartSec_chartInv P T _)

end GlobalTheory.PresCharts


open GlobalTheory.PresCharts in
theorem GlobalTheory.PresCharts.exists_charts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i), IsPullback i s₀ s (spMap π) → ∃ (V : AffOp X₀ → X.Opens) (hV : ∀ ⦃T T' : AffOp X₀⦄, (T ⟶ T') → V T' ≤ V T) (hi : ∀ T, T.unop.1 ≤ i ⁻¹ᵁ V T) (e : ∀ T, S.F.obj T →+* Γ(X, V T)), (∀ T, i ⁻¹ᵁ V T = T.unop.1) ∧ (∀ (T T' : AffOp X₀) (a : T ⟶ T') (b : S.F.obj T), e T' (mp S.F a b) = resG X (hV a) (e T b)) ∧ ∀ T b, (i.appLE (V T) T.unop.1 (hi T)).hom (e T b) = S.p T b := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S X s i P h
  have hinj := injective_of_isPullback hπ h
  refine ⟨chartOpen P, chartOpen_le P, le_preimage_chartOpen P, chartInv P,
    preimage_chartOpen_eq hI hinj P, fun T T' a b ↦ ?_, fun T b ↦ ?_⟩
  · rw [chartInv_eq_iff]
    have := congrArg (fun f ↦ f.hom (chartInv P T b)) (res_chartSec P a)
    refine this.trans ?_
    change (mp S.F a) ((chartSec P T).hom (chartInv P T b)) = _
    rw [chartSec_chartInv]
  · have := congrArg (fun f ↦ f.hom (chartInv P T b)) (appLE_chartSec P T (le_preimage_chartOpen P T))
    refine this.trans ?_
    change S.p T ((chartSec P T).hom (chartInv P T b)) = _
    rw [chartSec_chartInv]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsSquareZeroPresentedSchemeStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charts_squareZero_presented_scheme : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i), IsPullback i s₀ s (spMap π) → ∃ (V : AffOp X₀ → X.Opens) (hV : ∀ ⦃T T' : AffOp X₀⦄, (T ⟶ T') → V T' ≤ V T) (hi : ∀ T, T.unop.1 ≤ i ⁻¹ᵁ V T) (e : ∀ T, S.F.obj T →+* Γ(X, V T)), (∀ T, i ⁻¹ᵁ V T = T.unop.1) ∧ (∀ (T T' : AffOp X₀) (a : T ⟶ T') (b : S.F.obj T), e T' (mp S.F a b) = resG X (hV a) (e T b)) ∧ ∀ T b, (i.appLE (V T) T.unop.1 (hi T)).hom (e T b) = S.p T b := by
  first | exact @GlobalTheory.PresCharts.exists_charts | exact GlobalTheory.PresCharts.exists_charts | (intros; apply GlobalTheory.PresCharts.exists_charts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCosetsUnitIdelesCompletedOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCosetsUnitIdelesCompletedOrder
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem exists_finset_cover_units : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  classical
  intro E _ _ c hc
  let U : Subgroup (Af E)ˣ := (PicFin.intR E).toSubmonoid.units
  have h1 : ((hatOUnits c).subgroupOf U).FiniteIndex := PicFin.finiteIndex_units hc
  have h2 : Finite (U ⧸ (hatOUnits c).subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (U ⧸ (hatOUnits c).subgroupOf U)
  refine ⟨Finset.univ.image fun q : U ⧸ (hatOUnits c).subgroupOf U => (q.out : U).1, fun y hy => ?_⟩
  have hyU : y ∈ U := (Submonoid.mem_units_iff _ _).2
    ⟨fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hy v).le,
     fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (by rw [inv_coord, map_inv₀, hy v, inv_one])⟩
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨y, hyU⟩)), ?_⟩
  have h3 := (QuotientGroup.eq (s := (hatOUnits c).subgroupOf U)).1
    (QuotientGroup.out_eq' (QuotientGroup.mk ⟨y, hyU⟩ : U ⧸ (hatOUnits c).subgroupOf U))
  exact Subgroup.mem_subgroupOf.1 h3

end GlobalTheory.CMVal.Euler
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCosetsUnitIdelesCompletedOrderStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_cosets_unitIdeles_completedOrder : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ → ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  first | exact @GlobalTheory.CMVal.Euler.exists_finset_cover_units | exact GlobalTheory.CMVal.Euler.exists_finset_cover_units | (intros; apply GlobalTheory.CMVal.Euler.exists_finset_cover_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalVectorMemIdealCompletedLatticeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalVectorMemIdealCompletedLatticeIff
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdealCap

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem closure_eq_hat (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 E)) :
    AddSubgroup.closure {u : Fin n → GlobalTheory.AdLat.RA F E | ∃ b ∈ I, ∃ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      u = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i} =
      GlobalTheory.AdLat.hat F ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨b, hb, z, hz, rfl⟩
    rw [SetLike.mem_coe]
    induction hz using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨a, ha, b • x, Submodule.smul_mem_smul hb hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    | zero =>
      convert AddSubgroup.zero_mem _ using 1
      funext i; simp
    | add w w' _ _ h h' =>
      convert add_mem h h' using 1
      funext i; simp [mul_add]
    | neg w _ h =>
      convert neg_mem h using 1
      funext i; simp
  · unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx ⊢
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro b hb y hy
      refine AddSubgroup.subset_closure ⟨b, hb, fun i => a ⊗ₜ y i,
        AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    · intro y y' h h'
      convert add_mem h h' using 1
      funext i; simp [TensorProduct.tmul_add]

theorem span_smul_eq_top (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span E ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro x hx
  have hb1 : algebraMap (𝓞 E) E b ≠ 0 := by
    simpa using hb0
  have e : x = (algebraMap (𝓞 E) E b)⁻¹ • (b • x) := by
    rw [← algebraMap_smul E b x, smul_smul, inv_mul_cancel₀ hb1, one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.smul_mem_smul hb hx))

end General

theorem finVec_mem_closure_iff : ∀ (D : D7) (V : HSp D) (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ a : Fin V.rank → D.host.E, finVec V a ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} ↔ a ∈ I • latG V 1 := by
  intro D V I hI a
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hfg' : (I • latG V 1).FG := Submodule.FG.smul (IsNoetherian.noetherian I) hfg
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg'
    (span_smul_eq_top _ I hI hsp)).1 a
  rw [hhat, ← key, ← closure_eq_hat]
  rfl

end GlobalTheory.IdealCap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalVectorMemIdealCompletedLatticeIffStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalVector_mem_ideal_completedLattice_iff : ∀ (D : D7) (V : HSp D) (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ a : Fin V.rank → D.host.E, finVec V a ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} ↔ a ∈ I • latG V 1 := by
  first | exact @GlobalTheory.IdealCap.finVec_mem_closure_iff | exact GlobalTheory.IdealCap.finVec_mem_closure_iff | (intros; apply GlobalTheory.IdealCap.finVec_mem_closure_iff <;> assumption)
end
end

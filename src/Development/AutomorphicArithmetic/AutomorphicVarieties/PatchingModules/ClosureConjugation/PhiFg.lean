module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PhiFg
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem finite_open_homs_to_finite_group (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : TopFG G)
    (Z : Type) [Group Z] [Finite Z] : Finite {φ : G →* Z // IsOpen (φ.ker : Set G)} := by
  obtain ⟨s, hs, hgen⟩ := h
  rw [topGen_iff] at hgen
  have : Finite s := hs.to_subtype
  let f : {φ : G →* Z // IsOpen (φ.ker : Set G)} → (s → Z) := fun φ x => φ.1 x
  apply Finite.of_injective f
  intro φ ψ hφψ
  apply Subtype.ext
  have hK : IsOpen ((φ.1.ker ⊓ ψ.1.ker : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact φ.2.inter ψ.2
  have hle : φ.1.ker ⊓ ψ.1.ker ≤ MonoidHom.eqLocus φ.1 ψ.1 := by
    intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    show φ.1 g = ψ.1 g
    rw [hg.1, hg.2]
  have hopen := Subgroup.isOpen_mono hle hK
  have hcl := Subgroup.isClosed_of_isOpen _ hopen
  have hs' : Subgroup.closure (s : Set G) ≤ MonoidHom.eqLocus φ.1 ψ.1 := by
    rw [Subgroup.closure_le]
    intro x hx
    exact congrFun hφψ ⟨x, hx⟩
  have htop := Subgroup.topologicalClosure_minimal _ hs' hcl
  rw [hgen] at htop
  ext g
  exact htop (Subgroup.mem_top g)

theorem UpperTheory.V.Pa.phi_fg :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l),
      (∃ s : Finset F.Γ, (Subgroup.closure (s : Set F.Γ)).topologicalClosure = ⊤) →
        PhiCond (Γ := F.G₀) l := by
  intro l _ F hF
  obtain ⟨s, hs⟩ := hF
  have hΓ : TopFG F.Γ := ⟨(s : Set F.Γ), s.finite_toSet, (topGen_iff _).mpr hs⟩
  have hopen : IsOpen ((F.η.ker : Subgroup F.Γ) : Set F.Γ) := F.η_open
  have hG : TopFG F.G₀ := ((TopFG.subgroup_quot F.Γ hΓ).1 _ hopen)
  have : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ hopen).isCompact
  intro H hH
  have hH' : TopFG H := (TopFG.subgroup_quot F.G₀ hG).1 H hH
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact finite_open_homs_to_finite_group H hH' (Multiplicative (ZMod l))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.EpsEq
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.eps_eq :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ g : G.G₀, P.f (G.frame.eps O B g : Bˣ) = ((G0.frame.eps ℤ_[l] x.A (h.p₀ g) : x.Aˣ) : x.A) ∧ h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P g
  have hl : (l : x.K) = 0 := by
    by_contra hn
    obtain ⟨p, hp⟩ := CharP.exists x.K
    have hpp : p.Prime := CharP.char_is_prime x.K p
    have hne : p ≠ l := by rintro rfl; exact hn (CharP.cast_eq_zero _ _)
    have h6 : IsUnit ((p : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hne ?_)
      rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
      exact ((Nat.prime_dvd_prime_iff_eq Fact.out hpp).1 (by exact_mod_cast hlt)).symm
    have h8 := h6.map (algebraMap ℤ_[l] x.K)
    rw [map_intCast, Int.cast_natCast, CharP.cast_eq_zero] at h8
    exact not_isUnit_zero h8
  have hA : (l : x.A) = 0 := by rw [← map_natCast (PowerSeries.C (R := x.K)), hl, map_zero]
  have key : ∀ φ : ℤ_[l] →+* x.A, ∀ a, φ a = (a.zmodRepr : x.A) := fun φ a => by
    have h1 := PadicInt.sub_zmodRepr_mem a
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := congrArg φ hc
    rw [map_mul, map_natCast, hA, mul_zero, map_sub, map_natCast] at h2
    exact sub_eq_zero.1 h2.symm
  refine ⟨?_, Subtype.ext ?_⟩
  · have e1 := key (P.f.toRingHom.comp ((algebraMap O B).comp (algebraMap ℤ_[l] O))) (G.ε g : ℤ_[l])
    have e2 := key ((algebraMap ℤ_[l] x.A).comp (algebraMap ℤ_[l] ℤ_[l])) (G0.ε (h.p g) : ℤ_[l])
    rw [h.ε] at e2
    refine e1.trans (e2.symm.trans ?_)
    rw [← h.ε]; rfl
  · show h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
    rw [map_mul, map_mul, map_inv, h.c]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.FSurj
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.f_surj :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), Function.Surjective P.f ∧ IsLocalHom P.f.toRingHom := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P
  have hK : IsCO O x.K := by
    refine IsCO.mk ?_ ?_ ?_
    · rw [IsLocalRing.maximalIdeal_eq_bot]
      infer_instance
    · constructor
      intro a ha
      by_contra hna
      have hm : a ∈ maximalIdeal O := hna
      have hker : RingHom.ker (algebraMap O x.K) = maximalIdeal O :=
        eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ P.surj)
      have h0 : algebraMap O x.K a = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact hm
      rw [h0] at ha
      exact not_isUnit_zero ha
    · intro y
      obtain ⟨a, rfl⟩ := P.surj y
      exact ⟨a, by rw [sub_self]; exact Ideal.zero_mem _⟩
  have hA : IsCO O x.A := co_mvps O x.K Unit
  have hs : P.s ∈ maximalIdeal B := by
    rw [← res_eq_zero_iff O B, ← res_map P.f, P.f_s, res_eq_zero_iff,
      PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl
  have hsurj : Function.Surjective P.f := by
    apply co_surj O B x.A P.f
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hm := Ideal.mem_map_of_mem P.f hs
    rw [P.f_s] at hm
    exact Ideal.mem_sup_left hm
  exact ⟨hsurj, IsLocalHom.of_surjective P.f.toRingHom hsurj⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatChi
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem characteristic_polynomial_compatibility {n : ℕ} {G B A Bh F E : Type} [Group G] [CommRing B] [CommRing A] [CommRing Bh] [CommRing F]
    [Ring E] [Algebra Bh E] [Algebra Bh F] (D : GDet n B G) (f : B →+* A) (g : B →+* Bh) (a : A →+* F)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (hD : D.map f = GDet.ofRep ρ)
    (hc : ∀ b, algebraMap Bh F (g b) = a (f b)) (ι : MonoidAlgebra Bh G →ₐ[Bh] E) (DE : Det n Bh E)
    (hp : DE.pull ι = (D.map g).toDet) (r : E →ₐ[Bh] Matrix (Fin n) (Fin n) F)
    (hr : ∀ s, r (ι (MonoidAlgebra.single s 1)) = (ρ s).map a) (z : MonoidAlgebra Bh G) :
    (DE.chi (ι z)).map (algebraMap Bh F) = (r (ι z)).charpoly := by
  have hc' : (algebraMap Bh F).comp g = a.comp f := RingHom.ext hc
  rw [← (d_pull DE ι).1 z, hp, (d_toDet _ z).1, ← ((d_gmap (D.map g)).2.2.1 (algebraMap Bh F) z).1,
    (d_gmap D).2.1, hc', ← (d_gmap D).2.1, hD, (d_gmap (GDet.ofRep ρ)).2.2.2, ← (d_toDet _ _).1,
    d_toDet_ofRep.1, (d_ofRep _ _ _).1]
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | single s b =>
    have : (MonoidAlgebra.single s b : MonoidAlgebra Bh G) = b • MonoidAlgebra.single s 1 := by simp
    rw [MonoidAlgebra.mapRingHom_single]
    conv_rhs => rw [this, map_smul, map_smul, hr]
    ext i j
    simp [GDet.repAlg, Algebra.smul_def]

theorem UpperTheory.V.Pa.hat_chi :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ y, (H.DE.chi y).map (algebraMap Bh (FractionRing x.A)) = (H.r y).charpoly := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hc H y
  obtain ⟨z, rfl⟩ := H.surj y
  exact characteristic_polynomial_compatibility u.D P.f.toRingHom (algebraMap B Bh) (algebraMap x.A (FractionRing x.A)) (mat (x.ρ.comp h.p₀))
    P.maps.1 hc H.ι H.DE H.pull H.r H.r_ι z
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatRange
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem hr_span {A F : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F] {n a : ℕ}
    (t : A) (ht : t ≠ 0) (T : Set (Matrix (Fin n) (Fin n) A))
    (hT : ∀ Z ∈ Ev A A n a, ∃ s : ℕ, t ^ s • Z ∈ Submodule.span A T)
    (S : Submodule F (Matrix (Fin n) (Fin n) F)) (hS : ∀ Y ∈ T, Y.map (algebraMap A F) ∈ S) :
    Ev F F n a ≤ S := by
  have h1 : ∀ Y ∈ Submodule.span A T, Y.map (algebraMap A F) ∈ S := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem y hy => exact hS y hy
    | zero => simp
    | add y z _ _ hy hz =>
      have : (y + z).map (algebraMap A F) = y.map (algebraMap A F) + z.map (algebraMap A F) := by
        ext i j; simp
      rw [this]; exact S.add_mem hy hz
    | smul c y _ hy =>
      have : (c • y).map (algebraMap A F) = algebraMap A F c • y.map (algebraMap A F) := by
        ext i j; simp
      rw [this]; exact S.smul_mem _ hy
  intro Z hZ
  have hZ' : Z = ∑ i, ∑ j, single i j (Z i j) := matrix_eq_sum_single Z
  rw [hZ']
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
  · obtain ⟨s, hs⟩ := hT (single i j 1) (fun p q => ⟨fun _ => trivial, fun e' => by
      rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact e' e⟩)
    have h2 := S.smul_mem (Z i j * (algebraMap A F (t ^ s))⁻¹) (h1 _ hs)
    have hne : algebraMap A F (t ^ s) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A F)]
      exact pow_ne_zero _ ht
    convert h2 using 1
    ext p q
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    · simp
  · have : Z i j = 0 := (hZ i j).2 e
    simp [this]

theorem UpperTheory.V.Pa.hat_range :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], Function.Surjective (algebraMap Bh (FractionRing x.A)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ Z, Z ∈ Ev (FractionRing x.A) (FractionRing x.A) n x.a ↔ ∃ y, H.r y = Z := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hs H Z
  have hsm : ∀ (b : Bh) (Y : Matrix (Fin n) (Fin n) (FractionRing x.A)),
      b • Y = algebraMap Bh (FractionRing x.A) b • Y := by
    intro b Y
    ext i j
    simp [Algebra.smul_def]
  constructor
  · let S : Submodule (FractionRing x.A) (Matrix (Fin n) (Fin n) (FractionRing x.A)) :=
      { carrier := {Z | ∃ y, H.r y = Z}
        add_mem' := by
          rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
          exact ⟨y + z, map_add _ _ _⟩
        zero_mem' := ⟨0, map_zero _⟩
        smul_mem' := by
          rintro c _ ⟨y, rfl⟩
          obtain ⟨b, rfl⟩ := hs c
          exact ⟨b • y, by rw [map_smul, hsm]⟩ }
    intro hZ
    refine hr_span (A := x.A) x.t PowerSeries.X_ne_zero _ x.span S ?_ hZ
    rintro _ ⟨g, -, rfl⟩
    obtain ⟨g', hg'⟩ := h.surj g.1
    have hm : g' ∈ G.η.ker := by
      have h1 := h.η g'
      rw [hg'] at h1
      rw [MonoidHom.mem_ker, ← h1]
      exact g.2
    have : h.p₀ ⟨g', hm⟩ = g := Subtype.ext hg'
    exact ⟨_, by rw [← this]; exact H.r_ι ⟨g', hm⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := H.surj y
    induction z using MonoidAlgebra.induction_on with
    | of g =>
      have := H.r_ι g
      rw [MonoidAlgebra.of_apply, this]
      intro i j
      refine ⟨fun _ => trivial, fun e => ?_⟩
      have h0 : mat x.ρ (h.p₀ g) i j = 0 := (x.blk (h.p₀ g) i j).2 e
      rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]
    | add f g hf hg =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ hf hg
    | smul b f hf =>
      rw [map_smul, map_smul, hsm]
      exact Submodule.smul_mem _ _ hf
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrI
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsOneBlock
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.units_one_block :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p : ι), (∀ i, o i = p) → ∃ φ : E ≃ₐ[B] Matrix ι ι B, (∀ y i j, φ y i j = T.tr (U.x i * y * T.st (U.x j))) ∧ (∀ y, φ (T.st y) = (φ y)ᵀ) ∧ ∀ y, (φ y).trace = T.tr y := by
  intro B E _ _ _ T ι _ _ o U p ho
  obtain ⟨hA, hB, -, hD, hE, hF, -⟩ := units_basic T o U
  have hidem : U.ep p * U.ep p = U.ep p := (U.coi.idem p).eq
  have hte : T.tr (U.ep p) = 1 := U.tr_ep p
  have hxs : ∀ i j, U.x i * T.st (U.x j) = if i = j then U.ep p else 0 := by
    intro i j
    split_ifs with h
    · subst h
      rw [U.x_st, ho]
    · exact hA i j h
  have hex : ∀ j, U.ep p * U.x j = U.x j := by
    intro j
    have h := U.x_mem j
    rw [ho] at h
    calc U.ep p * U.x j = U.ep p * (U.ep p * U.x j * U.ep j) := by rw [h]
      _ = U.ep p * U.ep p * U.x j * U.ep j := by simp only [mul_assoc]
      _ = U.x j := by rw [hidem, h]
  have hE' : ∀ i j y, U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep p := by
    intro i j y
    have h := hE i j y (by rw [ho i, ho j])
    rwa [ho i] at h
  have hpair : ∀ a b : E, a = T.tr a • U.ep p → b = T.tr b • U.ep p → T.tr (a * b) = T.tr a * T.tr b := by
    intro a b ha hb
    calc T.tr (a * b) = T.tr ((T.tr a • U.ep p) * (T.tr b • U.ep p)) := by rw [← ha, ← hb]
      _ = T.tr a * T.tr b := by rw [smul_mul_smul_comm, hidem, map_smul, hte, smul_eq_mul, mul_one]
  let f : E → Matrix ι ι B := fun y => Matrix.of fun i j => T.tr (U.x i * y * T.st (U.x j))
  let g : Matrix ι ι B → E := fun M => ∑ i, ∑ j, M i j • (T.st (U.x i) * U.x j)
  have hfmul : ∀ y z, f (y * z) = f y * f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.mul_apply]
    calc T.tr (U.x i * (y * z) * T.st (U.x j))
        = T.tr (U.x i * y * (∑ k, T.st (U.x k) * U.x k) * z * T.st (U.x j)) := by
          rw [hB, mul_one, mul_assoc (U.x i) y z]
      _ = ∑ k, T.tr ((U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j))) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Finset.mul_sum, Finset.sum_mul, map_sum, mul_assoc]
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact hpair _ _ (hE' i k y) (hE' k j z)
  have hfadd : ∀ y z, f (y + z) = f y + f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add (f := _)]
  have hfsmul : ∀ (r : B) y, f (r • y) = r • f y := by
    intro r y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]
  have hf1 : f 1 = 1 := by
    ext i j
    simp only [f, Matrix.of_apply, mul_one, hxs, Matrix.one_apply]
    split_ifs <;> simp [hte]
  have hgf : ∀ y, g (f y) = y := by
    intro y
    simp only [g, f, Matrix.of_apply]
    conv_rhs => rw [hF y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := hE' i j y
    set c := T.tr (U.x i * y * T.st (U.x j)) with hc
    rw [h, mul_smul_comm, smul_mul_assoc, mul_assoc, hex]
  have hfg : ∀ M, f (g M) = M := by
    intro M
    ext i j
    have hq : ∀ k l, U.x i * (T.st (U.x k) * U.x l) * T.st (U.x j) = (U.x i * T.st (U.x k)) * (U.x l * T.st (U.x j)) := by
      intro k l
      simp only [mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, g, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc, map_smul, hq, hxs]
    simp [ite_mul, mul_ite, hidem, hte, apply_ite]
  have hfst : ∀ y, f (T.st y) = (f y)ᵀ := by
    intro y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.transpose_apply]
    rw [← T.tr_st (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]
  have hftr : ∀ y, (f y).trace = T.tr y := by
    intro y
    simp only [Matrix.trace, Matrix.diag, f, Matrix.of_apply]
    exact (hD y).symm
  have hcomm : ∀ r : B, f (algebraMap B E r) = algebraMap B (Matrix ι ι B) r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hfsmul, hf1]
  let φ : E ≃ₐ[B] Matrix ι ι B := { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg, map_mul' := hfmul, map_add' := hfadd, commutes' := hcomm }
  exact ⟨φ, fun y i j => rfl, hfst, hftr⟩
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gr_I :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F) (U : T.Units (Fin n) (oB n n)), 1 ≤ n → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (oB n n i) i 1) → Nonempty (GrAlg T n n r U.ep) := by
  intro B E F _ _ _ _ _ _ n T r U hn hr hx
  have ho : ∀ i : Fin n, oB n n i = ⟨0, by omega⟩ := fun i => Fin.ext (by simp [oB, i.isLt])
  obtain ⟨φ, hφ, hst, -⟩ := units_one_block T (oB n n) U ⟨0, by omega⟩ ho
  have hU := units_basic T (oB n n) U
  have hxe : ∀ i' i : Fin n, U.x i' * U.ep i = if i' = i then U.x i' else 0 := by
    intro i' i
    conv_lhs => rw [← U.x_mem i']
    split_ifs with h
    · subst h
      rw [mul_assoc, (U.coi.idem i').eq, U.x_mem]
    · rw [mul_assoc, U.coi.ortho h, mul_zero]
  have hone : (1 : Submodule B B) = ⊤ :=
    eq_top_iff.2 fun x _ => Submodule.mem_one.2 ⟨x, rfl⟩
  refine ⟨@GrAlg.mk B E F _ _ _ _ _ _ T n n r U.ep B _ _ inferInstance (fun a b h => h) ⊥
    ?_ ?_ (fun _ => rfl) φ.toAlgHom φ.injective ?_ hst ?_ ?_⟩
  · rw [hone]
    exact isCompl_top_bot
  · intro y hy z hz
    rw [Submodule.mem_bot] at hy
    subst hy
    exact ⟨0, zero_mem _, by simp⟩
  · intro Y
    constructor
    · intro _
      intro i j
      refine ⟨fun _ => by rw [hone]; trivial, fun h => absurd ⟨fun _ => j.isLt, fun _ => i.isLt⟩ h⟩
    · intro _
      exact φ.surjective Y
  · intro i
    show φ (U.ep i) = _
    ext i' j'
    rw [hφ, hxe]
    split_ifs with h1
    · subst h1
      by_cases h2 : i' = j'
      · subst h2
        rw [U.x_st, U.tr_ep]
        simp [Matrix.single_apply]
      · rw [hU.1 i' j' h2, map_zero]
        simp [Matrix.single_apply, h2, Ne.symm h2]
    · simp [Matrix.single_apply, Ne.symm h1]
  · intro y i j b h
    rw [Submodule.mem_bot, sub_eq_zero] at h
    change φ y i j = b at h
    rw [← h, hφ]
    have he0 : r (U.ep ⟨0, by omega⟩) = single ⟨0, by omega⟩ ⟨0, by omega⟩ 1 := by
      have h0 := U.x_base ⟨0, by omega⟩
      rw [ho] at h0
      rw [← h0, hx, ho]
    have hk := hU.2.2.2.2.1 i j y (by rw [ho, ho])
    have hr2 := congrArg (fun M => M ⟨0, by omega⟩ ⟨0, by omega⟩) (congrArg r hk)
    simp only [map_mul, map_smul, hr, hx, ho, he0] at hr2
    simp [Matrix.mul_apply, Matrix.single_apply, Algebra.smul_def] at hr2
    rw [hr2]
end

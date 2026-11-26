module

public import Formalism.LocalToGlobal.Columns.TiedVal
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.TiedValRat
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct Pointwise

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

end GSD.Ev

section Pol

variable {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}

theorem smul_mem_RatSpanG (lam : ι → DomWeight n) (r : K) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : s r • p ∈ RatSpanG s lam := by
  unfold RatSpanG at hp ⊢
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r', f, hf, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨r * r', f, hf, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem RatSpanG_shW (lam : ι → DomWeight n) (c : ι → ℤ) :
    RatSpanG s (fun τ => shW (lam τ) (c τ)) = RatSpanG s lam := by
  unfold RatSpanG
  simp only [delSq_shW]

theorem exists_VV_of_mem_RatSpanG (lam : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : ∃ F ∈ VV K lam, MvPolynomial.map s F = p := by
  unfold RatSpanG at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hf, rfl⟩ := hx
    refine ⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (MvPolynomial.map (Int.castRingHom K) (f τ)), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩)
      exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (natW_anti (lam τ)) (map_mem_weyl le_rfl _ _ (hf τ))
    · rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_ten]
      congr 2
      funext τ
      rw [MvPolynomial.map_map]
      have e : s.comp (Int.castRingHom K) = Int.castRingHom ℂ := RingHom.ext_int _ _
      rw [e]
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨F', hF', rfl⟩ := hy
    exact ⟨F + F', Submodule.add_mem _ hF hF', map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact ⟨-F, Submodule.neg_mem _ hF, map_neg _ _⟩

variable [CharZero K]

theorem map_mem_RatSpanG (lam : ι → DomWeight n) {F : MvPolynomial (ι × Fin n × Fin n) K} (hF : F ∈ VV K lam) :
    MvPolynomial.map s F ∈ RatSpanG s lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    let T : ι → Set (MvPolynomial (ι × Fin n × Fin n) K) := fun τ =>
      Set.range fun w : List (Fin n × Fin n × ℕ) =>
        Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW))
    have h1 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ) ∈ Submodule.span K (T τ) := by
      intro τ
      have h0 : f τ ∈ delSq K n (lam τ) := by rw [← nablaSq_eq_delSq]; exact hf τ
      have h := Submodule.mem_map_of_mem (f := (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ).toLinearMap) h0
      unfold delSq Formalism.GradedWeylDivisibility.weyl at h
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    have h2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ∈ Submodule.span K (∏ τ, T τ) := by
      rw [← Submodule.prod_span]
      exact prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
    have key : ∀ y ∈ Submodule.span K (∏ τ, T τ), MvPolynomial.map s y ∈ RatSpanG s lam := by
     intro y hy
     induction hy using Submodule.span_induction with
     | mem y hy =>
      rw [Set.mem_finsetProd] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
          Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) = g τ :=
        fun τ => hg (Finset.mem_univ τ)
      choose w hw using hg'
      refine AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
        fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩
      rw [map_one, one_smul]
      have e : (∏ τ, g τ) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K (w τ) (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) :=
        Finset.prod_congr rfl fun τ _ => (hw τ).symm
      rw [e, map_ten]
      congr 1
      funext τ
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
        Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
     | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
     | add y z _ _ hy hz => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hy hz
     | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
      exact smul_mem_RatSpanG s lam c hy
    exact key _ h2
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact smul_mem_RatSpanG s lam c hx

theorem mem_RatSpanG_iff (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    p ∈ RatSpanG s lam ↔ ∃ F ∈ VV K lam, MvPolynomial.map s F = p :=
  ⟨exists_VV_of_mem_RatSpanG s lam, by rintro ⟨F, hF, rfl⟩; exact map_mem_RatSpanG s lam hF⟩

end Pol

section Round

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

end Round

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) (i : ℕ)


end Gen

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.LocalLevelIsKOneEverywhere
section -- merged from Formalism.LocalToGlobal.Columns.ExistsPlaceOverFirstPrime
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Repack0

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {sp : Spaces R F E} {gp : Fin 2 → ℕ} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
  {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {bad : Set (HeightOneSpectrum (𝓞 F))}

def LevPack.toCol (P : LevPack sp.cm R.k sp.gram0 gp A.T R.f bad (C.stab 0) fun c => sp.crdLat0 (clsLat 0 c))
    (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (spl_sig : ∀ i v h x, spl i v h (sigR sp.cm.sig (v.adicCompletion F) x) = swapR _ (spl i v h x))
    (hiw : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
      ∀ x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), x ∈ P.lev.Uloc v ↔
        (1 : GL (Fin R.k) (v.adicCompletion F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU F R.k v)
    (w1 : HeightOneSpectrum (𝓞 F)) (reflection_mem_Glev_castSucc : (gp 0 : 𝓞 F) ∈ w1.asIdeal) :
    ColLevel R F E sp gp C A clsLat where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := P.lev.Lb_int
  Lb_dual := P.lev.Lb_dual
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_le := P.lev.Uloc_le
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  splitG := spl
  splitG_sig := spl_sig
  frG := fun _ _ _ => 1
  Uloc_g := hiw
  fM := P.lev.fM
  fT := P.lev.fT
  fT_ne := P.lev.fT_ne
  fT_T := P.lev.fT_T
  fM_card := P.lev.fM_card
  fT_L := P.lev.fT_L
  UlocAlt := P.lev.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq
  U_compact := P.lev.U_compact
  U_open := P.lev.U_open
  w1 := w1
  reflection_mem_Glev_castSucc := reflection_mem_Glev_castSucc
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := P.cls.stabI_range
  stabI_lat := P.cls.stabI_lat

end Repack0

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
      X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F)

def IwLoc : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
    ∀ x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (v.adicCompletion X.F), x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
      (1 : GL (Fin n) (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F n v

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))

theorem levPack_iw (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (hI : IwLoc hc u Λ spl) (H : HCrd Pr n fun c => (s c).1.L) :
    ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
      ∀ x ∈ UPts hc.sig H.J (v.adicCompletion X.F), x ∈ (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Uloc v ↔
        (1 : GL (Fin H.n') (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F H.n' v := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact hI

def th_resMap (P : Pl X.E) : 𝓞 X.F ⧸ (underPl X.F P).asIdeal →+* 𝓞 X.E ⧸ P.asIdeal :=
  Ideal.quotientMap P.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E)) (le_of_eq rfl)

include hPr in
theorem th_resMap_bij (P : {P // P ∈ Pr.vT u}) : Function.Bijective (th_resMap (X := X) P.1) := by
  constructor
  · exact Ideal.quotientMap_injective' (le_of_eq rfl)
  · intro b
    haveI : Fact (Pr.T u).Prime := ⟨hPr.T_prime u⟩
    haveI : Nontrivial (𝓞 X.E ⧸ P.1.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.1.isPrime.ne_top
    have hcard : Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := by
      rw [← Ideal.absNorm_eq_natCard]
      exact hPr.vT_norm u P.1 P.2
    obtain ⟨k, hk⟩ := mem_zmultiples_of_prime_card hcard (g := (1 : 𝓞 X.E ⧸ P.1.asIdeal)) (g' := b) one_ne_zero
    refine ⟨(k : 𝓞 X.F ⧸ (underPl X.F P.1).asIdeal), ?_⟩
    rw [map_intCast, ← hk]
    simp

def tieFv (P : {P // P ∈ Pr.vT u}) : (𝓞 X.E ⧸ P.1.asIdeal) ≃+* (𝓞 X.F ⧸ (tieEV hc hX hPr u P).1.asIdeal) :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm

theorem tieFv_mk (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    tieFv hc hX hPr u P (Ideal.Quotient.mk P.1.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E) x)) = Ideal.Quotient.mk _ x :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm_apply_apply (Ideal.Quotient.mk _ x)


include hX hPr in
theorem exists_place_over_first_prime : ∃ v : HeightOneSpectrum (𝓞 X.F), (Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal := by
  have hcard : 0 < (Pr.vG 0).card := by rw [hPr.vG_card 0]; exact hX.f_pos
  obtain ⟨P, hP⟩ := Finset.card_pos.1 hcard
  refine ⟨underPl X.F P, ?_⟩
  show (Pr.g 0 : 𝓞 X.F) ∈ P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast, ← hPr.piG_norm 0]
  exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs hP)

end Gen

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

theorem th_gram_eq (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) : (d.sp.X i).gram = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X i).hT ((d.sp.X i).frame x) ((d.sp.X i).frame y) = _
  rw [hS.X_on i hi, Matrix.one_apply]

theorem th_gram0_eq (hS : SpStd d.toColBase) : d.sp.gram0 = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X 0).hT ((d.sp.X 0).frame _) ((d.sp.X 0).frame _) = _
  rw [hS.X_on 0 (Nat.zero_le _), Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem th_crdLat_eq (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    Formalism.L2.Herm.crdLat (d.sp.X i) (d.clsLat u i c) = Formalism.L2.Forms.reL (d.sp.X_rank i hi).symm (d.repr u i c).1.L := by
  unfold Formalism.L2.Herm.crdLat ColDat.clsLat Formalism.L2.Forms.reL
  rw [dite_eq_left hi, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show (d.sp.X i).frame.equivFun ((d.crd i hi).symm x) j = _
  unfold ColDat.crd
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem th_crdLat0_eq (u : d.what₂.Word) (c : StCl (Pr := d.Pr) d.W d.lev u 0) :
    d.sp.crdLat0 (d.clsLat u 0 c) = Formalism.L2.Forms.reL (Formalism.L2.Forms.rank_eq_first_level d.R).symm (d.repr u 0 c).1.L := by
  unfold Spaces.crdLat0 ColDat.clsLat Formalism.L2.Forms.reL
  rw [dite_eq_left (Nat.zero_le _), ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show d.sp.crd0 ((d.crd 0 (Nat.zero_le _)).symm x) j = _
  unfold ColDat.crd Spaces.crd0
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

def hCrd (hS : SpStd d.toColBase) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    HCrd d.Pr (d.R.N i) fun c : StCl (Pr := d.Pr) d.W d.lev u i => (d.repr u i c).1.L where
  n' := (d.sp.X i).rank
  hn := d.sp.X_rank i hi
  J := (d.sp.X i).gram
  hJ := th_gram_eq hS i hi
  f := d.R.f
  hf := d.f_eq.symm
  bad := plUnder d.X.F d.Pr.vGs
  hbad := rfl
  lat := fun c => Formalism.L2.Herm.crdLat (d.sp.X i) (d.clsLat u i c)
  hlat := fun c => th_crdLat_eq u i hi c

def hCrd0 (hS : SpStd d.toColBase) (u : d.what₂.Word) :
    HCrd d.Pr (d.R.N 0) fun c : StCl (Pr := d.Pr) d.W d.lev u 0 => (d.repr u 0 c).1.L where
  n' := d.R.k
  hn := Formalism.L2.Forms.rank_eq_first_level d.R
  J := d.sp.gram0
  hJ := th_gram0_eq hS
  f := d.R.f
  hf := d.f_eq.symm
  bad := plUnder d.X.F d.Pr.vGs
  hbad := rfl
  lat := fun c => d.sp.crdLat0 (d.clsLat u 0 c)
  hlat := fun c => th_crdLat0_eq u c

def LocalLevelIsKOneEverywhere (d : ColDat) : Prop := ∀ (u : d.what₂.Word) (i : ℕ), LocalLevelIsKOneAtT d.sp.cm u (d.lev i)

def IwAll (d : ColDat) (S : GSplit (Pr := d.Pr) d.sp.cm) : Prop := ∀ u : d.what₂.Word, IwLoc d.sp.cm u (d.lev 0) S.sp

def hermPack (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :=
  levPack d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hi)

def hermPack0 (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (u : d.what₂.Word) :=
  levPack d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u)

def hermLev0 (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)
    (u : d.what₂.Word) :
    ColLevel d.R d.host.F d.host.E d.sp d.host.g (d.chain a u) (d.atT a u) (fun i c => d.clsLat u i c) :=
  LevPack.toCol (sp := d.sp) (C := d.chain a u) (A := d.atT a u) (clsLat := fun i c => d.clsLat u i c)
    (hermPack0 hS hP hK u) S.sp S.sp_sig
    (levPack_iw d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) S.sp _ _ _ _ _ (hI u) (hCrd0 hS u))
    (exists_place_over_first_prime d.hX d.hPr).choose (exists_place_over_first_prime d.hX d.hPr).choose_spec

def hermCols (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S) :
    CH.HermCols (d.colRec a) where
  lev0 := fun u => hermLev0 a hS hP hK S hI u
  lev := fun u i _ hm => LevPack.toStep (S := d.sp.X i) (lat := d.clsLat u i) (hermPack hS hP hK u i hm)
  cls := fun u i _ hm => LevPack.toCls (S := d.sp.X i) (lat := d.clsLat u i) (hermPack hS hP hK u i hm)
  vT := fun u => tieEV d.sp.cm d.hX d.hPr u
  Fv := fun u v => tieFv d.sp.cm d.hX d.hPr u v

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.InvariantSubspaceNonzeroXOfRegular
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Idem

variable {K : Type} [Field K] {A : Type} [Group A] {M : Type} [Group M] [Fintype M]


end Idem

section Gen

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) {A : Type} [Group A] [Fintype A]
  (ι : A →* GLG (E := X.E) (n := n) (SG := SG)) (hι : ∀ a w, (Λ w).NormBy (ι a w))
  {M : Type} [Group M] [Fintype M] (j : M →* A) (ε : M →* X.Kˣ)

end Gen

section StabComb

variable (κ : Type) [CommRing κ] {n : ℕ}

variable {κ}

end StabComb

section Stab

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Stab

section StabPt

variable {X : Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))}


end StabPt

section Scal

variable {E : Type} [Field E] [NumberField E]



end Scal

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)



end Rows

section ScalAct

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end ScalAct

section RhoScal

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem tensorWeights_scalar_action (lam : ι → DomWeight n) (t : ι → Kˣ) :
    Formalism.L2.DIV.rhoK lam (fun τ => (brpSc K (t τ) : GL (Fin n) K)) =
      (∏ τ, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
  classical
  have key : ∀ S : Finset ι, Formalism.L2.DIV.rhoK lam (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
      (∏ τ ∈ S, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
    intro S
    refine Finset.induction_on S ?_ (fun a S ha ih => ?_)
    · have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then (brpSc K (t τ) : GL (Fin n) K) else 1) = 1 := by
        funext τ
        simp
      rw [h0, map_one, Finset.prod_empty, one_smul]
    · have h0 : (fun τ => if τ ∈ insert a S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
          Pi.mulSingle a (brpSc K (t a) : GL (Fin n) K) * (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · have h1 : τ ∈ insert a S ↔ τ ∈ S := by simp [hτ]
          simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hτ, one_mul]
          by_cases h2 : τ ∈ S
          · rw [if_pos (h1.mpr h2), if_pos h2]
          · rw [if_neg (fun h => h2 (h1.mp h)), if_neg h2]
      rw [h0, map_mul, ih, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoK_single_scalar, Finset.prod_insert ha, smul_mul_smul, one_mul]
      rfl
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

end RhoScal

section RhoScal2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} [NeZero n]


end RhoScal2

section RowsScal

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)



end RowsScal

section LamKEv

end LamKEv

section RowsMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)




end RowsMain

section RowsMainV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)




end RowsMainV

section Card

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Card

section RowsCard

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end RowsCard

section NotFaithful

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)



end NotFaithful

end Formalism.L2.Col
end
end

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdVan2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.SelfDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.ModelSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.PairDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.HidaX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapOfRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.LocalOfFinite
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem local_of_finite {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] (f : R →+* S) : IsLocalHom f := by
  classical
  constructor
  intro a ha
  by_contra hna
  have hm : a ∈ maximalIdeal R := hna
  let g : R →+* ResidueField S := (residue S).comp f
  have hker : RingHom.ker g = maximalIdeal R := by
    haveI : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
    haveI : Finite (R ⧸ RingHom.ker g) := Finite.of_injective _ (RingHom.kerLift_injective g)
    have hmax : (RingHom.ker g).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
    exact IsLocalRing.eq_maximalIdeal hmax
  have hg : g a = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact hm
  have hfa : f a ∈ maximalIdeal S := by
    simpa [g, residue_eq_zero_iff] using hg
  exact hfa ha

theorem UpperTheory.V.Th.Nm.redOf :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c c' : Coef l) (h : c.O ≤ c'.O) (r : Resid F c.O n) (r' : Resid F c'.O n) (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (p : Pair r R) (x : R →ₐ[c.O] Qbar l) (ρ₀ : F.G₀ →* GL (Fin n) c'.O) (ψ₀ : ∀ v, Fin n → F.Gv v →* c'.Oˣ), RPush h r r' → (∀ b, x b ∈ c'.O) → p.D.map (x : R →+* Qbar l) = GDet.ofRep (mat (pushRep (algebraMap c'.O (Qbar l)) ρ₀)) → (∀ v i, pushCh (algebraMap c'.O (Qbar l)) (ψ₀ v i) = pushCh (x : R →+* Qbar l) (p.ψ v i)) → (GDet.ofRep (mat ρ₀)).map (res c'.O c'.O : c'.O →+* ResidueField c'.O) = r'.Dbar ∧ ∀ v i, r'.IsPsi v i (ψ₀ v i) := by
  intro l _ n F c c' h r r' R _ _ _ p x ρ₀ ψ₀ hpush hx hD hψ
  haveI : Module.Finite ℤ_[l] c'.O := c'.fin
  haveI : Finite (ResidueField c'.O) := (abelian₂.dvr_finite l c'.O).2.1
  obtain ⟨f, hf, hchi, hpsi, hth⟩ := hpush
  let ι : c'.O →+* Qbar l := algebraMap c'.O (Qbar l)
  have hι : Function.Injective ι := Subtype.val_injective
  let y : R →+* c'.O := (x : R →+* Qbar l).codRestrict c'.O hx
  have hy : ι.comp y = (x : R →+* Qbar l) := by
    ext z
    rfl
  haveI : IsLocalHom y := local_of_finite y
  have hyalg : ∀ a : c.O, y (algebraMap c.O R a) = inc h a := by
    intro a
    apply hι
    show x (algebraMap c.O R a) = ι (inc h a)
    rw [x.commutes]
    rfl
  have hym : ∀ z ∈ maximalIdeal R, y z ∈ maximalIdeal c'.O := by
    intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hz ((isUnit_map_iff y _).1 hu)
  have hres : ∀ z, residue c'.O (y z) = f (res c.O R z) := by
    intro z
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := c.O) z
    have hz : z = algebraMap c.O R a + (z - algebraMap c.O R a) := by ring
    have hm0 : res c.O R (z - algebraMap c.O R a) = 0 := by
      simp [UpperTheory.V.Alg.res, (IsLocalRing.residue_eq_zero_iff _).2 ha]
    have hm1 : residue c'.O (y (z - algebraMap c.O R a)) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 (hym _ ha)
    rw [hz, map_add (f := _), map_add (f := _), map_add (f := _), hm1, hm0, hyalg, AlgHom.commutes, ← hf]
    simp [ResidueField.algebraMap_eq]
  have hresid : ∀ w : c'.O, res c'.O c'.O w = residue c'.O w := by
    intro w
    have := (res c'.O c'.O).commutes w
    simpa [ResidueField.algebraMap_eq] using this
  have hresring : (res c'.O c'.O : c'.O →+* ResidueField c'.O) = residue c'.O := by
    ext w
    exact hresid w
  have hmapeq : (GDet.ofRep (mat ρ₀)).map ι = (p.D.map y).map ι := by
    rw [(CA.d_gmap (p.D)).2.1 y ι, hy, hD, (CA.d_gmap (GDet.ofRep (mat ρ₀))).2.2.2 ι (mat ρ₀)]
    congr 1
  have hρ : GDet.ofRep (mat ρ₀) = p.D.map y := by
    apply CA.d_gext
    intro g i _ _
    apply hι
    have e1 := ((CA.d_gmap (GDet.ofRep (mat ρ₀))).2.2.1 ι (MonoidAlgebra.single g 1)).2 i
    have e2 := ((CA.d_gmap (p.D.map y)).2.2.1 ι (MonoidAlgebra.single g 1)).2 i
    rw [← e1, ← e2, hmapeq]
  have hψy : ∀ v i g, ((ψ₀ v i g : c'.Oˣ) : c'.O) = y (p.ψ v i g : R) := by
    intro v i g
    apply hι
    have := congrArg (fun φ : F.Gv v →* (Qbar l)ˣ => ((φ g : (Qbar l)ˣ) : Qbar l)) (hψ v i)
    exact this
  refine ⟨?_, ?_⟩
  · rw [hρ, (CA.d_gmap p.D).2.1, hresring]
    have hcomp : (residue c'.O).comp y = f.comp (res c.O R : R →+* ResidueField c.O) := by
      ext z
      exact hres z
    rw [hcomp, ← (CA.d_gmap p.D).2.1, p.red]
    show (GDet.ofRep (diagRep r.chib)).map f = GDet.ofRep (diagRep r'.chib)
    rw [(CA.d_gmap (GDet.ofRep (diagRep r.chib))).2.2.2 f (diagRep r.chib)]
    congr 1
    ext g i j
    simp only [MonoidHom.coe_comp, Function.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk,
      RingHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, hchi]
    split_ifs with hij <;> simp [hij, Matrix.diagonal_apply]
  · intro v i
    refine ⟨?_, ?_, ?_⟩
    · intro N
      have hle : maximalIdeal R ^ N ≤ (maximalIdeal c'.O ^ N).comap y := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hym) N
      have hc := (p.psi v i).cont N
      have : (fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((ψ₀ v i g : c'.Oˣ) : c'.O)) =
          (Ideal.quotientMap (maximalIdeal c'.O ^ N) y hle) ∘
            (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) ((p.ψ v i g : Rˣ) : R)) := by
        funext g
        simp [hψy, Ideal.quotientMap_mk]
      rw [this]
      exact hc.comp _
    · intro g
      rw [hresid, hψy, hres, (p.psi v i).red, hpsi]
      rfl
    · intro g
      rw [hψy, (p.psi v i).mu, hyalg, hth]
      rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.ConjAll
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Nm.conjAll :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P Q P' : GL (Fin n) (Qbar l)), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q → (Continuous ρ → Continuous (cj Q ρ)) ∧ (Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → Submodule.span (Qbar l) (Set.range (mat (cj Q ρ))) = ⊤) ∧ (F.IsForm c.O n ρ P → F.IsForm c.O n (cj Q ρ) P') ∧ GDet.ofRep (mat (cj Q ρ)) = GDet.ofRep (mat ρ) ∧ (∀ g, (mat (cj Q ρ) g).charpoly = (mat ρ g).charpoly) ∧ (∀ S, DetQ F c.O ρ P S → DetQ F c.O (cj Q ρ) P' S) ∧ ∀ I ψ z, IsOrdCoc F ρ P I ψ z → IsOrdCoc F (cj Q ρ) P' I ψ fun g => ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * z g * Q := by
  intro l _ n F c ρ P Q P' hP
  have hm : ∀ g, mat (cj Q ρ) g = ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * mat ρ g * Q := by
    intro g
    change ((cj Q ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = _
    rw [cj_apply, Units.val_mul, Units.val_mul]; rfl
  have hch : ∀ g, (mat (cj Q ρ) g).charpoly = (mat ρ g).charpoly := by
    intro g
    have := Matrix.charpoly_units_conj Q⁻¹ (mat ρ g)
    rw [hm, ← this, ← Matrix.coe_units_inv, inv_inv]
  have hinv : ∀ w : GL (Fin n) (Qbar l), (((Q⁻¹ * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * Q := by
    intro w; rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  have hmul : ∀ w : GL (Fin n) (Qbar l), ((Q⁻¹ * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * w := fun w => Units.val_mul _ _
  have hD : GDet.ofRep (mat (cj Q ρ)) = GDet.ofRep (mat ρ) :=
    (UpperTheory.V.AlgebraTools.Det.repApi (mat ρ)).2.2.2.2.2.2.2 _ Q fun g => by
      rw [hm, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have h1 : (Q : Matrix (Fin n) (Fin n) (Qbar l)) * ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.mul_inv Q
  have h2 : ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * (Q : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.inv_mul Q
  generalize hqi : ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = qi at *
  generalize hq : (Q : Matrix (Fin n) (Fin n) (Qbar l)) = q at *
  have a1 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), q * (qi * X) = X := fun X => by rw [← mul_assoc, h1, one_mul]
  have a2 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), qi * (q * X) = X := fun X => by rw [← mul_assoc, h2, one_mul]
  have t1 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), qiᵀ * (qᵀ * X) = X := fun X => by
    rw [← mul_assoc, ← transpose_mul, h1, transpose_one, one_mul]
  refine ⟨fun h => ?_, fun h => ?_, fun h g => ?_, hD, hch, fun S h z hz hc hp ht => ?_, fun I ψ z h => ?_⟩
  · have : (cj Q ρ : F.G₀ → _) = fun g => Q⁻¹ * ρ g * Q := funext (cj_apply Q ρ)
    rw [this]
    exact (continuous_const.mul h).mul continuous_const
  · have key : ∀ Z ∈ Submodule.span (Qbar l) (Set.range (mat ρ)),
        qi * Z * q ∈ Submodule.span (Qbar l) (Set.range (mat (cj Q ρ))) := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact Submodule.subset_span ⟨g, hm g⟩
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
      | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    refine eq_top_iff.2 fun Z _ => ?_
    have := key (q * Z * qi) (h ▸ Submodule.mem_top)
    simpa only [mul_assoc, a2, h2, mul_one] using this
  · have := congrArg (fun X => qᵀ * X * q) (h g)
    simp only [mul_smul_comm, smul_mul_assoc] at this
    rw [hm, hm, hP, ← this]
    simp only [transpose_mul, mul_assoc, a1, t1]
  · obtain ⟨Y, hY⟩ := h (fun g => q * z g * qi) ((continuous_const.mul hz).mul continuous_const)
      (fun g g' => by
        simp only [hc g g', hm, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, a1, h1, mul_one])
      (fun g => by
        have := congrArg (fun X => qiᵀ * X * qi) (hp g)
        simpa only [hP, transpose_mul, mul_assoc, t1, h1, mul_one] using this)
      (fun σ hσ k => by
        have := ht σ hσ k
        rw [← map_pow, hm, map_pow, ← mul_assoc, trace_mul_comm] at this
        simpa only [mul_assoc] using this)
    refine ⟨qi * Y * q, fun g => ?_⟩
    have := congrArg (fun X => qi * X * q) (hY g)
    simpa only [hm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, a1, a2, h2, mul_one] using this
  · refine ⟨(continuous_const.mul h.cont).mul continuous_const, fun g g' => ?_, fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
    · simp only [h.coc g g', hm, mul_add, add_mul, mul_assoc, a1]
    · have := congrArg (fun X => qᵀ * X * q) (h.pol g)
      simpa only [hP, transpose_mul, mul_assoc, t1, a1, mul_neg, neg_mul] using this
    · simp [h.ine u g hg]
    · obtain ⟨w, Y, hw⟩ := h.ord v
      refine ⟨Q⁻¹ * w, qi * Y * q, fun g => ?_⟩
      have e1 : (Q⁻¹ * w)⁻¹ * cj Q ρ (F.φ v g) * (Q⁻¹ * w) = w⁻¹ * ρ (F.φ v g) * w := by
        rw [cj_apply]; group
      have e2 : (((Q⁻¹ * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (qi * z (F.φ v g) * q - dY F (mat (cj Q ρ)) (qi * Y * q) (F.φ v g)) *
          ((Q⁻¹ * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
          ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) (Qbar l)) := by
        simp only [hinv, hmul, dY, hm, mul_sub, sub_mul, mul_assoc, a1]
      rw [e1, e2]
      exact hw g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.ChiMapOfRep
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

section SlopeTestRemainingChoices

open Polynomial

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  rw [← Matrix.charpoly_map]
  change (GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  have h : ∀ a, algebraMap A K[X] a = C (f a) := fun _ => rfl
  by_cases hij : i = j
  · subst hij
    simp [GDet.repAlg, h]
  · simp [GDet.repAlg, h, hij]

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ A[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  by_cases hij : i = j
  · subst hij
    simp [GDet.repAlg]
  · simp [GDet.repAlg, hij]

private theorem aeval_mapM {n : ℕ} {A K : Type} [CommRing A] [CommRing K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (q : A[X]) :
    f.mapMatrix (aeval M q) = aeval (f.mapMatrix M) (q.map f) := by
  refine Polynomial.map_aeval_eq_aeval_map ?_ q M
  ext a i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_eq_diagonal, h]

private theorem aeval_inter {n : ℕ} {K : Type} [CommRing K] (M N Y : Matrix (Fin n) (Fin n) K)
    (h : N * Y = Y * M) (q : K[X]) : aeval N q * Y = Y * aeval M q := by
  have hp : ∀ k : ℕ, N ^ k * Y = Y * M ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc, ← pow_succ']
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mul, mul_add, hp, hq]
  | monomial k a => simp [aeval_monomial, ← Algebra.smul_def, hp]

private theorem key {n : ℕ} {A K : Type} [CommRing A] [IsDomain A] [Field K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (x : A) (c : K) (hc : c ≠ 0) (hx : f x ≠ 1)
    (hM : M.charpoly.map f = (X - C c) ^ n) (Y : Matrix (Fin n) (Fin n) A)
    (hY : x • (M * Y) = Y * M) : Y = 0 := by
  have h1 := aeval_inter M (x • M) Y (by rw [← hY, ← Matrix.smul_mul]) M.charpoly
  rw [Matrix.aeval_self_charpoly, mul_zero] at h1
  have hn : IsNilpotent (f.mapMatrix M - algebraMap K _ c) := by
    refine ⟨n, ?_⟩
    have := aeval_mapM f M M.charpoly
    rw [Matrix.aeval_self_charpoly, map_zero, hM] at this
    simpa using this.symm
  have hu : IsUnit (f.mapMatrix (x • M) - algebraMap K _ c) := by
    have e : f.mapMatrix (x • M) - algebraMap K _ c =
        f x • (f.mapMatrix M - algebraMap K _ c) + algebraMap K _ ((f x - 1) * c) := by
      ext a b
      by_cases h : a = b <;> simp [Matrix.algebraMap_eq_diagonal, h]
      ring
    rw [e]
    refine IsNilpotent.isUnit_add_right_of_commute (hn.smul _) ?_ (Algebra.commute_algebraMap_right _ _)
    exact (IsUnit.mk0 _ (mul_ne_zero (sub_ne_zero.2 hx) hc)).map _
  have hd : (aeval (x • M) M.charpoly).det ≠ 0 := by
    intro h0
    have h2 := RingHom.map_det f (aeval (x • M) M.charpoly)
    rw [h0, map_zero, aeval_mapM, hM, map_pow, map_sub, aeval_X, aeval_C] at h2
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hu.pow n)).ne_zero h2.symm
  have h3 : (aeval (x • M) M.charpoly).det • Y = 0 := by
    have := congrArg (fun W => (aeval (x • M) M.charpoly).adjugate * W) h1
    simpa only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero] using this
  ext i j
  have h4 := congrFun (congrFun h3 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
  exact (mul_eq_zero.1 h4).resolve_left hd

end SlopeTestRemainingChoices

theorem UpperTheory.V.Th.Nm.n4 :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] (r : Resid F O n) (ρ : F.G₀ →* GL (Fin n) O), r.V0ok → (GDet.ofRep (mat ρ)).map (res O O : O →+* ResidueField O) = r.Dbar → ∀ Z : Matrix (Fin n) (Fin n) O, (∀ g ∈ F.D0, ((F.eps O O g : Oˣ) : O) • (mat ρ g * Z) = Z * mat ρ g) → Z = 0 := by
  intro l _ n F O _ _ _ _ _ r ρ h hred Z hZ
  obtain ⟨-, h2, g, hg, h3⟩ := h
  ext i i'
  suffices H : Z = 0 by rw [H]
  refine key (res O O : O →+* ResidueField O) (mat ρ g) ((F.eps O O g : Oˣ) : O) (r.chib i g)
    (Units.ne_zero _) ?_ ?_ Z (hZ g hg)
  · intro h4
    apply h3
    apply Units.ext
    rw [Units.val_one, ← h4]
    exact ((res O O).commutes _).symm
  · have h := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) hred
    simp only [Resid.Dbar, chi_map_ofRep, chi_ofRep] at h
    rw [h]
    change (Matrix.diagonal _).charpoly = _
    rw [Matrix.charpoly_diagonal]
    simp only [fun k => h2 g hg k i]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.ResidPush
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem inc_local {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) : IsLocalHom (inc h) := by
  have hint : (inc h).IsIntegral := by
    have h0 : (algebraMap ℤ_[l] c'.O).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
    have e : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O := by
      ext a; rfl
    rw [← e] at h0
    exact RingHom.IsIntegral.tower_top _ _ h0
  exact RingHom.IsIntegral.isLocalHom hint (Subalgebra.inclusion_injective h)

private theorem pushCh_ker {H A B : Type} [Group H] [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (χ : H →* Aˣ) : (pushCh f χ).ker = χ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro hg
    apply Units.ext
    apply hf
    have := congrArg Units.val hg
    simpa using this
  · intro hg
    rw [hg, map_one]

private theorem polar_push {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) {O O' k k' : Type} [CommRing O] [CommRing O']
    [CommRing k] [CommRing k'] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [Algebra O k] [Algebra O' k']
    (i : O →+* O') (f : k →+* k') (hi : ∀ a, i (algebraMap ℤ_[l] O a) = algebraMap ℤ_[l] O' a)
    (hf : ∀ a, f (algebraMap O k a) = algebraMap O' k' (i a)) (χ : Fin n → F.G₀ →* kˣ)
    (hp : F.IsPolar O (GDet.ofRep (diagRep χ))) :
    F.IsPolar O' (GDet.ofRep (diagRep fun j => pushCh f (χ j))) := by
  intro B _ _ _ _ y
  letI : Algebra k B := ((algebraMap k' B).comp f).toAlgebra
  letI : Algebra O B := ((algebraMap O' B).comp i).toAlgebra
  haveI : IsScalarTower O k B := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap O' B (i a) = algebraMap k' B (f (algebraMap O k a))
    rw [hf, ← IsScalarTower.algebraMap_apply]
  have he : F.eps O' B = F.eps O B := by
    unfold GFrame.eps
    congr 1
    ext a
    change algebraMap O' B (algebraMap ℤ_[l] O' a) = algebraMap O' B (i (algebraMap ℤ_[l] O a))
    rw [hi]
  have hs : F.star O' B n y = F.star O B n y := by
    unfold GFrame.star GFrame.starOp
    simp only [he]
  have hr : GDet.repAlg (diagRep fun j => pushCh f (χ j)) B = GDet.repAlg (diagRep χ) B := by
    unfold GDet.repAlg
    congr 1
    ext g a b
    by_cases hab : a = b
    · subst hab
      simp [diagRep]
      rfl
    · simp [diagRep, hab]
  have := hp B y
  change (GDet.repAlg (diagRep χ) B _).det = (GDet.repAlg (diagRep χ) B _).det at this
  change (GDet.repAlg (diagRep fun j => pushCh f (χ j)) B _).det = (GDet.repAlg (diagRep fun j => pushCh f (χ j)) B _).det
  rw [hr, hs]
  exact this

theorem UpperTheory.V.Th.Nm.residPush :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c c' : Coef l) (h : c.O ≤ c'.O) (r : Resid F c.O n), ∃ r' : Resid F c'.O n, RPush h r r' ∧ (∀ u, r'.Ip u = r.Ip u) ∧ (r.V0ok → r'.V0ok) := by
  intro l _ n F c c' h r
  haveI := inc_local h
  let f : ResidueField c.O →+* ResidueField c'.O := ResidueField.map (inc h)
  have hfi : Function.Injective f := f.injective
  have hf : ∀ a, f (residue c.O a) = residue c'.O (inc h a) := fun a => ResidueField.map_residue _ a
  refine ⟨{ chib := fun i => pushCh f (r.chib i)
            chib_open := fun i => by rw [pushCh_ker f hfi]; exact r.chib_open i
            chib_inj := fun i j hij => r.chib_inj ?_
            polar := polar_push F (inc h) f (fun _ => rfl) hf r.chib r.polar
            psib := fun v i => pushCh f (r.psib v i)
            psib_open := fun v i => by rw [pushCh_ker f hfi]; exact r.psib_open v i
            th := fun v i => pushCh (inc h) (r.th v i)
            th_comm := fun v i g hg => by
              rw [MonoidHom.comp_apply, r.th_comm v i g hg, map_one] },
    ⟨f, hf, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun u => ?_, fun hv => ⟨fun i => ?_, fun g hg i j => ?_, ?_⟩⟩
  · ext g
    apply hfi
    have := congrArg Units.val (DFunLike.congr_fun hij g)
    simpa using this
  · simp only [Resid.Ip, pushCh_ker f hfi]
  · rw [pushCh_ker f hfi]; exact hv.1 i
  · change Units.map _ (r.chib i g) = Units.map _ (r.chib j g)
    rw [hv.2.1 g hg i j]
  · obtain ⟨g, hg, hne⟩ := hv.2.2
    refine ⟨g, hg, fun e => hne ?_⟩
    apply Units.ext
    apply hfi
    have := congrArg Units.val e
    rw [Units.val_one, map_one]
    exact (hf _).trans this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.TrZero
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.trZero_inner {K : Type} [Field K] {n : ℕ}
    (D : Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K)
    (hD : ∀ A B, D (A * B) = D A * B + A * D B) : ∃ Y, ∀ A, D A = A * Y - Y * A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun A => Subsingleton.elim _ _⟩
  let o : Fin n := ⟨0, hn⟩
  refine ⟨-∑ i, D (single i o 1) * single o i 1, fun A => ?_⟩
  have h1 : ∀ i, A * single i o (1 : K) = ∑ j, A j i • single j o (1 : K) := by
    intro i
    ext a b
    by_cases hb : o = b
    · subst hb
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, hb, Matrix.mul_apply]
  have h2 : ∀ j, single o j (1 : K) * A = ∑ i, A j i • single o i (1 : K) := by
    intro j
    ext a b
    by_cases ha : o = a
    · subst ha
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, ha, Matrix.mul_apply]
  have h3 : ∑ i, single i o (1 : K) * single o i (1 : K) = (1 : Matrix (Fin n) (Fin n) K) := by
    simp only [Matrix.single_mul_single_same, mul_one]
    exact Matrix.sum_single_one
  have h4 : A * ∑ i, D (single i o 1) * single o i 1
      = (∑ i, D (single i o 1) * single o i 1) * A - D A := by
    have e1 : ∀ i, A * (D (single i o 1) * single o i (1 : K))
        = D (A * single i o 1) * single o i 1 - D A * (single i o 1 * single o i 1) := by
      intro i
      rw [hD]; noncomm_ring
    rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_sub_distrib,
      ← Finset.mul_sum, h3, mul_one, Finset.sum_mul]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [h1, map_sum, map_smul, Finset.sum_mul, mul_assoc, h2, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  rw [mul_neg, neg_mul, h4]; abel

theorem UpperTheory.V.Th.Nm.trZero :
    ∀ {K G : Type} [Field K] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) K) (z : G → Matrix (Fin n) (Fin n) K), Submodule.span K (Set.range (mat ρ)) = ⊤ → (∀ g g', z (g * g') = z g + mat ρ g * z g' * mat ρ g⁻¹) → (∀ g, (z g * mat ρ g).trace = 0) → ∃ Y, ∀ g, z g = mat ρ g * Y * mat ρ g⁻¹ - Y := by
  intro K G _ _ n ρ z hsp hc ht
  have hmul : ∀ g h, mat ρ (g * h) = mat ρ g * mat ρ h := by
    intro g h; simp [mat]
  have hone : mat ρ 1 = 1 := by simp [mat]
  have hinv : ∀ g, mat ρ g⁻¹ * mat ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, hone]
  have hinv' : ∀ g, mat ρ g * mat ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, hone]
  let d : G → Matrix (Fin n) (Fin n) K := fun g => z g * mat ρ g
  have hd : ∀ g h, d (g * h) = d g * mat ρ h + mat ρ g * d h := by
    intro g h
    simp only [d]
    rw [hc, hmul, add_mul, mul_assoc (mat ρ g * z h), ← mul_assoc (mat ρ g⁻¹), hinv, one_mul]
    simp only [mul_assoc]
  let R := Finsupp.linearCombination K (mat ρ)
  let E := Finsupp.linearCombination K d
  have hR : LinearMap.range R = ⊤ := by rw [Finsupp.range_linearCombination]; exact hsp
  have hker : ∀ y, R y = 0 → E y = 0 := by
    intro y hy
    have key : ∀ h, ∀ y : G →₀ K, (d h * R y).trace + (mat ρ h * E y).trace = 0 := by
      intro h y
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
        simp only [map_add (f := _), mul_add, trace_add]
        linear_combination ha + hb
      | single g a =>
        have := ht (h * g)
        change (d (h * g)).trace = 0 at this
        rw [hd, trace_add] at this
        simp only [R, E, Finsupp.linearCombination_single, mul_smul_comm, trace_smul, smul_eq_mul]
        rw [← mul_add, this, mul_zero]
    have k2 : ∀ A : Matrix (Fin n) (Fin n) K, (A * E y).trace = 0 := by
      intro A
      have hA : A ∈ Submodule.span K (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
      induction hA using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        simpa [hy] using key h y
      | zero => simp
      | add a b _ _ ha hb => simp [add_mul, ha, hb]
      | smul a b _ hb => simp [hb]
    ext i j
    simpa [Matrix.trace_single_mul] using k2 (single j i 1)
  obtain ⟨s, hs⟩ := R.exists_rightInverse_of_surjective hR
  let D := E ∘ₗ s
  have hDg : ∀ g, D (mat ρ g) = d g := by
    intro g
    have h0 : R (s (mat ρ g) - Finsupp.single g 1) = 0 := by
      have := LinearMap.congr_fun hs (mat ρ g)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [map_sub, this]; simp [R]
    have := hker _ h0
    rw [map_sub, sub_eq_zero] at this
    simpa [D, E] using this
  have hD : ∀ A B, D (A * B) = D A * B + A * D B := by
    intro A B
    have hA : A ∈ Submodule.span K (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
    have hB : B ∈ Submodule.span K (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hB using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        rw [← hmul, hDg, hDg, hDg, hd]
      | zero => simp
      | add a b _ _ ha hb => simp only [mul_add, map_add (f := _), ha, hb]; abel
      | smul a b _ hb => simp only [mul_smul_comm, map_smul, hb, smul_add]
    | zero => simp
    | add a b _ _ ha hb => simp only [add_mul, map_add (f := _), ha, hb]; abel
    | smul a b _ hb => simp only [smul_mul_assoc, map_smul, hb, smul_add]
  obtain ⟨Y, hY⟩ := UpperTheory.V.Th.Nm.trZero_inner D hD
  refine ⟨Y, fun g => ?_⟩
  have h1 := hY (mat ρ g)
  rw [hDg] at h1
  have h2 : z g = d g * mat ρ g⁻¹ := by simp only [d]; rw [mul_assoc, hinv', mul_one]
  rw [h2, h1, sub_mul, mul_assoc Y, hinv', mul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.DerOf
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Nm.derOf :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (B : UniversalOrdinaryDeterminantRing r) [IsCO O (DualNumber O)] (p : Pair r (DualNumber O)) (D : GDet n O F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Oˣ), p.Maps (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) D ψ → ∃ (x : B.B →ₐ[O] O) (δ : B.B →ₗ[O] O), IsDer x δ ∧ B.u.Maps x.toRingHom D ψ ∧ (∀ g, δ (B.u.D.tr (MonoidAlgebra.single g 1)) = (p.D.tr (MonoidAlgebra.single g 1)).snd) ∧ ∀ v i g, δ (B.u.ψ v i g : B.Bˣ) = ((p.ψ v i g : (DualNumber O)ˣ) : DualNumber O).snd := by
  intro l _ n F O _ _ _ r B _ p D ψ hp
  obtain ⟨f, ⟨hD, hψ⟩, -⟩ := B.univ (DualNumber O) p
  refine ⟨(TrivSqZeroExt.fstHom O O O).comp f, (TrivSqZeroExt.sndHom O O).comp f.toLinearMap, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b
    change (f (a * b)).snd = (f a).fst • (f b).snd + (f b).fst • (f a).snd
    rw [map_mul, DualNumber.snd_mul, smul_eq_mul, smul_eq_mul]
    ring
  · rw [← hp.1, ← hD, (UpperTheory.V.CA.d_gmap B.u.D).2.1]
    rfl
  · intro v i
    rw [← hp.2 v i, ← hψ v i]
    rfl
  · intro g
    have h := ((UpperTheory.V.CA.d_gmap B.u.D).2.2.1 (f : B.B →+* DualNumber O) (MonoidAlgebra.single g 1)).2 1
    rw [hD, MonoidAlgebra.mapRingHom_single, map_one] at h
    change (f (B.u.D.lam 1 (MonoidAlgebra.single g 1))).snd = (p.D.lam 1 (MonoidAlgebra.single g 1)).snd
    rw [h]
    rfl
  · intro v i g
    rw [← hψ v i]
    rfl
end

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem ofRep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (ρ : G →* GL (Fin n) A) (φ : H →* G) :
    (GDet.ofRep (mat ρ)).comap φ = GDet.ofRep (mat (ρ.comp φ)) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg (mat ρ) B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (mat (ρ.comp φ)) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg, mat]

private theorem tr_cj {n : ℕ} {K : Type} [Field K] (Q A : GL (Fin n) K) (Z : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ((a • (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z * Q)) * ((Q⁻¹ * A * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).trace = 0) :
    (Z * (A : Matrix (Fin n) (Fin n) K)).trace = 0 := by
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_eq_zero, or_iff_right ha] at h
  have e : ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z * Q * ((Q⁻¹ * A * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Z * A) * Q := by
    simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rwa [e, Matrix.trace_mul_cycle, Units.mul_inv, Matrix.one_mul] at h

private theorem mat_push {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (ρ : G →* GL (Fin n) A) :
    f.mapMatrix.toMonoidHom.comp (mat ρ) = mat (pushRep f ρ) := rfl

private theorem mat_push' {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (ρ : G →* GL (Fin n) A) (g : G) :
    (mat ρ g).map f = (pushRep f ρ g : Matrix (Fin n) (Fin n) B) := rfl

private theorem map_pt {n : ℕ} {O R K G : Type} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K] [Group G]
    (D : GDet n R G) (x : R →ₐ[O] O) (ρ : G →* GL (Fin n) O) (h : D.map x.toRingHom = GDet.ofRep (mat ρ)) :
    D.map (((Algebra.ofId O K).comp x : R →ₐ[O] K) : R →+* K) = GDet.ofRep (mat (pushRep (algebraMap O K) ρ)) := by
  have e1 := (CA.d_gmap D).2.1 x.toRingHom (algebraMap O K)
  rw [h, (CA.d_gmap (GDet.ofRep (mat ρ))).2.2.2 (algebraMap O K) (mat ρ), mat_push] at e1
  exact e1.symm

private theorem map_ch {O R K G : Type} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K] [Group G]
    (χ : G →* Rˣ) (x : R →ₐ[O] O) (χ' : G →* Oˣ) (h : pushCh x.toRingHom χ = χ') :
    pushCh (((Algebra.ofId O K).comp x : R →ₐ[O] K) : R →+* K) χ = pushCh (algebraMap O K) χ' := by
  subst h
  rfl

private theorem tr_fin {n : ℕ} {O K : Type} [CommRing O] [Field K] (f : O →+* K) (Q A : GL (Fin n) K) (Z : Matrix (Fin n) (Fin n) K) (a : K)
    (ha : a ≠ 0) (Z₀ A₀ : Matrix (Fin n) (Fin n) O)
    (h1 : Z₀.map f = a • (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z * Q))
    (h2 : A₀.map f = ((Q⁻¹ * A * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (h : (Z₀ * A₀).trace = 0) :
    (Z * (A : Matrix (Fin n) (Fin n) K)).trace = 0 := by
  have e2 := congrArg f h
  rw [map_zero, AddMonoidHom.map_trace f, Matrix.map_mul, h1, h2] at e2
  exact tr_cj Q A Z a ha e2

private theorem re_form {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing K] [Algebra O K]
    (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (h : F.IsForm O n ρ P) : (reIu F I).IsForm O n ρ P := h

private theorem re_coc {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l))
    (h : IsOrdCoc F ρ P I ψ z) : IsOrdCoc (reIu F I) ρ P (reIu F I).Iu ψ z := ⟨h.cont, h.coc, h.pol, h.ine, h.ord⟩

private theorem modelF {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (q : ℕ) (sg : Fin q → F.G₀) (h1 : Continuous ρ)
    (h2 : Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤) (h3 : F.IsForm c.O n ρ P)
    (h4 : (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) (h5 : ∀ u, ∀ g ∈ I u, ρ g = 1)
    (h6 : ∀ v, ∃ g, Function.Injective fun i => ψ v i g) (h7 : ∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c.O (Qbar l)).comp (F.φ v))
    (h8 : IsOrdCoc F ρ P I ψ z) (h9 : ∀ g, IntM (mat ρ g)) (h10 : IntM (P : Matrix (Fin n) (Fin n) (Qbar l)))
    (h11 : IntM ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) (h12 : ∀ j, (mat ρ (sg j)).charpoly.Separable) (c₁ : Coef l) :
    ∃ (c' : Coef l) (y : Pt (reIu F I) c'.O n) (z₀ : F.G₀ → Matrix (Fin n) (Fin n) c'.O) (a : Qbar l) (al : Fin q → Fin n → c'.O),
      c₁.O ≤ c'.O ∧ IsModel y ρ P ψ ∧ a ≠ 0 ∧ (∀ g, (z₀ g).map (algebraMap c'.O (Qbar l)) = a • z g) ∧ OCoc y z₀ ∧
      ∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)) :=
  model (reIu F I) c ρ P ψ z q sg h1 h2 (re_form F I _ _ ρ P h3) h4 h5 h6 h7 (re_coc F I ρ P ψ z h8) h9 h10 h11 h12 c₁

private theorem shr2 {l : ℕ} [Fact l.Prime] {n : ℕ} {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Algebra O (Qbar l)] {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (x : B.B →ₐ[O] O) {I : F.St → Subgroup F.G₀} (y : Pt (reIu F I) O n)
    (ρ₀ : F.G₀ →* GL (Fin n) O) (ψ₀ : ∀ v, Fin n → F.Gv v →* Oˣ) (e1 : @Eq (F.G₀ →* GL (Fin n) O) y.ρ ρ₀)
    (e2 : @Eq (∀ v, Fin n → F.Gv v →* Oˣ) y.ψ ψ₀) {q : ℕ} (sg : Fin q → F.G₀) (al : Fin q → Fin n → O)
    (h1 : B.u.Maps x.toRingHom (GDet.ofRep (mat ρ₀)) ψ₀)
    (h2 : ∀ Z : Matrix (Fin n) (Fin n) O, (∀ g ∈ F.D0, ((F.eps O O g : Oˣ) : O) • (mat ρ₀ g * Z) = Z * mat ρ₀ g) → Z = 0)
    (h3 : ∀ j, Function.Injective (al j) ∧ (mat ρ₀ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)))
    (h4 : DetQ F O (pushRep (algebraMap O (Qbar l)) ρ₀) (GeneralLinearGroup.map (algebraMap O (Qbar l)) y.P) (Set.range sg))
    (I' : F.St → Subgroup F.G₀) (h : ∀ u, I' u ≤ I u) : ∃ y : Pt (reIu F I') O n,
        B.u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ ∧ y.N4 F.D0 ∧
        (∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) ∧
        DetQ (reIu F I') O (pushRep (algebraMap O (Qbar l)) y.ρ) (GeneralLinearGroup.map (algebraMap O (Qbar l)) y.P) (Set.range sg) := by
  subst e1 e2
  exact ⟨shrink y I' h, h1, h2, h3, h4⟩

private theorem detq_tr' {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (Qbar l)] [CommRing O'] [Algebra ℤ_[l] O'] [Algebra O' (Qbar l)]
    (e : (algebraMap O (Qbar l)).comp (algebraMap ℤ_[l] O) = (algebraMap O' (Qbar l)).comp (algebraMap ℤ_[l] O'))
    (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (S : Set F.G₀) (h : DetQ F O ρ P S) : DetQ F O' ρ P S := by
  have e' : F.eps O (Qbar l) = F.eps O' (Qbar l) := by rw [GFrame.eps, GFrame.eps, e]
  unfold DetQ at h
  rw [e'] at h
  exact h

private theorem pairF {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (r : Resid F c.O n) (I : F.St → Subgroup F.G₀)
    (hI : I = r.Ip) (y : Pt (reIu F I) c.O n) (z : F.G₀ → Matrix (Fin n) (Fin n) c.O) [IsCO c.O c.O] [IsCO c.O (DualNumber c.O)]
    (ρ₀ : F.G₀ →* GL (Fin n) c.O) (ψ₀ : ∀ v, Fin n → F.Gv v →* c.Oˣ) (e1 : @Eq (F.G₀ →* GL (Fin n) c.O) y.ρ ρ₀)
    (e2 : @Eq (∀ v, Fin n → F.Gv v →* c.Oˣ) y.ψ ψ₀) (hn : 1 ≤ n) (hO : OCoc y z)
    (h1 : (GDet.ofRep (mat ρ₀)).map (res c.O c.O : c.O →+* ResidueField c.O) = r.Dbar) (h2 : ∀ v i, r.IsPsi v i (ψ₀ v i)) :
    ∃ p : Pair r (DualNumber c.O), p.Maps (TrivSqZeroExt.fstHom c.O c.O c.O : DualNumber c.O →+* c.O) (GDet.ofRep (mat ρ₀)) ψ₀ ∧
      (∀ g, (p.D.tr (MonoidAlgebra.single g 1)).snd = (z g * mat ρ₀ g).trace) ∧
      ∀ v i, ∀ g ∈ F.Iv v, ((p.ψ v i g : (DualNumber c.O)ˣ) : DualNumber c.O).snd = 0 := by
  subst e1 e2 hI
  exact pairDual F c r y z hn hO h1 h2

private theorem modelG {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (c : Coef l) (y : Pt (reIu F I) c.O n)
    (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (h : IsModel y ρ P ψ)
    {q : ℕ} (sg : Fin q → F.G₀) (al : Fin q → Fin n → c.O)
    (hal : ∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) :
    ∃ (ρ₀ : F.G₀ →* GL (Fin n) c.O) (ψ₀ : ∀ v, Fin n → F.Gv v →* c.Oˣ), @Eq (F.G₀ →* GL (Fin n) c.O) y.ρ ρ₀ ∧
      @Eq (∀ v, Fin n → F.Gv v →* c.Oˣ) y.ψ ψ₀ ∧ pushRep (algebraMap c.O (Qbar l)) ρ₀ = ρ ∧
      GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P = P ∧ (∀ v i, pushCh (algebraMap c.O (Qbar l)) (ψ₀ v i) = ψ v i) ∧
      ∀ j, Function.Injective (al j) ∧ (mat ρ₀ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)) :=
  ⟨y.ρ, y.ψ, rfl, rfl, h.1, h.2.1, h.2.2, hal⟩

private theorem nmAbs {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (r : Resid F c.O n) (B : UniversalOrdinaryDeterminantRing r)
    (x : B.B →ₐ[c.O] Qbar l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (hn : 1 ≤ n) (h0 : r.V0ok)
    (hD : B.u.D.map (x : B.B →+* Qbar l) = GDet.ofRep (mat ρ)) (hc : Continuous ρ)
    (hsp : Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤) (hform : F.IsForm c.O n ρ P)
    (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (hψ : ∀ v i, ψ v i = pushCh (x : B.B →+* Qbar l) (B.u.ψ v i))
    (hreg : ∀ v, ∃ g, Function.Injective fun i => ψ v i g)
    (hN1 : ∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c.O (Qbar l)).comp (F.φ v))
    (q : ℕ) (sg : Fin q → F.G₀) (hsg : ∀ j, (mat ρ (sg j)).charpoly.Separable) (hdet : DetQ F c.O ρ P (Set.range sg))
    (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (hz : IsOrdCoc F ρ P r.Ip ψ z)
    (hB : ∀ (c' : Coef l) (r' : Resid F c'.O n) (R : Type) [CommRing R] [Algebra c'.O R] [IsCO c'.O R], Nonempty (Pair r' R) → Nonempty (UniversalOrdinaryDeterminantRing r')) :
    ∃ (c' : Coef l) (r' : Resid F c'.O n) (B' : UniversalOrdinaryDeterminantRing r') (x' : B'.B →ₐ[c'.O] c'.O) (δ : B'.B →ₗ[c'.O] c'.O) (al : Fin q → Fin n → c'.O),
      B'.u.D.map (((Algebra.ofId c'.O (Qbar l)).comp x' : B'.B →ₐ[c'.O] Qbar l) : B'.B →+* Qbar l) = GDet.ofRep (mat ρ) ∧
      (∀ v i, pushCh (((Algebra.ofId c'.O (Qbar l)).comp x' : B'.B →ₐ[c'.O] Qbar l) : B'.B →+* Qbar l) (B'.u.ψ v i) = ψ v i) ∧
      IsDer x' δ ∧ (∀ v i, ∀ g ∈ F.Iv v, δ (B'.u.ψ v i g : B'.Bˣ) = 0) ∧
      ((∀ g, δ (B'.u.D.tr (MonoidAlgebra.single g 1)) = 0) → ∃ Y, ∀ g, z g = dY F (mat ρ) Y g) ∧
      ∀ I : F.St → Subgroup F.G₀, (∀ u, I u ≤ r'.Ip u) → ∃ y : Pt (reIu F I) c'.O n,
        B'.u.Maps x'.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ ∧ y.N4 F.D0 ∧
        (∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) ∧
        DetQ (reIu F I) c'.O (pushRep (algebraMap c'.O (Qbar l)) y.ρ) (GeneralLinearGroup.map (algebraMap c'.O (Qbar l)) y.P) (Set.range sg) := by
  obtain ⟨Q, P', hP', hsgn, hP1, hP2, hint⟩ := selfDual F c ρ P hc hsp hform
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := conjAll F c ρ P Q P' hP'
  have hD' : B.u.D.map (x : B.B →+* Qbar l) = GDet.ofRep (mat (cj Q ρ)) := hD.trans k4.symm
  have hine := (Ws.Eb.relKill B x (cj Q ρ) (k2 hsp) hD').2
  obtain ⟨c₂, hc₂, hx₂⟩ := ((GradeZeroInterpolatingElement.coPt c B.B).1 x).1
  have hz' := k7 _ _ _ hz
  have hs : ∀ j, (mat (cj Q ρ) (sg j)).charpoly.Separable := fun j => by rw [k5]; exact hsg j
  have hm := modelF F r.Ip c (cj Q ρ) P' ψ _ q sg (k1 hc) (k2 hsp) (k3 hform) hsgn hine hreg hN1 hz' hint hP1 hP2 hs c₂
  obtain ⟨c', y, z₀, a, al, hle, hM, ha, hz₀, hO, hal'⟩ := hm
  obtain ⟨ρ₀, ψ₀, e1, e2, m1, m2, m3, hal⟩ := modelG F r.Ip c' y _ _ _ hM sg al hal'
  obtain ⟨r', hr', hIp, hV0⟩ := residPush F c c' (hc₂.trans hle) r
  haveI := (abelian₂.dvr_finite l c'.O).1
  haveI : IsCO c'.O (DualNumber c'.O) := co_sqz c'.O c'.O c'.O fun _ => rfl
  obtain ⟨hred, hpsi⟩ := redOf F c c' _ r r' B.B B.u x ρ₀ ψ₀ hr' (fun b => hle (hx₂ b))
    (hD'.trans (congrArg (fun t => GDet.ofRep (mat t)) m1.symm)) fun v i => (m3 v i).trans (hψ v i)
  obtain ⟨p, hp1, hp2, hp3⟩ := pairF F c' r' r.Ip (funext hIp).symm y z₀ ρ₀ ψ₀ e1 e2 hn hO hred hpsi
  obtain ⟨B'⟩ := hB c' r' _ ⟨p⟩
  obtain ⟨x', δ, hδ, hx', hδ1, hδ2⟩ := derOf F c'.O r' B' p _ _ hp1
  have h4 := detq_tr' F c.O c'.O ((IsScalarTower.algebraMap_eq _ _ _).symm.trans (IsScalarTower.algebraMap_eq _ _ _)) _ _ _ (k6 _ hdet)
  rw [← m1, ← m2] at h4
  refine ⟨c', r', B', x', δ, al, ?_, fun v i => ?_, hδ, fun v i g hg => (hδ2 v i g).trans (hp3 v i g hg), fun key => ?_,
    fun I hI => shr2 B' x' y ρ₀ ψ₀ e1 e2 sg al hx' (n4 F c'.O r' ρ₀ (hV0 h0) hred) hal h4 I fun u => (hI u).trans (hIp u).le⟩
  · exact (map_pt B'.u.D x' ρ₀ hx'.1).trans ((congrArg (fun t => GDet.ofRep (mat t)) m1).trans k4)
  · exact (map_ch _ x' _ (hx'.2 v i)).trans (m3 v i)
  · refine trZero ρ z hsp hz.coc fun g => tr_fin (algebraMap c'.O (Qbar l)) Q (ρ g) (z g) a ha (z₀ g) (mat ρ₀ g) (hz₀ g) ?_
      ((hp2 g).symm.trans ((hδ1 g).symm.trans (key g)))
    exact (mat_push' _ _ g).trans (congrArg Units.val ((DFunLike.congr_fun m1 g).trans (cj_apply Q ρ g)))

theorem UpperTheory.V.Th.ordVan2 :
    Af.HypothesesH → OrdVan2 := by
  intro hP l _ L Ω _ _ _ _ _ _ s V c n r B ι x h ρ P hS hn2 hn4 h0 hA hD hc haut hsp hform hI0 hN1 ⟨q, sg, hsg, hdet⟩ z hz
  have hn : 1 ≤ n := by omega
  have hN := hP.litN
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have heps : ∀ v : V.frame.Vl, (V.frame.eps c.O (Qbar l)).comp (V.frame.φ v) =
      (cycBar L Ω l).comp (Dec (F := L) (s.A (Subtype.val v))).subtype := fun v => MonoidHom.ext fun g => by
    have e : V.ε (toGS Ω V.S' (W.resP L Ω g.1)) = cycZ (W.Lp L) Ω l (W.resP L Ω g.1) := DFunLike.congr_fun V.hε _
    apply Units.ext
    change algebraMap c.O (PadicAlgCl l) (algebraMap ℤ_[l] c.O (V.ε (toGS Ω V.S' (W.resP L Ω g.1)) : ℤ_[l]ˣ)) = _
    rw [e]
    rfl
  obtain ⟨c', r', B', x', δ, al, hDx, hψ', hδ, hδ2, hfin, hy⟩ := nmAbs V.frame c r B x ρ P hn h0 hD hc hsp hform x.psi (fun _ _ => rfl)
    (fun v => regArith hN s h v (x.psi v) hA.1 (hA.2 v)) (fun v i j _ e => hN1 v i j (e.trans (congrArg _ (heps v))))
    q sg (fun j => (hsg j).2) hdet z hz fun c' r' R _ _ _ => b0Ex (phiAll hC) l L Ω s V c' n r' R
  obtain ⟨Λ', -⟩ := lamEx (W.locCFT hN.aut.art hC) l L Ω s V c' n r'
  obtain ⟨J, hJ, hLev⟩ := hidaX hP l L Ω s V hS c' n hn r' B' Λ' ι
  have hψ : (barPt B' x').psi = x.psi := funext fun v => funext fun i => hψ' v i
  have hAr : (barPt B' x').Arith h := ⟨hA.1, fun v j => by rw [hψ]; exact hA.2 v j⟩
  have hR : (barPt B' x').IsRep (ρ.comp V.pr) :=
    (congrArg (fun D => GDet.comap D V.pr) hDx).trans (ofRep_comap ρ V.pr)
  have hF : ∀ v : Vl l L, HasFlag ((ρ.comp V.pr).comp (Dec (F := L) (s.A v)).subtype) (x.psi v) := fun v => by
    obtain ⟨w, Y, hw⟩ := hz.ord v
    exact ⟨w⁻¹, fun g => by rw [inv_inv]; exact ⟨(hw g).1, (hw g).2.1⟩⟩
  have hJx : J ≤ RingHom.ker (barPt B' x') :=
    hJ _ h (ρ.comp V.pr) hn2 hn4 hAr hR (hc.comp (V.pr_cont continuous_resP)) haut (fun g hg => hI0 _ ⟨g, hg, rfl⟩)
      fun v => by rw [hψ]; exact ⟨hF v, hN1 v⟩
  obtain ⟨y, y1, y2, y3, y4⟩ := hy (globOf r' V).frame.Iu fun u => by
    rintro g ⟨γ, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨Subtype.val γ, h1, rfl⟩, Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h2 i⟩
  exact hfin (coreO hN l L Ω s V c' n r' B' J y x' h q sg al hS hn hLev (fun b hb => Subtype.ext (hJx hb)) hAr y1 y2
    (fun j => ⟨(hsg j).1, y3 j⟩) y4 δ hδ hδ2)

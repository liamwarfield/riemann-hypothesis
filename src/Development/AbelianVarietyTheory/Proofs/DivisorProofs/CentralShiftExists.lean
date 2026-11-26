module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumValuesUnitOfClassSumValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

theorem glued_idempotent_units_mul_eq_one {e e' a ai b bi : A} (h1 : e * e = e) (h2 : e * e' = 0) (h3 : e' * e' = e') (ha : a * ai = 1)
    (hb : b * bi = 1) : (e * a + e' * bi + (1 - e - e')) * (e' * b + e * ai + (1 - e - e')) = 1 := by
  linear_combination (a * ai - a - ai + 1) * h1 + (a * b + bi * ai - a - bi - b - ai + 2) * h2 +
    (bi * b - bi - b + 1) * h3 + e * ha + e' * hb

def scal (n : ℕ) {u v : A} (h : u * v = 1) : GL (Fin n) A where
  val := u • (1 : Matrix (Fin n) (Fin n) A)
  inv := v • (1 : Matrix (Fin n) (Fin n) A)
  val_inv := by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, one_smul, one_mul]
  inv_val := by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm v, h, one_smul, one_mul]

theorem scal_mem (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) {u : A} (h : u * σ u = 1) :
    scal n h ∈ Formalism.UG.UJ σ J := by
  change Formalism.UG.cT σ (u • (1 : Matrix (Fin n) (Fin n) A)) * J * (u • (1 : Matrix (Fin n) (Fin n) A)) = J
  have h1 : Formalism.UG.cT σ (u • (1 : Matrix (Fin n) (Fin n) A)) = σ u • Formalism.UG.cT σ (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [h1, Formalism.UG.cT_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h, one_smul, one_mul, mul_one]

theorem map_smul_one {B : Type} [CommRing B] (f : A →+* B) (u : A) :
    (u • (1 : Matrix (Fin n) (Fin n) A)).map f = f u • (1 : Matrix (Fin n) (Fin n) B) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem smul_one_comm (u : A) (M : Matrix (Fin n) (Fin n) A) :
    M * (u • (1 : Matrix (Fin n) (Fin n) A)) = (u • (1 : Matrix (Fin n) (Fin n) A)) * M := by
  rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

theorem smul_one_supp {f u : A} (h : f * (u - 1) = u - 1) (i j : Fin n) :
    f * (u • (1 : Matrix (Fin n) (Fin n) A) - 1) i j = (u • (1 : Matrix (Fin n) (Fin n) A) - 1) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, h]
  · simp

theorem blockTri_of_scalar (b : Fin n → ℕ) {g : GL (Fin n) A} {u : A} (h : g.1 = u • (1 : Matrix (Fin n) (Fin n) A)) :
    g ∈ blockTri b := by
  intro i j hij
  show g.1 i j = 0
  have : i ≠ j := by
    rintro rfl
    exact lt_irrefl _ hij
  rw [h, Matrix.smul_apply, Matrix.one_apply_ne this, smul_zero]

theorem blockRestriction_of_scalar_eq_scalar {r : ℕ} (hr : r ≤ n) {g : GL (Fin n) A} {u : A} (h : g.1 = u • (1 : Matrix (Fin n) (Fin n) A))
    {k : GL (Fin r) A} (hk : k.1 = u • (1 : Matrix (Fin r) (Fin r) A)) : upperLeftBlock hr g = k := by
  apply Units.ext
  rw [upper_block_val_submatrix hr (blockTri_of_scalar _ h), h, hk]
  ext i j
  simp [Matrix.one_apply]

theorem scalar_of_center {ι : Type} {κ : ι → Type} [∀ i, CommRing (κ i)] {r : ℕ} {g : ∀ i, GL (Fin r) (κ i)}
    (hg : ∀ x, x * g = g * x) (i : ι) : ∃ u : (κ i)ˣ, (g i).1 = (u : κ i) • (1 : Matrix (Fin r) (Fin r) (κ i)) := by
  classical
  have h : g i ∈ Subgroup.center (GL (Fin r) (κ i)) := Subgroup.mem_center_iff.2 fun x => by
    have := congrFun (hg (Function.update 1 i x)) i
    simpa using this
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  rw [← hu]
  exact (Matrix.smul_one_eq_diagonal _).symm

end Generic

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem scalar_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {u v : Formalism.L2.Herm.intAf F E} (h : u * v = 1)
    {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x.1 = (u : E ⊗[F] Formalism.L2.Herm.Af F) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    x ∈ St β ∧ ∀ P, (redFn β P x).1 = resS F P u • (1 : Matrix (Fin n) (Fin n) (kP P)) := by
  have e : frGL β (scal n h) = x := by
    apply Units.ext
    have e1 : ((frGL β (scal n h) : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      β.1 * (u • (1 : Matrix (Fin n) (Fin n) _)).map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 := rfl
    rw [e1, map_smul_one, smul_one_comm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hx]
    rfl
  subst e
  refine ⟨⟨_, rfl⟩, fun P => ?_⟩
  rw [redFn_frGL]
  exact map_smul_one (resS F P) u

theorem exists_int_res (S : Finset (Pl E)) (c : ∀ P : S, (kP P.1)ˣ) :
    ∃ a : 𝓞 E, a ≠ 0 ∧ ∀ P : S, Ideal.Quotient.mk P.1.asIdeal a = (c P : kP P.1) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨Q, hQ⟩
  · exact ⟨1, one_ne_zero, fun P => absurd P.2 (Finset.notMem_empty _)⟩
  choose x hx using fun P : S => Ideal.Quotient.mk_surjective (I := P.1.asIdeal) (c P : kP P.1)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun P => P.asIdeal) (fun _ => 1)
    (fun P _ => P.prime) (fun P _ P' _ h h' => h (HeightOneSpectrum.ext h')) x
  have key : ∀ P : S, Ideal.Quotient.mk P.1.asIdeal y = (c P : kP P.1) := fun P => by
    rw [← hx P]
    exact Ideal.Quotient.eq.2 (by simpa using hy P.1 P.2)
  refine ⟨y, ?_, key⟩
  rintro rfl
  have := Q.isPrime
  exact (c ⟨Q, hQ⟩).ne_zero ((key ⟨Q, hQ⟩).symm.trans (map_zero _))

theorem res_of_mul_eq (P : Pl E) {p u w : Formalism.L2.Herm.intAf F E} (hp : resS F P p = 1) (h : p * u = p * w) :
    resS F P u = resS F P w := by
  have := congrArg (resS F P) h
  rwa [map_mul, map_mul, hp, one_mul, one_mul] at this

end Frame

section Adelic

open GlobalTheory.LevSplit

variable {D : D7}

theorem exists_idemSum (P : Finset (Pl D.host.E)) (h : ∀ Q ∈ P, ∀ Q' ∈ P, ¬ Lev.IsConjPl Q Q') :
    ∃ e : Formalism.L2.Theta.AE D, IsIdemSum e P :=
  GlobalTheory.GridIdem.exists_isIdemSum P (fun Q hQ => GlobalTheory.ParahoricLift.exists_isIdemAt (h Q hQ Q hQ))
    fun Q hQ Q' hQ' e => (GlobalTheory.IdemSupport.eq_or_eq_cP e).resolve_right fun e' =>
      h Q' hQ' Q hQ ((GlobalTheory.IdemSupport.isConjPl_iff Q' Q).2 e')

theorem sum_mul_mem {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (B : Subring R') (p : ι → R) (c : R)
    (s : Finset ι) (h : ∀ i ∈ s, f (p i * c) ∈ B) : f ((∑ i ∈ s, p i) * c) ∈ B := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum]; exact sum_mem h

theorem idemSum_div_int {e : Formalism.L2.Theta.AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {a : 𝓞 D.host.E}
    (h0 : a ≠ 0) (ha : ∀ P ∈ S, a ∉ P.asIdeal) :
    finSw D (e * incA D ((a : D.host.E)⁻¹)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  exact sum_mul_mem (finSw D) _ es _ S fun P hP =>
    swapAE_int (not_not.1 fun hn => ha P hP (((hes P hP).2 a h0).2 hn))

theorem unit_aux {R T : Type} [CommRing R] [CommRing T] (c : R →+* R) (hc : ∀ x, c (c x) = x) (f : R →+* T)
    (B : Subring T) (hB : ∀ x, f x ∈ B → f (c x) ∈ B) {e a ai : R} (h1 : e * e = e) (h2 : e * c e = 0) (ha : a * ai = 1)
    (i1 : f e ∈ B) (i2 : f a ∈ B) (i3 : f (e * ai) ∈ B) :
    ∃ u, u * c u = 1 ∧ f u ∈ B ∧ (e + c e) * (u - 1) = u - 1 ∧ e * u = e * a := by
  have h3 : c e * c e = c e := by rw [← map_mul, h1]
  have hb : c a * c ai = 1 := by rw [← map_mul, ha, map_one]
  refine ⟨e * a + c e * c ai + (1 - e - c e), ?_, ?_, ?_, ?_⟩
  · simp only [map_add (f := _), map_mul, map_sub, map_one, hc]
    rw [sub_right_comm 1 (c e) e]
    exact glued_idempotent_units_mul_eq_one h1 h2 h3 ha hb
  · rw [← map_mul c, map_add (f := _), map_add (f := _), map_sub, map_sub, map_one, map_mul]
    exact add_mem (add_mem (mul_mem i1 i2) (hB _ i3)) (sub_mem (sub_mem (one_mem _) i1) (hB _ i1))
  · linear_combination (a - 1) * h1 + (a + c ai - 2) * h2 + (c ai - 1) * h3
  · linear_combination (a - 1) * h1 + (c ai - 1) * h2

theorem finSw_cA_int (x : Formalism.L2.Theta.AE D) (h : finSw D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    finSw D (cA D x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [finSw_cA]
  exact sigR_int h

theorem exists_norm_one {e : Formalism.L2.Theta.AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    (c : ∀ P : S, (kP P.1)ˣ) : ∃ u : Formalism.L2.Theta.AE D, u * cA D u = 1 ∧ (e + cA D e) * (u - 1) = u - 1 ∧
      ∃ hu : finSw D u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
        ∀ P : S, resS D.host.F P.1 ⟨finSw D u, hu⟩ = (c P : kP P.1) := by
  obtain ⟨a, h0, ha⟩ := exists_int_res S c
  have hn : ∀ P ∈ S, a ∉ P.asIdeal := fun P hP h => by
    have := P.isPrime
    exact (c ⟨P, hP⟩).ne_zero ((ha ⟨P, hP⟩).symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
  have h0' : (a : D.host.E) ≠ 0 := fun h => h0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨i1, r1⟩ := GlobalTheory.TameProd.resS_idemSum he
  have i1' : finSw D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := i1
  have i2 : finSw D (incA D (a : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (oToS D.host.F D.host.E a).2
  have hai : incA D (a : D.host.E) * incA D ((a : D.host.E)⁻¹) = 1 := by
    rw [← RingHom.map_mul, mul_inv_cancel₀ h0', RingHom.map_one]
  obtain ⟨u, u1, u2, u3, u4⟩ := unit_aux (cA D) Formalism.L2.Theta.cA_cA (finSw D) _ finSw_cA_int
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hai i1' i2 (idemSum_div_int he h0 hn)
  refine ⟨u, u1, u3, u2, fun P => ?_⟩
  have e1 : (⟨finSw D e, i1'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨finSw D u, u2⟩ =
      ⟨finSw D e, i1'⟩ * oToS D.host.F D.host.E a :=
    Subtype.ext (((finSw D).map_mul _ _).symm.trans ((congrArg (finSw D) u4).trans ((finSw D).map_mul _ _)))
  exact (res_of_mul_eq P.1 (r1 P.1 P.2) e1).trans ((resS_oToS P.1 a).trans (ha P))

theorem exists_central_lift (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {e : Formalism.L2.Theta.AE D} (he : IsIdemSum e L.Pg) {g : G0 L.Pg L.r} (hg : ∀ x, x * g = g * x) :
    ∃ ζ ∈ Subgroup.center (GA D V), SuppAt e V ζ ∧ Lev.IsLevelLift V β L g ζ := by
  choose c hc using scalar_of_center hg
  obtain ⟨u, u1, u2, hu, u3⟩ := exists_norm_one he c
  obtain ⟨ζ, hζ⟩ : ∃ ζ : GA D V, mt V ζ = u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
    ⟨⟨scal V.rank u1, scal_mem _ _ u1⟩, rfl⟩
  have hs : SuppAt e V ζ := fun i j => by
    rw [hζ]
    exact smul_one_supp u2 i j
  have h0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hf : ζ ∈ GfC V := GlobalTheory.IdemSupport.mem_GfC_of_suppF V (f := e + cA D e)
    (by rw [RingHom.map_add (f := _), h0, GlobalTheory.PlaceDatum.infPart_cA h0, add_zero]) hs
  have huv : (⟨finSw D u, hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨finSw D (cA D u), finSw_cA_int u hu⟩ = 1 :=
    Subtype.ext (((finSw D).map_mul _ _).symm.trans ((congrArg (finSw D) u1).trans (finSw D).map_one))
  have hx : (Lev.finE V ζ).1 = finSw D u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) := by
    rw [finE_val, hζ]
    exact map_smul_one _ _
  obtain ⟨hS, hr⟩ := scalar_mem_St β huv hx
  refine ⟨ζ, Subgroup.mem_center_iff.2 fun y => GlobalTheory.IdemSupport.mt_inj V ?_, hs, hf,
    mem_parLev.2 ⟨finE_mem_UA V _, hS, fun P _ => blockTri_of_scalar _ (hr P), fun P _ => blockTri_of_scalar _ (hr P)⟩,
    funext fun P => blockRestriction_of_scalar_eq_scalar L.hr (hr P.1) ?_⟩
  · rw [GlobalTheory.IdemSupport.mt_mul, GlobalTheory.IdemSupport.mt_mul, hζ]
    exact smul_one_comm _ _
  · rw [u3 P]
    exact hc P

end Adelic

theorem inner_eq_of_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →ₗ[ℂ] H)
    (h : ∀ x, ‖T x‖ = ‖x‖) (y y' : H) : ⟪T y, T y'⟫_ℂ = ⟪y, y'⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨T, h⟩ y y'

theorem comm_of_center {G H : Type*} [Group G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {z : G}
    (hz : z ∈ Subgroup.center G) (g : G) (y : H) : ρ z (ρ g y) = ρ g (ρ z y) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.1 hz g, map_mul, Module.End.mul_apply]

theorem map_center {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {z : G} (hz : z ∈ Subgroup.center G) (x : H) :
    x * φ z = φ z * x := by
  obtain ⟨g, rfl⟩ := φ.surjective x
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]

end GlobalTheory.CentralShift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFifth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatOfInt
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh
variable {D : D7} {r g : ℕ}

theorem isMod_of (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (hm : Formalism.L2.Pj.ModelW W hr X)
    (hp : ∀ ρ, tauE D ρ ∈ X.Ψ) : IsMod W hr X := by
  have hpsi : ∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, h⟩ => h ▸ hp ρ⟩
    have h1 := (X.cmType τ).1 h
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.StdRat.tauE_cm D τ).2 (fun ⟨ρ, hρ⟩ => h1 (hρ ▸ hp ρ))
    exact ⟨ρ, hρ.symm⟩
  obtain ⟨ρ⟩ : Nonempty D.what₂.Tau := by
    by_contra hne
    have h := GlobalTheory.StdRat.tauE_cm D D.host.φ₀
    obtain ⟨ρ, -⟩ := h.2 (fun ⟨ρ, _⟩ => hne ⟨ρ⟩)
    exact hne ⟨ρ⟩
  refine ⟨hm, hpsi, ?_⟩
  have h1 := X.κ0_sign ⟨tauE D ρ, hp ρ⟩
  have h2 := xi_zero_im_pos D ρ
  rcases X.κ0_xi with h | h
  · rw [h, hm.2]; ring
  · exfalso
    rw [h, hm.2] at h1
    simp [map_ofNat] at h1
    linarith

end GlobalTheory.AdTh
end

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CoverVal

theorem perFr_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r} (h : SameSp X' X)
    (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X' x v τ i = perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X
  cases X'
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem sameSp_of {D : D7} {W : HSp D} {r : ℕ} {hr : W.rank = r} {X' X : Data D.host.E r} (h' : IsMod W hr X')
    (h : IsMod W hr X) (hp : X'.p0 = X.p0) : SameSp X' X :=
  ⟨Finset.ext fun τ => (h'.psi τ).trans (h.psi τ).symm, h'.model.1.trans h.model.1.symm, hp,
    h'.model.2.trans h.model.2.symm, h'.kap.trans h.kap.symm⟩

theorem realM_mul {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (γ k : GA D W)
    (δ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (hδ : ∀ (τ : D.host.E →+* ℂ) th, IsInfEmb τ th → archM W th γ = δ.map τ) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) :
    realM θ (Formalism.L2.Theta.mt W (γ * k)) τ = δ.map τ * realM θ (Formalism.L2.Theta.mt W k) τ := by
  have h1 := hδ τ (θ hτ.choose) (by have h := hθ hτ.choose; rwa [← hτ.choose_spec] at h)
  rw [realM, realM, dif_pos hτ, dif_pos hτ, ← h1]
  change archM W _ (γ * k) = _ * archM W _ k
  rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]


open CategoryTheory MonObj in
theorem marked_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

theorem move_congr {A : Type} [CommRing A] {n N : ℕ} (p q : Matrix (Fin n) (Fin n) A) {x x' b w w' : Fin n → A}
    (h : x - q *ᵥ b = N • w) (h' : x' - p *ᵥ (q *ᵥ b) = N • w') : p *ᵥ x - x' = N • (p *ᵥ w - w') := by
  rw [smul_sub, ← h', ← Matrix.mulVec_smul, ← h, Matrix.mulVec_sub, sub_sub_sub_cancel_right]

theorem point_eq {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (h1 : 1 ≤ r) (hA : l.A = 1) {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (Wt : UW U) (j : U.Comp) (x' : Frame (U.X j).Ψ r) (γ k : GA D W) (hγ : γ ∈ GQ W) (hm' : IsMod W hr (U.X j))
    (hL' : latR hr (latG W (γ * k)) = (U.X j).Λ) (hx' : x' = frMove θ W hr (U.X j) (γ * k) fun τ => x₀ τ.1)
    (hon : IsONFr (U.X j) x') (hk' : MarkAd l W hr ι (γ * k) (Wt.mark j))
    (X : Data D.host.E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (hm : IsMod W hr X) (hp : X.p0 = Dw.q) (hs : IsSympl X bas)
    (hi : IdxIs c σ X idx e) (hL : latR hr (latG W k) = X.Λ) (hmk : IsMark l X.Λ mk) (hk : MarkAd l W hr ι k mk) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y : FrPt Xo c ℂ) (A : AnFib X bas idx e (frMove θ W hr X k fun τ => x₀ τ.1) X.Λ y), A.Marked mk →
      ∃ h : x' ∈ (U.X j).dom, y.x = (U.un j ⟨x', h⟩).x := by
  let _ : Algebra c.F ℂ := σ.toAlgebra
  intro y A hA'
  subst hr
  obtain rfl : g = Wt.g := Fin.equiv_iff_eq.1 ⟨e.trans Wt.e.symm⟩
  obtain ⟨π, rfl⟩ : ∃ π : Equiv.Perm (Fin Wt.g), e = π.trans Wt.e :=
    ⟨e.trans Wt.e.symm, Equiv.ext fun a => (Wt.e.apply_symm_apply _).symm⟩
  obtain ⟨idx, rfl⟩ : ∃ idx' : Fin Wt.g ≃ X.Ψ × Fin W.rank, idx = π.trans idx' :=
    ⟨π.symm.trans idx, Equiv.ext fun a => congrArg idx (π.symm_apply_apply a).symm⟩
  have hsp : SameSp (U.X j) X := sameSp_of hm' hm ((hU.2.1 j).1.trans hp.symm)
  obtain ⟨-, hsd, -⟩ := uw_lattice _ H Dw l Xo c σ _ U hσ hU h1 Wt j
  obtain ⟨Dc, hDc, -⟩ := exists_dic _ H Dw l c σ _ Wt.g 0 (U.X j) 0 Wt.e hσ hU.1 (hU.2.1 j).1 (hU.2.1 j).2 hsd
    ⟨fun _ => antitone_const, Even.zero⟩
  have hper := Dc.per_eq
  have hty := Dc.ty_eq
  rw [hDc] at hper hty
  obtain ⟨hd', hu', -⟩ := hx_of_isONFr _ _ _ 0 (U.X j) Dc.bas Dc.idx Dc.sympl Even.zero x' hon
  obtain ⟨A', hA'', -⟩ := uw_anFib _ H Dw l Xo c σ _ U hσ hU h1 Wt j Dc.bas Dc.idx Dc.sympl hper hty ⟨x', hd'⟩ hu'
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix W γ hγ
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hG : X.Gm = -W.gram.transpose := hm.model.1
  have hun : IsUn X δ⁻¹ := fun u v => by rw [hG, ← hδu, hri, hri]
  have hR : ∀ L : Lt D.host.E W.rank, latR rfl L = L := fun L => Submodule.map_id L
  rw [hR] at hL hL'
  have hmem : ∀ v, v ∈ X.Λ ↔ δ.1 *ᵥ v ∈ (U.X j).Λ := fun v => by
    rw [← hL, ← hL', GlobalTheory.Member.LatMove.mem_lat_iff, GlobalTheory.Member.LatMove.mem_lat_iff,
      GlobalTheory.Member.LatMove.move_iff W γ k, hδf]
  obtain ⟨hd, -, hsd', A'', -, -, hM⟩ := anFib_move _ H Dw l Xo c _ _ (U.X j) X hsp Dc.bas Dc.idx bas idx Wt.e x' _ _ A' δ⁻¹
    Dc.sympl hs hd' hsd hun
    (fun v => funext fun a => by
      obtain ⟨a, rfl⟩ := π.surjective a
      exact (hper x' v _).trans ((perFr_cast hsp _ _ _ _).trans (hi.1 _ v a).symm))
    (fun a => by
      obtain ⟨a, rfl⟩ := π.surjective a
      exact (hty _).trans (hi.2 a).symm)
  have hM' := hM _ hA''
  have e1 : mapL δ⁻¹ (U.X j).Λ = X.Λ := Submodule.ext fun v => by
    rw [Lev.mem_mapL, inv_inv, hmem]; rfl
  have e2 : lact δ⁻¹ (castFr hsp.psi x') = frMove θ W rfl X k fun τ => x₀ τ.1 := by
    funext τ
    rw [hx']
    change (δ⁻¹).1.map τ.1 * (realM θ (Formalism.L2.Theta.mt W (γ * k)) τ.1 * x₀ τ.1) =
      realM θ (Formalism.L2.Theta.mt W k) τ.1 * x₀ τ.1
    rw [realM_mul hθ W γ k δ.1 hδa τ.1 ((hm.psi _).1 τ.2), ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul,
      Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  revert A'' hd hsd'
  rw [e1, e2]
  intro hd hsd' A'' _ hM'
  refine ⟨hd', anFib_point_eq _ H Dw l Xo c hA _ _ X bas idx Wt.e _ _ _ y A'' (Cmp.anFibRen π A) hs hd hsd' mk hmk
    (marked_congr A'' hM' fun a ha => ?_) hA'⟩
  obtain ⟨w, hw, ew⟩ := hk a ha
  obtain ⟨w', hw', ew'⟩ := hk' a ha
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (δ.1 *ᵥ mk a - Wt.mark j a) ((finHom W γ).1 *ᵥ w - w') (by
    have e3 : finVec W (δ.1 *ᵥ mk a - Wt.mark j a) = finVec W (δ.1 *ᵥ mk a) - finVec W (Wt.mark j a) :=
      funext fun i => TensorProduct.tmul_sub _ _ _
    rw [e3, ← hδf]
    exact move_congr _ _ ew (GlobalTheory.Member.LatMove.fin_mul W γ k _ ▸ ew'))
  refine ⟨(δ⁻¹).1 *ᵥ u, ?_, ?_⟩
  · rw [hmem, hri, ← hL', GlobalTheory.Member.LatMove.mem_lat_iff, hu]
    exact sub_mem (GlobalTheory.Member.LatMove.move_mem W γ k w hw) hw'
  · rw [← Matrix.mulVec_smul, ← eu, Matrix.mulVec_sub, hli]
    exact (add_sub_cancel _ _).symm

theorem evR_eq_of_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (σ : c.F →+* ℂ) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (y y' : FrPt Xo c (CAt σ)) (h : y'.x = y.x) : toC (evR Xo c f y') = toC (evR Xo c f y) :=
  GlobalTheory.WeightZeroValue.evR_conj E H Dw l Xo c σ (RingEquiv.refl ℂ) f hf y y'
    (h.trans ((CategoryTheory.Category.id_comp _).symm.trans
      (congrArg (CategoryTheory.CategoryStruct.comp · y.x) (AlgebraicGeometry.Spec.map_id _).symm)))

end GlobalTheory.AdTh.CoverVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicSchwartzFunctionLeftGLEquivariance
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicSchwartzFunctionLeftGLEquivariance
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

namespace GlobalTheory

theorem fFun_mul_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k),
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν Ψ g h
  let f : Matrix (Fin a) (Fin a) k →* Matrix C C k :=
    { toFun := fun M => (Matrix.fromBlocks M (0 : Matrix (Fin a) A' k) 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm
      map_one' := by rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
      map_mul' := fun M N => by
        rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp }
  let E : GL C k := Units.map f g
  have hE : ∀ M : Matrix (Fin a) (Fin a) k, f M = (Matrix.fromBlocks M (0 : Matrix (Fin a) A' k) 0 (1 : Matrix A' A' k)).submatrix σ.symm σ.symm := fun _ => rfl
  have hX : g.val * X0 k σ = X0 k σ * E.val := by
    ext i j
    rw [frameMatrixFirstColumnBlock_mul_apply]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [X0, E, hE, Matrix.mul_apply]
  have hY : Y0 k σ * (invT E).val = Y0 k σ := by
    ext i j
    rw [frameMatrixSecondColumnBlock_mul_apply, invT_val]
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [Y0, E, hE, ← map_inv, Matrix.one_apply, eq_comm]
  have hdet : gdet E = gdet g := by
    ext
    simp [E, hE, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have h1 : g.val * (X0 k σ * (invT h).val) = X0 k σ * (invT (invT E * h)).val := by
    rw [map_mul, invT_invT, Units.val_mul, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  have h2 : Y0 k σ * (invT E * h).val = Y0 k σ * h.val := by
    rw [Units.val_mul, ← Matrix.mul_assoc, hY]
  have h3 : gdet (invT E * h) = (gdet g)⁻¹ * gdet h := by rw [gdet_mul, gdet_invT, hdet]
  rw [h1, splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ, splitTheta_fFun_frameFirstBlock_mul μ σ ν Ψ, h2, h3, map_mul, map_inv, apow_mul, apow_inv, apow_neg,
    Units.val_mul, Units.val_inv_eq_inv_val]
  have hν : ((ν (gdet g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have ha : apow (gdet g) ((Fintype.card C : ℂ) / 2) ≠ 0 := apow_ne_zero _ _
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicSchwartzFunctionLeftGLEquivarianceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_schwartzFunction_left_GL_equivariance : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k),
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  first | exact @GlobalTheory.fFun_mul_left | exact GlobalTheory.fFun_mul_left | (intros; apply GlobalTheory.fFun_mul_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

noncomputable section
namespace GlobalTheory.OneSquareZeta
open ValuativeRel GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isPrimFrame_mul_iff {a : ℕ} {C : Type} [Fintype C] [DecidableEq C] {Λ : Submodule 𝒪[k] (C → k)}
    {X : Matrix (Fin a) C k} {g₀ : GL (Fin a) k} (h₀ : IsPrimFrame Λ (g₀.val * X)) (g : GL (Fin a) k) :
    IsPrimFrame Λ (g.val * X) ↔ g * g₀⁻¹ ∈ KO k (Fin a) := by
  rw [isPrimFrame_iff] at h₀ ⊢
  have hrow : ∀ (M : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) C k) i, (M * Y).row i = M.row i ᵥ* Y :=
    fun M Y i => by funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  have hgX : g.val * X = (g * g₀⁻¹).val * (g₀.val * X) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_assoc g.val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  have hg0X : g₀.val * X = ((g * g₀⁻¹)⁻¹).val * (g.val * X) := by
    rw [hgX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [mem_KO_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact h₀.2 ((g * g₀⁻¹).val.row i) (by rw [← hrow, ← hgX]; exact h1 i) j
    · exact h2 (((g * g₀⁻¹)⁻¹).val.row i) (by rw [← hrow, ← hg0X]; exact h₀.1 i) j
  · rintro ⟨hu1, hu2⟩
    refine ⟨fun i => ?_, fun c hc i => ?_⟩
    · show (g.val * X).row i ∈ Λ
      rw [hgX, hrow]; exact vecMul_mem_of_int h₀.1 (fun j => hu1 i j)
    · have h3 := h₀.2 (c ᵥ* (g * g₀⁻¹).val) (by rw [vecMul_vecMul, ← hgX]; exact hc)
      have hc' : c = (c ᵥ* (g * g₀⁻¹).val) ᵥ* ((g * g₀⁻¹)⁻¹).val := by
        rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
      rw [hc']
      change (∑ l, (c ᵥ* (g * g₀⁻¹).val) l * ((g * g₀⁻¹)⁻¹).val l i) ∈ 𝒪[k]
      exact Subring.sum_mem _ fun l _ => mul_mem (h3 l) (hu2 l i)

theorem fFun_mul_left {a : ℕ} {A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    [MeasurableSpace k] [BorelSpace k] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : Fin a ⊕ A' ≃ C)
    (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k) :
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  exact GlobalTheory.T.mirabolic_schwartzFunction_left_GL_equivariance k a A' C μ σ ν Ψ g h

theorem exists_primFrame {a : ℕ} {C : Type} [Fintype C] [DecidableEq C] (d : C → kˣ)
    (X : Matrix (Fin a) C k) (hX : X.rank = a) : ∃ g₀ : GL (Fin a) k, IsPrimFrame (diagLat d) (g₀.val * X) := by
  exact GlobalTheory.T.exists_GL_mul_isPrimitiveFrame_diagonalLattice k a C d X hX

theorem exists_unique_shell {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (g : GL (Fin a) k) :
    ∃! m : {m : Fin a → ℤ // Antitone m}, g ∈ shellSet ϖ m.1 := by
  obtain ⟨m, hm, x, hx, y, hy, e⟩ := GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g
  have ht : ∀ m : Fin a → ℤ, GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i :=
    fun m => Units.ext (by rw [GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])
  refine ⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩
  rintro ⟨m', hm'⟩ hmem
  obtain ⟨x', hx', y', hy', e'⟩ := mem_shellSet.1 hmem
  have E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i := by
    have h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y' := by
      rw [← ht, ← e]; exact e'
    calc _ = x'⁻¹ * (x * diagGL (fun i => ϖ ^ m i) * y) * y'⁻¹ := by group
      _ = _ := by rw [h1]; group
  have E' := congrArg Units.val E
  simp only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'
  exact Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm

variable [MeasurableSpace k] [BorelSpace k]

theorem bigF_phiA {a : ℕ} {A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ)
    (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (hϖ : IsUnif ϖ) (h : GL C k) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (phiA μ σ ν ϖ n (diagLat c) Ψ) (X0 k σ * (invT h).val) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  set X := X0 k σ * (invT h).val with hXdef
  have hΛ : latA ϖ n (diagLat c) = diagLat (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) := by
    rw [latA, dualLat_diagLat, smul_diagLat]
  have hrank : X.rank = a := by
    have := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 ⟨h, rfl⟩; simpa using this
  obtain ⟨g₀, hg₀⟩ := exists_primFrame (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) X hrank
  rw [← hΛ] at hg₀
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := exists_unique_shell hϖ g₀
  set S : Set (GL (Fin a) k) := (fun g => g * g₀⁻¹) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, phiA μ σ ν ϖ n (diagLat c) Ψ (g.val * X) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card C : ℂ) / 2) = S.indicator (fun _ => fFun μ σ ν Ψ X) g := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, phiA, if_pos ((isPrimFrame_mul_iff hg₀ g).2 hg)]
      exact fFun_mul_left μ σ ν Ψ g h
    · rw [Set.indicator_of_notMem hg, phiA, if_neg (fun h' => hg ((isPrimFrame_mul_iff hg₀ g).1 h')),
        zero_mul, zero_mul]
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν
      ((Fintype.card C : ℂ) / 2) (fun M => phiA μ σ ν ϖ n (diagLat c) Ψ (M * X)) m.1 =
      (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • fFun μ σ ν Ψ X := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => fFun μ σ ν Ψ X) hSm
    rw [e1, setIntegral_const]
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₀⁻¹ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₀⁻¹ * g₀ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₀⁻¹)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₀ = (g * g₀⁻¹)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

end GlobalTheory.OneSquareZeta


open GlobalTheory.OneSquareZeta in
theorem GlobalTheory.OneSquareZeta.bigZeta_phiA_eq_smallZeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ), IsUnif ϖ →
    bigP (haarVol (KO k (Fin a))) ϖ σ ν β (phiA μ σ ν ϖ n (diagLat c) Ψ) = smallP μ σ ν (ν * β) Ψ := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν β ϖ n c Ψ hϖ
  funext h
  rw [bigZetaIntegral_eq, bigF_phiA μ σ ν ϖ n c Ψ hϖ h, splitTheta_fFun_frameFirstBlock_mul, smallP]
  have hC : (Fintype.card C : ℂ) = a + Fintype.card A' := by
    rw [← Fintype.card_congr σ, Fintype.card_sum, Fintype.card_fin]; push_cast; ring
  have e : apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) =
      apow (gdet h) ((Fintype.card A' : ℂ) / 2) := by
    rw [← apow_add, hC]; congr 1; ring
  simp only [MonoidHom.mul_apply, Units.val_mul]
  linear_combination (β (gdet h) * ν (gdet h) * smallF μ ν Ψ (Y0 k σ * h.val) : ℂ) * e
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmallerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveFrameDatum_zetaIntegral_eq_smaller : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ), IsUnif ϖ →
    bigP (haarVol (KO k (Fin a))) ϖ σ ν β (phiA μ σ ν ϖ n (diagLat c) Ψ) = smallP μ σ ν (ν * β) Ψ := by
  first | exact @GlobalTheory.OneSquareZeta.bigZeta_phiA_eq_smallZeta | exact GlobalTheory.OneSquareZeta.bigZeta_phiA_eq_smallZeta | (intros; apply GlobalTheory.OneSquareZeta.bigZeta_phiA_eq_smallZeta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocalIsom

theorem lintegral_sq_eq_of_acts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∀ φ φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ → φ₁ ∈ GlobalTheory.WeilM.SB _ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ φ₁ →
      ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr v x _ φ φ₁ hφ hφ₁ hact μ hμ
  obtain ⟨r, K, hrm, hinv, hsch, hK, hKi, hint⟩ := GlobalTheory.T.exists_periodic_measurable_schwartz_bound (κ := Fin a' × Fin (a + a')) v
  letI mA : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  haveI : BorelSpace (Fin a' × Fin (a + a') → AF F) := ⟨rfl⟩
  have hμA : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F)) := inferInstance
  obtain ⟨C, hC0, hCt, hC⟩ := GlobalTheory.T.lintegral_normSq_componentTensor_eq_const_mul v r hrm hinv _ hμA μ hμ K hK hKi (hint _ hμA).1 (hint _ hμA).2
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil').unit
  have e := hU _ hμA (x, 1) _ (hsch φ hφ)
  rw [hact r ⟨hinv, hsch φ hφ⟩, hC φ₁ hφ₁.1.continuous hφ₁.2, hC φ hφ.1.continuous hφ.2] at e
  exact (ENNReal.mul_right_inj hC0 hCt).mp e

end GlobalTheory.LocalIsom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∀ φ φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ → φ₁ ∈ GlobalTheory.WeilM.SB _ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ φ₁ →
      ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts | exact GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts | (intros; apply GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommTensCastRSymmMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.ConjFrame

theorem comm_tensCastR_symm_map {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (σ : E →ₐ[F1] E) (τ : E →ₐ[F2] E) (hστ : ∀ x, σ x = τ x) (x : E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2) :
    Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E
        ((GlobalTheory.StdFrame.tensCastR h).symm (Algebra.TensorProduct.map τ (AlgHom.id F2 (FiniteAdeleRing (𝓞 F2) F2)) x)) =
      Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F1) F1)
        (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E ((GlobalTheory.StdFrame.tensCastR h).symm x)) := by
  subst h
  have hc : ∀ y, (GlobalTheory.StdFrame.tensCastR (rfl : F1 = F1)).symm y =
      (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).symm y := fun _ => rfl
  simp only [hc]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, hστ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem swapAE_conjAL : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) (x : ReciprocityTheory.Aut.AL D.host.E), Formalism.IndefR.Lev.swapAE D ((GlobalTheory.StdFrame.tensCastR hF).symm (ReciprocityTheory.Aut.conjAL D.host.E x)) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.IndefR.Lev.swapAE D ((GlobalTheory.StdFrame.tensCastR hF).symm x)) := by
  intro D hF x
  exact comm_tensCastR_symm_map hF D.sp.cm.sig ((IsCMField.complexConj D.host.E).toAlgHom) (fun _ => rfl) x

end GlobalTheory.ConjFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFr
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.CuspCocpt
open GlobalTheory.StdPar GlobalTheory.Cusp

theorem cocompact_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X S) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S
  by_cases hS0 : S = ∅
  · subst hS0
    rw [unip_empty]
    refine ⟨Set.univ, ?_, fun u => ⟨1, Subgroup.one_mem _, Set.mem_univ _⟩⟩
    exact Set.Subsingleton.isCompact fun a _ b _ => Subsingleton.elim a b
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hσ := sigma_sigma h
  have hs : m.val + 1 ≤ r := m.2
  have hS : ∀ i : Fin r, i.val < m.val + 1 ↔ ∃ k ∈ S, i ≤ k := fun i =>
    ⟨fun hi => ⟨m, hm, Fin.le_def.2 (Nat.lt_succ_iff.1 hi)⟩,
      fun ⟨k, hk, hik⟩ => Nat.lt_succ_iff.2 (le_trans (Fin.le_def.1 hik) (Fin.le_def.1 (hm' k hk)))⟩
  have e := (GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (m.val + 1) hs hS
    (fun i => (S.filter (· < Fin.castLE hs i)).card) fun _ => rfl).1
  have hC : IsIsoCols σ J (X.submatrix id (Fin.castLE hs)) := isIsoCols_of_isWittFrame hW hσ hJ hs
  exact e ▸ cocompact_unipFlag hJ hσ hC _

end GlobalTheory.CuspCocpt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFrStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X S) := by
  first | exact @GlobalTheory.CuspCocpt.cocompact_unip | exact GlobalTheory.CuspCocpt.cocompact_unip | (intros; apply GlobalTheory.CuspCocpt.cocompact_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnitary
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacKInf.LeviFix

variable {D : D7}

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_adj' {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (x : Mx D m n) :
    compAt θ τ (adj x) = (compAt θ τ x)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.FockCompare.comp_cA hθ τ]
  rfl

end GlobalTheory.VacKInf.LeviFix

namespace GlobalTheory.VacKInf

end GlobalTheory.VacKInf
end
end

/-
Taxes et contributions patronales annexes :
- formation professionnelle et taxe d'apprentissage (recouvrées par l'Urssaf) ;
- contribution supplémentaire à l'apprentissage (barème paramétrable) ;
- effort construction PEEC (≥ 50 salariés) ;
- versement mobilité (taux de l'AOM) ;
- contribution CPF-CDD (1 %, tranche 1) ;
- forfait social sur les rémunérations > 10 PASS ;
- taxe sur les salaires (DGFiP, barème annuel 2026) ;
- contribution annuelle OETH (DOETH), montant paramétré.
-/
import Cotisations.Assiette
import Cotisations.Organismes
import Cotisations.Parametres

namespace Cotisations

/-- Formation professionnelle : 1,00 % (≥ 11 salariés) ou 0,55 %. -/
def formationProfessionnelle (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : LigneCotisation :=
  let taux := if pe.effectif ≥ 11 then pa.tauxFormationProGrand else pa.tauxFormationProPetit
  { nom := "Contribution formation professionnelle"
    organisme := .urssaf, nature := .taxe, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := taux * ps.assietteSecu }

/-- Taxe d'apprentissage (effectif ≥ 11) : 0,59 % + 0,09 % de solde ;
    Alsace-Moselle : 0,44 %, solde néant. -/
def taxeApprentissage (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : LigneCotisation :=
  let taux :=
    if pe.effectif < 11 then 0
    else if pe.region == .alsaceMoselle then pa.tauxTaxeApprentissageAlsaceMoselle
    else pa.tauxTaxeApprentissagePrincipale + pa.tauxTaxeApprentissageSolde
  { nom := "Taxe d'apprentissage"
    organisme := .urssaf, nature := .taxe, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := taux * ps.assietteSecu }

/-- Contribution supplémentaire à l'apprentissage (barème selon le ratio
    d'alternants, taux fourni en paramètre d'entreprise). -/
def csaApprentissage (pe : ParametresEntreprise) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Contribution supplémentaire à l'apprentissage"
    organisme := .urssaf, nature := .taxe, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := pe.tauxCSAApprentissage * ps.assietteSecu
    commentaire := "Barème selon effectif (≥ 250) et ratio d'alternants" }

/-- Participation à l'effort de construction (PEEC) : 0,45 %, employeurs
    d'au moins 50 salariés. -/
def effortConstruction (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Participation à l'effort de construction (PEEC)"
    organisme := .urssaf, nature := .taxe, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale :=
      if pe.sujetPEEC && pe.effectif ≥ 50 then pa.tauxPEEC * ps.assietteSecu else 0 }

/-- Versement mobilité : taux fixé par l'autorité organisatrice de la
    mobilité (employeurs d'au moins 11 salariés dans le périmètre). -/
def versementMobilite (pe : ParametresEntreprise) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Versement mobilité"
    organisme := .urssaf, nature := .taxe, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := pe.tauxVersementMobilite * ps.assietteSecu }

/-- Contribution CPF-CDD : 1 % sur la tranche 1 pour les CDD
    (sauf usage et certains cas) — recouvrée via la DSN. -/
def contributionCpfCdd (pa : ParametresAnnee) (ps : ParametresSalarie)
    (t : Tranches) : LigneCotisation :=
  let eligible := ps.contrat == .cddStandard
  { nom := "Contribution CPF-CDD"
    organisme := .urssaf, nature := .taxe, cote := .patronale
    assiette := t.tranche1
    partPatronale := if eligible then pa.tauxCpfCdd * t.tranche1 else 0
    commentaire := "Recouvrée par l'Urssaf pour le compte de France Travail" }

/-- Forfait social sur la fraction des rémunérations excédant 10 PASS :
    20 % (effectif < 250) ou 30 %. -/
def forfaitSocial (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (plafond : Eur) : LigneCotisation :=
  let seuil := pa.fsSeuilPass * plafond
  let base := max 0 (ps.assietteSecu - seuil)
  let taux := if pe.effectif ≥ pa.fsSeuilEffectifGrand then pa.fsTauxGrand else pa.fsTauxPetit
  { nom := "Forfait social (rémunérations > 10 PASS)"
    organisme := .urssaf, nature := .contribution, cote := .patronale
    assiette := base
    partPatronale := taux * base }

/-- Taxe sur les salaires : barème annuel progressif par salarié
    (4,25 % / 8,50 % / 13,60 %, seuils 9 229 € et 18 423 € en 2026),
    avec franchise (1 200 €) et décote, et abattement de 24 256 € pour
    les associations. -/
def taxeSurSalairesSalarie (pa : ParametresAnnee) (estAssociation : Bool)
    (salaireAnnuel : Eur) : Eur :=
  let t1 := min salaireAnnuel pa.tsSeuil1
  let t2 := max 0 (min salaireAnnuel pa.tsSeuil2 - pa.tsSeuil1)
  let t3 := max 0 (salaireAnnuel - pa.tsSeuil2)
  let brute := pa.tsTaux1 * t1 + pa.tsTaux2 * t2 + pa.tsTaux3 * t3
  let abattue := if estAssociation then max 0 (brute - pa.tsAbattementAssociation) else brute
  let denomDecote := pa.tsSeuilDecote - pa.tsFranchise
  if abattue ≤ pa.tsFranchise then 0
  else if abattue ≤ pa.tsSeuilDecote then
    abattue - abattue * (pa.tsSeuilDecote - abattue) / denomDecote
  else abattue

/-- Ligne mensualisée de taxe sur les salaires (montant annuel / 12). -/
def taxeSurSalaires (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : LigneCotisation :=
  let annuelle := taxeSurSalairesSalarie pa pe.estAssociation
    ((12 : Rat) * ps.assietteSecu)
  { nom := "Taxe sur les salaires"
    organisme := .dgfip, nature := .taxe, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := annuelle / 12
    commentaire := "Barème annuel 2026, payée à la DGFiP" }

/-- Contribution annuelle OETH (DOETH), montant annuel calculé par
    ailleurs, mensualisé ici. -/
def contributionOETH (pe : ParametresEntreprise) : LigneCotisation :=
  { nom := "Contribution annuelle OETH (DOETH)"
    organisme := .urssaf, nature := .contribution, cote := .patronale
    assiette := 0
    partPatronale := pe.contributionOETHAnnuelle / 12
    commentaire := "Montant annuel calculé selon les points d'obligation d'emploi" }

/-- Toutes les lignes patronales de taxes annexes. -/
def lignesTaxesPatronales (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (t : Tranches) (plafond : Eur) : List LigneCotisation :=
  [formationProfessionnelle pa pe ps, taxeApprentissage pa pe ps,
   csaApprentissage pe ps, effortConstruction pa pe ps,
   versementMobilite pe ps, contributionCpfCdd pa ps t,
   forfaitSocial pa pe ps plafond]
  ++ (if pe.assujettiTaxeSalaires then [taxeSurSalaires pa pe ps] else [])
  ++ (if pe.contributionOETHAnnuelle > 0 then [contributionOETH pe] else [])

end Cotisations
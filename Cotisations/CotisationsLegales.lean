/-
Cotisations et contributions légales du régime général (recouvrées par
l'Urssaf via la DSN), parts salariale et patronale.

Taux = droit applicable en 2026 (Urssaf, « Taux de cotisations – Secteur
privé », 01/01/2026). Tous les taux restent paramétrables.

Toutes les lignes sont construites avec les primitives communes
`ligneTauxUnique` et `ligneMixte` (module `Organismes`) : une seule
définition de la mécanique « taux × assiette ».
-/
import Cotisations.Assiette
import Cotisations.Organismes
import Cotisations.Parametres

namespace Cotisations

/-! ### Parts salariales -/

/-- Ligne de vieillesse (plafonnée ou déplafonnée) pour une cote donnée :
    même assiette, même mécanique, seul le taux et la cote varient. -/
def ligneVieillesse (nom : String) (salariale : Bool) (taux : Taux)
    (assiette : Eur) : LigneCotisation :=
  ligneTauxUnique nom .urssaf .cotisation salariale assiette (taux * assiette)

/-- Assurance vieillesse plafonnée (tranche 1) — salarié : 6,90 % en 2026. -/
def vieillesseSalarialeT1 (pa : ParametresAnnee) (t : Tranches) : LigneCotisation :=
  ligneVieillesse "Assurance vieillesse plafonnée — salarié" true
    pa.tauxVieillesseSalarialPlafonne t.tranche1

/-- Assurance vieillesse déplafonnée — salarié : 0,40 % sur la totalité. -/
def vieillesseSalarialeDeplafonnee (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  ligneVieillesse "Assurance vieillesse déplafonnée — salarié" true
    pa.tauxVieillesseSalarialDeplafonne ps.assietteSecu

/-- Régime local d'assurance maladie d'Alsace-Moselle — salarié : 1,30 %. -/
def maladieAlsaceMoselleSalariale (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  let a := ps.assietteSecu
  ligneTauxUnique "Régime local Alsace-Moselle — maladie, salarié" .urssaf .cotisation true
    a (pa.tauxMaladieAlsaceMoselleSalarie * a)

/-- Ligne CSG/CRDS : part salariale d'un taux appliqué à l'assiette
    commune de 98,25 % du brut (abattement heures supplémentaires inclus). -/
def ligneCsgCrds (pa : ParametresAnnee) (ps : ParametresSalarie) (nom : String)
    (nature : NatureCotisation) (taux : Taux) : LigneCotisation :=
  let a := assietteCSGSalariale pa ps
  ligneTauxUnique nom .urssaf nature true a (taux * a)

/-- CSG déductible (régime réel) : 6,80 % sur 98,25 % du brut. -/
def csgDeductible (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  ligneCsgCrds pa ps "CSG déductible" .contribution pa.tauxCsgDeductible

/-- CSG non déductible (imposable) : 2,40 % sur 98,25 % du brut. -/
def csgNonDeductible (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  ligneCsgCrds pa ps "CSG non déductible" .contribution pa.tauxCsgNonDeductible

/-- CSG unique non déductible pour les employeurs au forfait
    (la CSG n'est alors pas déductible : 9,20 %). -/
def csgForfaitaire (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  ligneCsgCrds pa ps "CSG (non déductible, régime forfaitaire)" .contribution
    (pa.tauxCsgDeductible + pa.tauxCsgNonDeductible)

/-- CRDS : 0,50 % sur 98,25 % du brut. -/
def crds (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  ligneCsgCrds pa ps "CRDS" .contribution pa.tauxCrds

/-- Lignes salariales de sécurité sociale d'un salarié. -/
def lignesSecuSalariales (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (t : Tranches) : List LigneCotisation :=
  [vieillesseSalarialeT1 pa t, vieillesseSalarialeDeplafonnee pa ps]
  ++ (if pe.region == .alsaceMoselle then [maladieAlsaceMoselleSalariale pa ps] else [])
  ++ (if pe.regimeReel then [csgDeductible pa ps, csgNonDeductible pa ps]
      else [csgForfaitaire pa ps])
  ++ [crds pa ps]

/-! ### Parts patronales -/

/-- Ligne patronale Urssaf : taux unique appliqué à une assiette. -/
def lignePatronaleUrssaf (nom : String) (nature : NatureCotisation)
    (taux : Taux) (assiette : Eur) (commentaire : String := "") : LigneCotisation :=
  ligneTauxUnique nom .urssaf nature false assiette (taux * assiette) commentaire

/-- Maladie, maternité, invalidité, décès : 13 % sur la totalité. -/
def maladiePatronale (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  lignePatronaleUrssaf "Maladie, maternité, invalidité, décès" .cotisation
    pa.tauxMaladie ps.assietteSecu

/-- Contribution solidarité autonomie : 0,30 %. -/
def csaPatronale (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  lignePatronaleUrssaf "Contribution solidarité autonomie (CSA)" .contribution
    pa.tauxCsa ps.assietteSecu

/-- Assurance vieillesse plafonnée (T1) : 8,55 %, et déplafonnée :
    2,11 % en 2026. -/
def vieillessePatronale (pa : ParametresAnnee) (ps : ParametresSalarie)
    (t : Tranches) : List LigneCotisation :=
  [ ligneVieillesse "Assurance vieillesse plafonnée — employeur" false
      pa.tauxVieillessePatronalPlafonne t.tranche1,
    ligneVieillesse "Assurance vieillesse déplafonnée — employeur" false
      pa.tauxVieillessePatronalDeplafonne ps.assietteSecu ]

/-- Allocations familiales : 5,25 %, ou 3,45 % si la masse salariale
    annuelle reste sous 250 % du SMIC. -/
def famillePatronale (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : LigneCotisation :=
  lignePatronaleUrssaf "Allocations familiales" .cotisation (pe.tauxFamille pa) ps.assietteSecu

/-- FNAL : 0,10 % sur la tranche 1 (effectif < 50) ou 0,50 % sur la
    totalité (effectif ≥ 50). -/
def fnalPatronal (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (t : Tranches) : LigneCotisation :=
  if pe.effectif ≥ 50 then
    lignePatronaleUrssaf "FNAL (0,50 %, totalité)" .contribution
      pa.tauxFnalTotalite ps.assietteSecu
  else
    lignePatronaleUrssaf "FNAL (0,10 %, tranche 1)" .contribution
      pa.tauxFnalPlafonne t.tranche1

/-- Assurance chômage : 4,00 % (2026), plafonnée à 4 PASS. -/
def chomagePatronal (pa : ParametresAnnee) (ps : ParametresSalarie)
    (plafond : Eur) : LigneCotisation :=
  let a := assietteQuatrePlafonds ps.assietteSecu plafond
  ligneTauxUnique "Assurance chômage" .urssaf .cotisation false a
    (if ps.assujettiChomage then pa.tauxChomage * a else 0)

/-- AGS (garantie des salaires) : 0,25 % plafonné à 4 PASS ;
    0,03 % pour le travail temporaire. -/
def agsPatronale (pa : ParametresAnnee) (ps : ParametresSalarie)
    (plafond : Eur) : LigneCotisation :=
  let a := assietteQuatrePlafonds ps.assietteSecu plafond
  let taux := if ps.contrat == .interimaire then pa.tauxAgsInterimaire else pa.tauxAgs
  ligneTauxUnique "AGS — garantie des salaires" .urssaf .cotisation false a (taux * a)

/-- Contribution au dialogue social : 0,016 % (effectif ≥ 11). -/
def dialogueSocialPatronale (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : LigneCotisation :=
  ligneTauxUnique "Contribution au dialogue social" .urssaf .contribution false
    ps.assietteSecu (if pe.effectif ≥ 11 then pa.tauxDialogueSocial * ps.assietteSecu else 0)

/-- Accidents du travail et maladies professionnelles : taux notifié
    par la Carsat (partie mutualisée plafonnée à 0,49 % en 2026). -/
def atmpPatronale (pe : ParametresEntreprise) (ps : ParametresSalarie) : LigneCotisation :=
  ligneTauxUnique "Accidents du travail et maladies professionnelles" .carsat .cotisation false
    ps.assietteSecu (pe.tauxATMP * ps.assietteSecu)
    "Taux net notifié par la Carsat/Cramif"

/-- Toutes les lignes patronales de sécurité sociale (hors retraite
    complémentaire, hors taxes du module `Taxes`). -/
def lignesSecuPatronales (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (t : Tranches) (plafond : Eur) : List LigneCotisation :=
  [maladiePatronale pa ps, csaPatronale pa ps]
  ++ vieillessePatronale pa ps t
  ++ [famillePatronale pa pe ps, fnalPatronal pa pe ps t,
      chomagePatronal pa ps plafond, agsPatronale pa ps plafond,
      dialogueSocialPatronale pa pe ps, atmpPatronale pe ps]

end Cotisations

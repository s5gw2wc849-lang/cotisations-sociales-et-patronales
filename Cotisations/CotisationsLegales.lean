/-
Cotisations et contributions légales du régime général (recouvrées par
l'Urssaf via la DSN), parts salariale et patronale.

Taux = droit applicable en 2026 (Urssaf, « Taux de cotisations – Secteur
privé », 01/01/2026). Tous les taux restent paramétrables.
-/
import Cotisations.Assiette
import Cotisations.Organismes
import Cotisations.Parametres

namespace Cotisations

/-! ### Parts salariales -/

/-- Assurance vieillesse plafonnée (tranche 1) — salarié : 6,90 % en 2026. -/
def vieillesseSalarialeT1 (pa : ParametresAnnee) (t : Tranches) : LigneCotisation :=
  { nom := "Assurance vieillesse plafonnée — salarié"
    organisme := .urssaf, nature := .cotisation, cote := .salariale
    assiette := t.tranche1
    partSalariale := pa.tauxVieillesseSalarialPlafonne * t.tranche1 }

/-- Assurance vieillesse déplafonnée — salarié : 0,40 % sur la totalité. -/
def vieillesseSalarialeDeplafonnee (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Assurance vieillesse déplafonnée — salarié"
    organisme := .urssaf, nature := .cotisation, cote := .salariale
    assiette := ps.assietteSecu
    partSalariale := pa.tauxVieillesseSalarialDeplafonne * ps.assietteSecu }

/-- Régime local d'assurance maladie d'Alsace-Moselle — salarié : 1,30 %. -/
def maladieAlsaceMoselleSalariale (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Régime local Alsace-Moselle — maladie, salarié"
    organisme := .urssaf, nature := .cotisation, cote := .salariale
    assiette := ps.assietteSecu
    partSalariale := pa.tauxMaladieAlsaceMoselleSalarie * ps.assietteSecu }

/-- CSG déductible (régime réel) : 6,80 % sur 98,25 % du brut
    (abattement heures supplémentaires inclus). -/
def csgDeductible (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "CSG déductible"
    organisme := .urssaf, nature := .contribution, cote := .salariale
    assiette := assietteCSGSalariale pa ps
    partSalariale := pa.tauxCsgDeductible * assietteCSGSalariale pa ps }

/-- CSG non déductible (imposable) : 2,40 % sur 98,25 % du brut. -/
def csgNonDeductible (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "CSG non déductible"
    organisme := .urssaf, nature := .contribution, cote := .salariale
    assiette := assietteCSGSalariale pa ps
    partSalariale := pa.tauxCsgNonDeductible * assietteCSGSalariale pa ps }

/-- CSG unique non déductible pour les employeurs au forfait
    (la CSG n'est alors pas déductible : 9,20 %). -/
def csgForfaitaire (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "CSG (non déductible, régime forfaitaire)"
    organisme := .urssaf, nature := .contribution, cote := .salariale
    assiette := assietteCSGSalariale pa ps
    partSalariale := (pa.tauxCsgDeductible + pa.tauxCsgNonDeductible) * assietteCSGSalariale pa ps }

/-- CRDS : 0,50 % sur 98,25 % du brut. -/
def crds (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "CRDS"
    organisme := .urssaf, nature := .contribution, cote := .salariale
    assiette := assietteCSGSalariale pa ps
    partSalariale := pa.tauxCrds * assietteCSGSalariale pa ps }

/-- Lignes salariales de sécurité sociale d'un salarié. -/
def lignesSecuSalariales (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (t : Tranches) : List LigneCotisation :=
  [vieillesseSalarialeT1 pa t, vieillesseSalarialeDeplafonnee pa ps]
  ++ (if pe.region == .alsaceMoselle then [maladieAlsaceMoselleSalariale pa ps] else [])
  ++ (if pe.regimeReel then [csgDeductible pa ps, csgNonDeductible pa ps]
      else [csgForfaitaire pa ps])
  ++ [crds pa ps]

/-! ### Parts patronales -/

/-- Maladie, maternité, invalidité, décès : 13 % sur la totalité. -/
def maladiePatronale (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Maladie, maternité, invalidité, décès"
    organisme := .urssaf, nature := .cotisation, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := pa.tauxMaladie * ps.assietteSecu }

/-- Contribution solidarité autonomie : 0,30 %. -/
def csaPatronale (pa : ParametresAnnee) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Contribution solidarité autonomie (CSA)"
    organisme := .urssaf, nature := .contribution, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := pa.tauxCsa * ps.assietteSecu }

/-- Assurance vieillesse plafonnée (T1) : 8,55 %, et déplafonnée :
    2,11 % en 2026. -/
def vieillessePatronale (pa : ParametresAnnee) (ps : ParametresSalarie)
    (t : Tranches) : List LigneCotisation :=
  [ ({ nom := "Assurance vieillesse plafonnée — employeur"
       organisme := .urssaf, nature := .cotisation, cote := .patronale
       assiette := t.tranche1
       partPatronale := pa.tauxVieillessePatronalPlafonne * t.tranche1 } : LigneCotisation),
    ({ nom := "Assurance vieillesse déplafonnée — employeur"
       organisme := .urssaf, nature := .cotisation, cote := .patronale
       assiette := ps.assietteSecu
       partPatronale := pa.tauxVieillessePatronalDeplafonne * ps.assietteSecu } : LigneCotisation) ]

/-- Allocations familiales : 5,25 %, ou 3,45 % si la masse salariale
    annuelle reste sous 250 % du SMIC. -/
def famillePatronale (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Allocations familiales"
    organisme := .urssaf, nature := .cotisation, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := pe.tauxFamille pa * ps.assietteSecu }

/-- FNAL : 0,10 % sur la tranche 1 (effectif < 50) ou 0,50 % sur la
    totalité (effectif ≥ 50). -/
def fnalPatronal (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (t : Tranches) : LigneCotisation :=
  if pe.effectif ≥ 50 then
    { nom := "FNAL (0,50 %, totalité)"
      organisme := .urssaf, nature := .contribution, cote := .patronale
      assiette := ps.assietteSecu
      partPatronale := pa.tauxFnalTotalite * ps.assietteSecu }
  else
    { nom := "FNAL (0,10 %, tranche 1)"
      organisme := .urssaf, nature := .contribution, cote := .patronale
      assiette := t.tranche1
      partPatronale := pa.tauxFnalPlafonne * t.tranche1 }

/-- Assurance chômage : 4,00 % (2026), plafonnée à 4 PASS. -/
def chomagePatronal (pa : ParametresAnnee) (ps : ParametresSalarie)
    (plafond : Eur) : LigneCotisation :=
  let assiette := assietteQuatrePlafonds ps.assietteSecu plafond
  { nom := "Assurance chômage"
    organisme := .urssaf, nature := .cotisation, cote := .patronale
    assiette := assiette
    partPatronale := if ps.assujettiChomage then pa.tauxChomage * assiette else 0 }

/-- AGS (garantie des salaires) : 0,25 % plafonné à 4 PASS ;
    0,03 % pour le travail temporaire. -/
def agsPatronale (pa : ParametresAnnee) (ps : ParametresSalarie)
    (plafond : Eur) : LigneCotisation :=
  let assiette := assietteQuatrePlafonds ps.assietteSecu plafond
  let taux := if ps.contrat == .interimaire then pa.tauxAgsInterimaire else pa.tauxAgs
  { nom := "AGS — garantie des salaires"
    organisme := .urssaf, nature := .cotisation, cote := .patronale
    assiette := assiette
    partPatronale := taux * assiette }

/-- Contribution au dialogue social : 0,016 % (effectif ≥ 11). -/
def dialogueSocialPatronale (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Contribution au dialogue social"
    organisme := .urssaf, nature := .contribution, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := if pe.effectif ≥ 11 then pa.tauxDialogueSocial * ps.assietteSecu else 0 }

/-- Accidents du travail et maladies professionnelles : taux notifié
    par la Carsat (partie mutualisée plafonnée à 0,49 % en 2026). -/
def atmpPatronale (pe : ParametresEntreprise) (ps : ParametresSalarie) : LigneCotisation :=
  { nom := "Accidents du travail et maladies professionnelles"
    organisme := .carsat, nature := .cotisation, cote := .patronale
    assiette := ps.assietteSecu
    partPatronale := pe.tauxATMP * ps.assietteSecu
    commentaire := "Taux net notifié par la Carsat/Cramif" }

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
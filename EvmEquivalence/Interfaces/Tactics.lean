/-
This file contains tactics to agilize and compress certain repetitive proofs
 -/

import EvmEquivalence.KEVM2Lean.Func

-- Tactics to perform lengthy simps for schedule
syntax "simp_schedule1"     : tactic
syntax "simp_schedule2"     : tactic

-- The reason for having separate simps is that otherwise
-- Lean performs too many operations at once
macro_rules
| `(tactic| simp_schedule1) =>
    `(tactic| simp [«_<_>_SCHEDULE_Int_ScheduleConst_Schedule»];
              simp [SCHEDULE_GaccesslistaddressBer];
              simp [SCHEDULE_GaccesslistaddressDef];
              simp [SCHEDULE_GaccessliststoragekeyBer];
              simp [SCHEDULE_GaccessliststoragekeyDef];
              simp [SCHEDULE_GbalanceDef];
              simp [SCHEDULE_GbalanceIst];
              simp [SCHEDULE_GbalanceTang];
              simp [SCHEDULE_GbaseDef];
              simp [SCHEDULE_GblockhashDef];
              simp [SCHEDULE_GcallDef];
              simp [SCHEDULE_GcallTang];
              simp [SCHEDULE_GcallstipendDef];
              simp [SCHEDULE_GcallvalueDef];
              simp [SCHEDULE_GcodedepositDef];
              simp [SCHEDULE_GcoldaccountaccessBer];
              simp [SCHEDULE_GcoldaccountaccessDef];
              simp [SCHEDULE_GcoldsloadBer];
              simp [SCHEDULE_GcoldsloadDef];
              simp [SCHEDULE_GcopyDef];
              simp [SCHEDULE_GcreateDef];
              simp [SCHEDULE_GecaddDef];
              simp [SCHEDULE_GecaddIst];
              simp [SCHEDULE_GecmulDef];
              simp [SCHEDULE_GecmulIst];
              simp [SCHEDULE_GecpaircoeffDef];
              simp [SCHEDULE_GecpaircoeffIst];
              simp [SCHEDULE_GecpairconstDef];
              simp [SCHEDULE_GecpairconstIst];
              simp [SCHEDULE_GexpDef];
              simp [SCHEDULE_GexpbyteDef];
              simp [SCHEDULE_GexpbyteDrag];
              simp [SCHEDULE_GextcodecopyTang];
              simp [SCHEDULE_GextcodesizeDef];
              simp [SCHEDULE_GextcodesizeTang];
              simp [SCHEDULE_GfroundDef];
              simp [SCHEDULE_GhighDef];
              simp [SCHEDULE_GinitcodewordcostDef];
              simp [SCHEDULE_GinitcodewordcostShang];
              simp [SCHEDULE_GjumpdestDef];
              simp [SCHEDULE_GlogDef];
              simp [SCHEDULE_GlogdataDef];
              simp [SCHEDULE_GlogtopicDef];
              simp [SCHEDULE_GlowDef];
              simp [SCHEDULE_GmemoryDef];
              simp [SCHEDULE_GmidDef];
              simp [SCHEDULE_GnewaccountDef];
              simp [SCHEDULE_GquadcoeffDef];
              simp [SCHEDULE_GquaddivisorBer];
              simp [SCHEDULE_GquaddivisorDef];
              simp [SCHEDULE_GselfdestructDef];
              simp [SCHEDULE_GselfdestructTang];
              simp [SCHEDULE_Gsha3Def];
              simp [SCHEDULE_Gsha3wordDef];
              (try simp [SCHEDULE_GsloadBer]);
              simp [SCHEDULE_GsloadDef];
              simp [SCHEDULE_GsloadIst];
              simp [SCHEDULE_GsloadTang];
              (try simp [SCHEDULE_GsstoreresetBer]);
              simp [SCHEDULE_GsstoreresetDef];
              simp [SCHEDULE_GsstoresetDef];
              simp [SCHEDULE_GtransactionDef];
              simp [SCHEDULE_GtxcreateDef];
              simp [SCHEDULE_GtxcreateFront];
              simp [SCHEDULE_GtxdatanonzeroDef];
              simp [SCHEDULE_GtxdatanonzeroIst];
              simp [SCHEDULE_GtxdatazeroDef];
              simp [SCHEDULE_GverylowDef])

-- Depending on the proofs, the rewrites finish sooner than others
-- Hence the pervasiveness of `try` in this tactic
macro_rules
| `(tactic| simp_schedule2) =>
    `(tactic| (try simp [SCHEDULE_GwarmstoragedirtystoreCanc]);
              (try simp [SCHEDULE_GwarmstoragedirtystoreDef]);
              (try simp [SCHEDULE_GwarmstoragereadBer]);
              (try simp [SCHEDULE_GwarmstoragereadDef]);
              (try simp [SCHEDULE_GzeroDef]);
              (try simp [SCHEDULE_RbByz]);
              (try simp [SCHEDULE_RbConst]);
              (try simp [SCHEDULE_RbDef]);
              (try simp [SCHEDULE_RbMerg]);
              (try simp [SCHEDULE_Rmaxquotient]);
              (try simp [SCHEDULE_RmaxquotientLond]);
              (try simp [SCHEDULE_RselfdestructDef]);
              (try simp [SCHEDULE_RselfdestructLond]);
              (try simp [SCHEDULE_RsstoreclearDef]);
              (try simp [SCHEDULE_RsstoreclearLond]);
              (try simp [SCHEDULE_SCHEDCONSTBer]);
              (try simp [SCHEDULE_SCHEDCONSTByz]);
              (try simp [SCHEDULE_SCHEDCONSTCanc]);
              (try simp [SCHEDULE_SCHEDCONSTConst]);
              (try simp [SCHEDULE_SCHEDCONSTDrag1]);
              (try simp [SCHEDULE_SCHEDCONSTFront]);
              (try simp [SCHEDULE_SCHEDCONSTHome]);
              (try simp [SCHEDULE_SCHEDCONSTIst]);
              (try simp [SCHEDULE_SCHEDCONSTLond]);
              (try simp [SCHEDULE_SCHEDCONSTMerg]);
              (try simp [SCHEDULE_SCHEDCONSTPete]);
              (try simp [SCHEDULE_SCHEDCONSTShang]);
              (try simp [SCHEDULE_SCHEDCONSTTang1]);
              (try simp [SCHEDULE_maxCodeSizeDef]);
              (try simp [SCHEDULE_maxCodeSizeDrag]);
              (try simp [SCHEDULE_maxInitCodeSizeDef]);
              (try simp [SCHEDULE_maxInitCodeSizeShang]);
              try simp [_fc2d477])

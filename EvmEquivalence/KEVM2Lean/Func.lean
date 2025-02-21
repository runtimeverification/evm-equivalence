import EvmEquivalence.KEVM2Lean.Inj
import EvmEquivalence.KEVM2Lean.ScheduleOrdering

def SCHEDULE_GzeroDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gzero_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def _5b9db8d : SortBool → SortBool → Option SortBool
  | true, B => some B
  | _, _ => none

def _61fbef3 : SortBool → SortBool → Option SortBool
  | false, _Gen0 => some false
  | _, _ => none

def SCHEDULE_GsloadTang : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 200
  | _, _ => none

axiom «.Map» : Option SortMap

def SCHEDULE_GverylowDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 3
  | _, _ => none

def SCHEDULE_GbaseDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbase_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 2
  | _, _ => none

def SCHEDULE_GtxdatanonzeroDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxdatanonzero_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 68
  | _, _ => none

def SCHEDULE_GbalanceIst : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 700
  | _, _ => none

axiom «_==K_» (x0 : SortK) (x1 : SortK) : Option SortBool

def SCHEDULE_GecaddDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecadd_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 500
  | _, _ => none

def SCHEDULE_GecpairconstIst : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpairconst_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 45000
  | _, _ => none

def _7174452 : SortBool → SortBool → Option SortBool
  | true, _Gen0 => some true
  | _, _ => none

def SCHEDULE_GecpaircoeffIst : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpaircoeff_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 34000
  | _, _ => none

def SCHEDULE_RselfdestructDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 24000
  | _, _ => none

def SCHEDULE_RbMerg : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.MERGE_EVM => some 0
  | _, _ => none

def SCHEDULE_GlogdataDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glogdata_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 8
  | _, _ => none

def SCHEDULE_Gsha3Def : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsha3_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 30
  | _, _ => none

def SCHEDULE_GinitcodewordcostDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Ginitcodewordcost_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GcoldaccountaccessBer : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldaccountaccess_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 2600
  | _, _ => none

def SCHEDULE_GcoldsloadBer : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 2100
  | _, _ => none

def SCHEDULE_GextcodesizeTang : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodesize_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 700
  | _, _ => none

def SCHEDULE_GquaddivisorBer : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gquaddivisor_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 3
  | _, _ => none

def SCHEDULE_GcallstipendDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcallstipend_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 2300
  | _, _ => none

def SCHEDULE_maxCodeSizeDrag : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst, SortSchedule.SPURIOUS_DRAGON_EVM => some 24576
  | _, _ => none

def SCHEDULE_GblockhashDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gblockhash_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GextcodesizeDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodesize_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GsstoreresetDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 5000
  | _, _ => none

def SCHEDULE_GcoldaccountaccessDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldaccountaccess_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GbalanceTang : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 400
  | _, _ => none

def SCHEDULE_GlogDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glog_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 375
  | _, _ => none

def _17ebc68 : SortBool → Option SortBool
  | false => some true
  | _ => none

def SCHEDULE_Rmaxquotient : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rmaxquotient_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 2
  | _, _ => none

def SCHEDULE_GnewaccountDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gnewaccount_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 25000
  | _, _ => none

def SCHEDULE_RmaxquotientLond : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rmaxquotient_SCHEDULE_ScheduleConst, SortSchedule.LONDON_EVM => some 5
  | _, _ => none

def SCHEDULE_RsstoreclearDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 15000
  | _, _ => none

def SCHEDULE_GtxdatazeroDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxdatazero_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 4
  | _, _ => none

def _991a329 : SortBool → SortBool → Option SortBool
  | false, B => some B
  | _, _ => none

def SCHEDULE_GecpaircoeffDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpaircoeff_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 80000
  | _, _ => none

def _fc2d477 : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodecopy_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GtxcreateDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxcreate_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 53000
  | _, _ => none

def SCHEDULE_GlogtopicDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glogtopic_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 375
  | _, _ => none

def SCHEDULE_RbDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 5000000000000000000
  | _, _ => none

def SCHEDULE_GexpbyteDrag : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst, SortSchedule.SPURIOUS_DRAGON_EVM => some 50
  | _, _ => none

def SCHEDULE_GecmulIst : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecmul_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 6000
  | _, _ => none

def SCHEDULE_GmemoryDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gmemory_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 3
  | _, _ => none

def SCHEDULE_GcoldsloadDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GtransactionDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtransaction_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 21000
  | _, _ => none

def SCHEDULE_GlowDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glow_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 5
  | _, _ => none

def SCHEDULE_GaccessliststoragekeyDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GcodedepositDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcodedeposit_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 200
  | _, _ => none

def SCHEDULE_GmidDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gmid_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 8
  | _, _ => none

def SCHEDULE_GcallDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcall_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 40
  | _, _ => none

def SCHEDULE_GsstoresetDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsstoreset_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20000
  | _, _ => none

def SCHEDULE_Gsha3wordDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsha3word_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 6
  | _, _ => none

def SCHEDULE_GexpbyteDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 10
  | _, _ => none

def SCHEDULE_GecmulDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecmul_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 40000
  | _, _ => none

def SCHEDULE_maxInitCodeSizeDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.maxInitCodeSize_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GtxcreateFront : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxcreate_SCHEDULE_ScheduleConst, SortSchedule.FRONTIER_EVM => some 21000
  | _, _ => none

def SCHEDULE_GextcodecopyTang : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodecopy_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 700
  | _, _ => none

def SCHEDULE_GaccessliststoragekeyBer : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 1900
  | _, _ => none

def SCHEDULE_GcopyDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcopy_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 3
  | _, _ => none

def SCHEDULE_maxCodeSizeDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 4294967295
  | _, _ => none

def SCHEDULE_GecaddIst : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecadd_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 150
  | _, _ => none

def SCHEDULE_GexpDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gexp_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 10
  | _, _ => none

def SCHEDULE_GaccesslistaddressDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccesslistaddress_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GinitcodewordcostShang : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Ginitcodewordcost_SCHEDULE_ScheduleConst, SortSchedule.SHANGHAI_EVM => some 2
  | _, _ => none

def SCHEDULE_GecpairconstDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpairconst_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 100000
  | _, _ => none

def SCHEDULE_GwarmstoragereadDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GselfdestructDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GquaddivisorDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gquaddivisor_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GjumpdestDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gjumpdest_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 1
  | _, _ => none

def SCHEDULE_GtxdatanonzeroIst : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxdatanonzero_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 16
  | _, _ => none

def SCHEDULE_GaccesslistaddressBer : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccesslistaddress_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 2400
  | _, _ => none

def SCHEDULE_GcreateDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcreate_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 32000
  | _, _ => none

def SCHEDULE_GselfdestructTang : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 5000
  | _, _ => none

def SCHEDULE_GhighDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Ghigh_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 10
  | _, _ => none

def SCHEDULE_GwarmstoragereadBer : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 100
  | _, _ => none

def SCHEDULE_GbalanceDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GcallvalueDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcallvalue_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 9000
  | _, _ => none

def SCHEDULE_GsloadDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 50
  | _, _ => none

def SCHEDULE_GsloadIst : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 800
  | _, _ => none

def SCHEDULE_GfroundDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gfround_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 1
  | _, _ => none

def _53fc758 : SortBool → Option SortBool
  | true => some false
  | _ => none

def SCHEDULE_GcallTang : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcall_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 700
  | _, _ => none

def SCHEDULE_GwarmstoragedirtystoreDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gwarmstoragedirtystore_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_RselfdestructLond : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.LONDON_EVM => some 0
  | _, _ => none

def SCHEDULE_GquadcoeffDef : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gquadcoeff_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 512
  | _, _ => none

def _1ff8f4d {SortSort : Type} : SortBool → SortSort → SortSort → Option SortSort
  | C, B1, _Gen0 => do
    guard C
    return B1

def _75897fa : SortWordStack → SortInt → Option SortInt
  | SortWordStack.«.WordStack_EVM-TYPES_WordStack», SIZE => some SIZE
  | _, _ => none

axiom «.List» : Option SortList

axiom _Map_ (x0 : SortMap) (x1 : SortMap) : Option SortMap

axiom _modInt_ (x0 : SortInt) (x1 : SortInt) : Option SortInt

axiom SetItem (x0 : SortKItem) : Option SortSet

axiom ListItem (x0 : SortKItem) : Option SortList

axiom AccountCellMapItem (x0 : SortAcctIDCell) (x1 : SortAccountCell) : Option SortAccountCellMap

axiom _AccountCellMap_ (x0 : SortAccountCellMap) (x1 : SortAccountCellMap) : Option SortAccountCellMap

axiom «.Set» : Option SortSet

axiom _List_ (x0 : SortList) (x1 : SortList) : Option SortList

axiom «.MessageCellMap» : Option SortMessageCellMap

axiom _Set_ (x0 : SortSet) (x1 : SortSet) : Option SortSet

axiom _MessageCellMap_ (x0 : SortMessageCellMap) (x1 : SortMessageCellMap) : Option SortMessageCellMap

axiom «.AccountCellMap» : Option SortAccountCellMap

axiom «_|->_» (x0 : SortKItem) (x1 : SortKItem) : Option SortMap

axiom MessageCellMapItem (x0 : SortMsgIDCell) (x1 : SortMessageCell) : Option SortMessageCellMap

def _c6b37e3 : SortGas → SortGas → Option SortGas
  | SortGas.inj_SortInt I1, SortGas.inj_SortInt I2 => do
    let _Val0 <- «_-Int_» I1 I2
    return ((@inj SortInt SortGas) _Val0)

def _andBool_ (x0 : SortBool) (x1 : SortBool) : Option SortBool := (_5b9db8d x0 x1) <|> (_61fbef3 x0 x1)

def _orBool_ (x0 : SortBool) (x1 : SortBool) : Option SortBool := (_7174452 x0 x1) <|> (_991a329 x0 x1)

def SCHEDULE_RbConst : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.CONSTANTINOPLE_EVM => do
    let _Val0 <- «_*Int_» 2 1000000000000000000
    return _Val0
  | _, _ => none

def SCHEDULE_RbByz : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.BYZANTIUM_EVM => do
    let _Val0 <- «_*Int_» 3 1000000000000000000
    return _Val0
  | _, _ => none

def notBool_ (x0 : SortBool) : Option SortBool := (_17ebc68 x0) <|> (_53fc758 x0)

mutual
  def _432555e : SortWordStack → SortInt → Option SortInt
    | SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Gen0 WS, SIZE => do
      let _Val0 <- «_+Int_» SIZE 1
      let _Val1 <- sizeWordStackAux WS _Val0
      return _Val1
    | _, _ => none

  def sizeWordStackAux (x0 : SortWordStack) (x1 : SortInt) : Option SortInt := (_432555e x0 x1) <|> (_75897fa x0 x1)
end

def _33ba3c9 : SortGas → SortGas → Option SortBool
  | SortGas.inj_SortInt I1, SortGas.inj_SortInt I2 => do
    let _Val0 <- «_<=Int_» I1 I2
    return _Val0

noncomputable def _85aa67b : SortInt → Option SortInt
  | I => do
    let _Val0 <- _modInt_ I 115792089237316195423570985008687907853269984665640564039457584007913129639936
    return _Val0

def «_-Gas__GAS-SYNTAX_Gas_Gas_Gas» (x0 : SortGas) (x1 : SortGas) : Option SortGas := _c6b37e3 x0 x1

noncomputable def _bccaba7 : SortK → SortK → Option SortBool
  | K1, K2 => do
    let _Val0 <- «_==K_» K1 K2
    let _Val1 <- notBool_ _Val0
    return _Val1

def _2f3f58a {SortSort : Type} : SortBool → SortSort → SortSort → Option SortSort
  | C, _Gen0, B2 => do
    let _Val0 <- notBool_ C
    guard _Val0
    return B2

def _c0f9e27 : SortWordStack → Option SortInt
  | WS => do
    let _Val0 <- sizeWordStackAux WS 0
    return _Val0

def «_<=Gas__GAS-SYNTAX_Bool_Gas_Gas» (x0 : SortGas) (x1 : SortGas) : Option SortBool := _33ba3c9 x0 x1

noncomputable def chop (x0 : SortInt) : Option SortInt := _85aa67b x0

noncomputable def «_=/=K_» (x0 : SortK) (x1 : SortK) : Option SortBool := _bccaba7 x0 x1

def kite {SortSort : Type} (x0 : SortBool) (x1 : SortSort) (x2 : SortSort) : Option SortSort := (_1ff8f4d x0 x1 x2) <|> (_2f3f58a x0 x1 x2)

def «#sizeWordStack» (x0 : SortWordStack) : Option SortInt := _c0f9e27 x0

-- Necessary to have the following `mutual` block passing without a `decreasing_by` proof
attribute [local simp] Prod.lex_def SortScheduleConst.toNat SortSchedule.toNat

mutual
  noncomputable def SCHEDULE_GsstoreresetBer : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SortSchedule.BERLIN_EVM
      let _Val1 <- «_-Int_» 5000 _Val0
      return _Val1
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTMerg : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.MERGE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rb_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.LONDON_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTTang1 : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.TANGERINE_WHISTLE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gsload_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gcall_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gselfdestruct_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gextcodesize_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val8 <- _orBool_ _Val6 _Val7
      let _Val9 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gextcodecopy_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val10 <- _orBool_ _Val8 _Val9
      let _Val11 <- notBool_ _Val10
      let _Val12 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.HOMESTEAD_EVM
      guard _Val11
      return _Val12
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTByz : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.BYZANTIUM_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rb_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.SPURIOUS_DRAGON_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTDrag1 : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.SPURIOUS_DRAGON_EVM => do
      let _Val0 <- «_=/=K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_=/=K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _andBool_ _Val0 _Val1
      let _Val3 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.TANGERINE_WHISTLE_EVM
      guard _Val2
      return _Val3
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTCanc : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.CANCUN_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gwarmstoragedirtystore_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.SHANGHAI_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_GsloadBer : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SortSchedule.BERLIN_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTBer : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.BERLIN_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gcoldaccountaccess_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gsload_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val8 <- _orBool_ _Val6 _Val7
      let _Val9 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gquaddivisor_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val10 <- _orBool_ _Val8 _Val9
      let _Val11 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val12 <- _orBool_ _Val10 _Val11
      let _Val13 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gaccesslistaddress_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val14 <- _orBool_ _Val12 _Val13
      let _Val15 <- notBool_ _Val14
      let _Val16 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.ISTANBUL_EVM
      guard _Val15
      return _Val16
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_GwarmstoragedirtystoreCanc : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Gwarmstoragedirtystore_SCHEDULE_ScheduleConst, SortSchedule.CANCUN_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SortSchedule.CANCUN_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTPete : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.PETERSBURG_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.CONSTANTINOPLE_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTLond : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.LONDON_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rselfdestruct_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rmaxquotient_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- notBool_ _Val4
      let _Val6 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.BERLIN_EVM
      guard _Val5
      return _Val6
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTIst : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.ISTANBUL_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gecadd_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gecmul_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gecpairconst_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gecpaircoeff_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gtxdatanonzero_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val8 <- _orBool_ _Val6 _Val7
      let _Val9 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gsload_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val10 <- _orBool_ _Val8 _Val9
      let _Val11 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val12 <- _orBool_ _Val10 _Val11
      let _Val13 <- notBool_ _Val12
      let _Val14 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.PETERSBURG_EVM
      guard _Val13
      return _Val14
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (x0 : SortScheduleConst) (x1 : SortSchedule) : Option SortInt := (SCHEDULE_GaccesslistaddressBer x0 x1) <|>
  (SCHEDULE_GaccesslistaddressDef x0 x1) <|> (SCHEDULE_GaccessliststoragekeyBer x0 x1) <|> (SCHEDULE_GaccessliststoragekeyDef x0 x1) <|> (SCHEDULE_GbalanceDef x0 x1) <|> (SCHEDULE_GbalanceIst x0 x1) <|> (SCHEDULE_GbalanceTang x0 x1) <|> (SCHEDULE_GbaseDef x0 x1) <|> (SCHEDULE_GblockhashDef x0 x1) <|> (SCHEDULE_GcallDef x0 x1) <|> (SCHEDULE_GcallTang x0 x1) <|> (SCHEDULE_GcallstipendDef x0 x1) <|> (SCHEDULE_GcallvalueDef x0 x1) <|> (SCHEDULE_GcodedepositDef x0 x1) <|> (SCHEDULE_GcoldaccountaccessBer x0 x1) <|> (SCHEDULE_GcoldaccountaccessDef x0 x1) <|> (SCHEDULE_GcoldsloadBer x0 x1) <|> (SCHEDULE_GcoldsloadDef x0 x1) <|> (SCHEDULE_GcopyDef x0 x1) <|> (SCHEDULE_GcreateDef x0 x1) <|> (SCHEDULE_GecaddDef x0 x1) <|> (SCHEDULE_GecaddIst x0 x1) <|> (SCHEDULE_GecmulDef x0 x1) <|> (SCHEDULE_GecmulIst x0 x1) <|> (SCHEDULE_GecpaircoeffDef x0 x1) <|> (SCHEDULE_GecpaircoeffIst x0 x1) <|> (SCHEDULE_GecpairconstDef x0 x1) <|> (SCHEDULE_GecpairconstIst x0 x1) <|> (SCHEDULE_GexpDef x0 x1) <|> (SCHEDULE_GexpbyteDef x0 x1) <|> (SCHEDULE_GexpbyteDrag x0 x1) <|> (SCHEDULE_GextcodecopyTang x0 x1) <|> (SCHEDULE_GextcodesizeDef x0 x1) <|> (SCHEDULE_GextcodesizeTang x0 x1) <|> (SCHEDULE_GfroundDef x0 x1) <|> (SCHEDULE_GhighDef x0 x1) <|> (SCHEDULE_GinitcodewordcostDef x0 x1) <|> (SCHEDULE_GinitcodewordcostShang x0 x1) <|> (SCHEDULE_GjumpdestDef x0 x1) <|> (SCHEDULE_GlogDef x0 x1) <|> (SCHEDULE_GlogdataDef x0 x1) <|> (SCHEDULE_GlogtopicDef x0 x1) <|> (SCHEDULE_GlowDef x0 x1) <|> (SCHEDULE_GmemoryDef x0 x1) <|> (SCHEDULE_GmidDef x0 x1) <|> (SCHEDULE_GnewaccountDef x0 x1) <|> (SCHEDULE_GquadcoeffDef x0 x1) <|> (SCHEDULE_GquaddivisorBer x0 x1) <|> (SCHEDULE_GquaddivisorDef x0 x1) <|> (SCHEDULE_GselfdestructDef x0 x1) <|> (SCHEDULE_GselfdestructTang x0 x1) <|> (SCHEDULE_Gsha3Def x0 x1) <|> (SCHEDULE_Gsha3wordDef x0 x1) <|> (SCHEDULE_GsloadBer x0 x1) <|> (SCHEDULE_GsloadDef x0 x1) <|> (SCHEDULE_GsloadIst x0 x1) <|> (SCHEDULE_GsloadTang x0 x1) <|> (SCHEDULE_GsstoreresetBer x0 x1) <|> (SCHEDULE_GsstoreresetDef x0 x1) <|> (SCHEDULE_GsstoresetDef x0 x1) <|> (SCHEDULE_GtransactionDef x0 x1) <|> (SCHEDULE_GtxcreateDef x0 x1) <|> (SCHEDULE_GtxcreateFront x0 x1) <|> (SCHEDULE_GtxdatanonzeroDef x0 x1) <|> (SCHEDULE_GtxdatanonzeroIst x0 x1) <|> (SCHEDULE_GtxdatazeroDef x0 x1) <|> (SCHEDULE_GverylowDef x0 x1) <|> (SCHEDULE_GwarmstoragedirtystoreCanc x0 x1) <|> (SCHEDULE_GwarmstoragedirtystoreDef x0 x1) <|> (SCHEDULE_GwarmstoragereadBer x0 x1) <|> (SCHEDULE_GwarmstoragereadDef x0 x1) <|> (SCHEDULE_GzeroDef x0 x1) <|> (SCHEDULE_RbByz x0 x1) <|> (SCHEDULE_RbConst x0 x1) <|> (SCHEDULE_RbDef x0 x1) <|> (SCHEDULE_RbMerg x0 x1) <|> (SCHEDULE_Rmaxquotient x0 x1) <|> (SCHEDULE_RmaxquotientLond x0 x1) <|> (SCHEDULE_RselfdestructDef x0 x1) <|> (SCHEDULE_RselfdestructLond x0 x1) <|> (SCHEDULE_RsstoreclearDef x0 x1) <|> (SCHEDULE_RsstoreclearLond x0 x1) <|> (SCHEDULE_SCHEDCONSTBer x0 x1) <|> (SCHEDULE_SCHEDCONSTByz x0 x1) <|> (SCHEDULE_SCHEDCONSTCanc x0 x1) <|> (SCHEDULE_SCHEDCONSTConst x0 x1) <|> (SCHEDULE_SCHEDCONSTDrag1 x0 x1) <|> (SCHEDULE_SCHEDCONSTFront x0 x1) <|> (SCHEDULE_SCHEDCONSTHome x0 x1) <|> (SCHEDULE_SCHEDCONSTIst x0 x1) <|> (SCHEDULE_SCHEDCONSTLond x0 x1) <|> (SCHEDULE_SCHEDCONSTMerg x0 x1) <|> (SCHEDULE_SCHEDCONSTPete x0 x1) <|> (SCHEDULE_SCHEDCONSTShang x0 x1) <|> (SCHEDULE_SCHEDCONSTTang1 x0 x1) <|> (SCHEDULE_maxCodeSizeDef x0 x1) <|> (SCHEDULE_maxCodeSizeDrag x0 x1) <|> (SCHEDULE_maxInitCodeSizeDef x0 x1) <|> (SCHEDULE_maxInitCodeSizeShang x0 x1) <|> (_fc2d477 x0 x1)
  termination_by (x1.toNat, x0.toNat + 1)

  noncomputable def SCHEDULE_RsstoreclearLond : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst, SortSchedule.LONDON_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst SortSchedule.LONDON_EVM
      let _Val1 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst SortSchedule.LONDON_EVM
      let _Val2 <- «_+Int_» _Val0 _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_maxInitCodeSizeShang : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.maxInitCodeSize_SCHEDULE_ScheduleConst, SortSchedule.SHANGHAI_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst SortSchedule.SHANGHAI_EVM
      let _Val1 <- «_*Int_» 2 _Val0
      return _Val1
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTShang : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.SHANGHAI_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.maxInitCodeSize_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Ginitcodewordcost_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- notBool_ _Val2
      let _Val4 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.MERGE_EVM
      guard _Val3
      return _Val4
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTFront : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.FRONTIER_EVM => do
      let _Val0 <- «_=/=K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gtxcreate_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.DEFAULT_EVM
      guard _Val0
      return _Val1
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTConst : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.CONSTANTINOPLE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rb_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.BYZANTIUM_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTHome : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.HOMESTEAD_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.DEFAULT_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)
end

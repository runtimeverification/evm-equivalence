import EvmEquivalence.KEVM2Lean.Inj
import EvmEquivalence.KEVM2Lean.ScheduleOrdering

axiom «.Set» : Option SortSet

axiom _Map_ (x0 : SortMap) (x1 : SortMap) : Option SortMap

def SCHEDULE_GexpDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gexp_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 10
  | _, _ => none

def SCHEDULE_GpointevalDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gpointeval_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GextcodecopyTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodecopy_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 700
  | _, _ => none

def SCHEDULE_GsloadIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 800
  | _, _ => none

def SCHEDULE_GtxcreateDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxcreate_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 53000
  | _, _ => none

def SCHEDULE_GcallvalueDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcallvalue_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 9000
  | _, _ => none

def SCHEDULE_GlogtopicDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glogtopic_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 375
  | _, _ => none

def SCHEDULE_GcallstipendDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcallstipend_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 2300
  | _, _ => none

def SCHEDULE_GlogdataDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glogdata_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 8
  | _, _ => none

def SCHEDULE_GquadcoeffDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gquadcoeff_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 512
  | _, _ => none

def SCHEDULE_GwarmstoragereadBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 100
  | _, _ => none

def SCHEDULE_GcoldsloadBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 2100
  | _, _ => none

def SCHEDULE_GexpbyteDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 10
  | _, _ => none

def SCHEDULE_RselfdestructDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 24000
  | _, _ => none

def SCHEDULE_GbalanceIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 700
  | _, _ => none

def SCHEDULE_GwarmstoragedirtystoreDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gwarmstoragedirtystore_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_RsstoreclearDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 15000
  | _, _ => none

def SCHEDULE_GnewaccountDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gnewaccount_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 25000
  | _, _ => none

def SCHEDULE_GlogDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glog_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 375
  | _, _ => none

def SCHEDULE_GverylowDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 3
  | _, _ => none

def SCHEDULE_GblockhashDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gblockhash_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GselfdestructTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 5000
  | _, _ => none

def SCHEDULE_RbMerge : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.MERGE_EVM => some 0
  | _, _ => none

def _5b9db8d : SortBool → SortBool → Option SortBool
  | true, B => some B
  | _, _ => none

def SCHEDULE_GaccesslistaddressBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccesslistaddress_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 2400
  | _, _ => none

def SCHEDULE_GcallDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcall_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 40
  | _, _ => none

def SCHEDULE_GextcodesizeDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodesize_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_RmaxquotientLondon : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rmaxquotient_SCHEDULE_ScheduleConst, SortSchedule.LONDON_EVM => some 5
  | _, _ => none

def SCHEDULE_GsloadTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 200
  | _, _ => none

def SCHEDULE_GjumpdestDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gjumpdest_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 1
  | _, _ => none

def SCHEDULE_GecmulIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecmul_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 6000
  | _, _ => none

def SCHEDULE_GcoldaccountaccessDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldaccountaccess_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GpointevalCancun : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gpointeval_SCHEDULE_ScheduleConst, SortSchedule.CANCUN_EVM => some 50000
  | _, _ => none

def SCHEDULE_GecpaircoeffIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpaircoeff_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 34000
  | _, _ => none

def SCHEDULE_maxInitCodeSizeDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.maxInitCodeSize_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GexpbyteDragon : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst, SortSchedule.SPURIOUS_DRAGON_EVM => some 50
  | _, _ => none

def SCHEDULE_GtxcreateFrontier : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxcreate_SCHEDULE_ScheduleConst, SortSchedule.FRONTIER_EVM => some 21000
  | _, _ => none

def SCHEDULE_RselfdestructLondon : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.LONDON_EVM => some 0
  | _, _ => none

def SCHEDULE_GquaddivisorBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gquaddivisor_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 3
  | _, _ => none

def SCHEDULE_GwarmstoragereadDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GaccesslistaddressDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccesslistaddress_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GcoldsloadDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_maxCodeSizeDragon : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst, SortSchedule.SPURIOUS_DRAGON_EVM => some 24576
  | _, _ => none

axiom «_==K_» (x0 : SortK) (x1 : SortK) : Option SortBool

def SCHEDULE_GecmulDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecmul_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 40000
  | _, _ => none

def SCHEDULE_GtxdatazeroDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxdatazero_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 4
  | _, _ => none

def SCHEDULE_GtxdatanonzeroIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxdatanonzero_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 16
  | _, _ => none

def SCHEDULE_GbalanceDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GmemoryDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gmemory_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 3
  | _, _ => none

def SCHEDULE_GtxdatanonzeroDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxdatanonzero_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 68
  | _, _ => none

def SCHEDULE_GselfdestructDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GecpaircoeffDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpaircoeff_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 80000
  | _, _ => none

def SCHEDULE_GtransactionDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtransaction_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 21000
  | _, _ => none

def SCHEDULE_GsstoreresetDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 5000
  | _, _ => none

def SCHEDULE_GfroundDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gfround_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 1
  | _, _ => none

def SCHEDULE_GlowDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glow_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 5
  | _, _ => none

def SCHEDULE_GecpairconstDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpairconst_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 100000
  | _, _ => none

def SCHEDULE_GcreateDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcreate_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 32000
  | _, _ => none

def SCHEDULE_GcopyDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcopy_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 3
  | _, _ => none

def SCHEDULE_GecaddIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecadd_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 150
  | _, _ => none

def SCHEDULE_GcodedepositDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcodedeposit_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 200
  | _, _ => none

def SCHEDULE_GcallTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcall_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 700
  | _, _ => none

def SCHEDULE_GcoldaccountaccessBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldaccountaccess_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 2600
  | _, _ => none

def SCHEDULE_GecpairconstIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpairconst_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 45000
  | _, _ => none

def SCHEDULE_GsstoresetDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsstoreset_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20000
  | _, _ => none

def SCHEDULE_GecaddDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecadd_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 500
  | _, _ => none

def SCHEDULE_GsloadDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 50
  | _, _ => none

def SCHEDULE_RmaxquotientDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rmaxquotient_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 2
  | _, _ => none

def _61fbef3 : SortBool → SortBool → Option SortBool
  | false, _Gen0 => some false
  | _, _ => none

def SCHEDULE_GbaseDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbase_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 2
  | _, _ => none

def SCHEDULE_GmidDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gmid_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 8
  | _, _ => none

def SCHEDULE_GzeroDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gzero_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GextcodecopyDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodecopy_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_RbDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 5000000000000000000
  | _, _ => none

def SCHEDULE_Gsha3wordDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsha3word_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 6
  | _, _ => none

def _991a329 : SortBool → SortBool → Option SortBool
  | false, B => some B
  | _, _ => none

def _17ebc68 : SortBool → Option SortBool
  | false => some true
  | _ => none

def SCHEDULE_GquaddivisorDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gquaddivisor_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GinitcodewordcostDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Ginitcodewordcost_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GhighDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Ghigh_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 10
  | _, _ => none

def SCHEDULE_GaccessliststoragekeyDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GbalanceTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 400
  | _, _ => none

def SCHEDULE_GinitcodewordcostShanghai : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Ginitcodewordcost_SCHEDULE_ScheduleConst, SortSchedule.SHANGHAI_EVM => some 2
  | _, _ => none

def _7174452 : SortBool → SortBool → Option SortBool
  | true, _Gen0 => some true
  | _, _ => none

def SCHEDULE_GaccessliststoragekeyBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 1900
  | _, _ => none

def SCHEDULE_Gsha3Default : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsha3_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 30
  | _, _ => none

def SCHEDULE_GextcodesizeTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodesize_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 700
  | _, _ => none

def _53fc758 : SortBool → Option SortBool
  | true => some false
  | _ => none

def SCHEDULE_maxCodeSizeDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 4294967295
  | _, _ => none

axiom _MessageCellMap_ (x0 : SortMessageCellMap) (x1 : SortMessageCellMap) : Option SortMessageCellMap

axiom «.AccountCellMap» : Option SortAccountCellMap

axiom _WithdrawalCellMap_ (x0 : SortWithdrawalCellMap) (x1 : SortWithdrawalCellMap) : Option SortWithdrawalCellMap

axiom «.List» : Option SortList

axiom MessageCellMapItem (x0 : SortMsgIDCell) (x1 : SortMessageCell) : Option SortMessageCellMap

axiom «.WithdrawalCellMap» : Option SortWithdrawalCellMap

axiom SetItem (x0 : SortKItem) : Option SortSet

axiom «_|->_» (x0 : SortKItem) (x1 : SortKItem) : Option SortMap

axiom «.Map» : Option SortMap

axiom WithdrawalCellMapItem (x0 : SortWithdrawalIDCell) (x1 : SortWithdrawalCell) : Option SortWithdrawalCellMap

def _75897fa : SortWordStack → SortInt → Option SortInt
  | SortWordStack.«.WordStack_EVM-TYPES_WordStack», SIZE => some SIZE
  | _, _ => none

axiom «_<Int_» (x0 : SortInt) (x1 : SortInt) : Option SortBool

axiom _modInt_ (x0 : SortInt) (x1 : SortInt) : Option SortInt

axiom _List_ (x0 : SortList) (x1 : SortList) : Option SortList

axiom «.MessageCellMap» : Option SortMessageCellMap

axiom AccountCellMapItem (x0 : SortAcctIDCell) (x1 : SortAccountCell) : Option SortAccountCellMap

axiom _AccountCellMap_ (x0 : SortAccountCellMap) (x1 : SortAccountCellMap) : Option SortAccountCellMap

axiom _Set_ (x0 : SortSet) (x1 : SortSet) : Option SortSet

axiom ListItem (x0 : SortKItem) : Option SortList

def SCHEDULE_RbConstantinople : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.CONSTANTINOPLE_EVM => do
    let _Val0 <- «_*Int_» 2 1000000000000000000
    return _Val0
  | _, _ => none

def SCHEDULE_RbByzantium : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.BYZANTIUM_EVM => do
    let _Val0 <- «_*Int_» 3 1000000000000000000
    return _Val0
  | _, _ => none

def _andBool_ (x0 : SortBool) (x1 : SortBool) : Option SortBool := (_5b9db8d x0 x1) <|> (_61fbef3 x0 x1)

def _orBool_ (x0 : SortBool) (x1 : SortBool) : Option SortBool := (_7174452 x0 x1) <|> (_991a329 x0 x1)

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

noncomputable def _85aa67b : SortInt → Option SortInt
  | I => do
    let _Val0 <- _modInt_ I 115792089237316195423570985008687907853269984665640564039457584007913129639936
    return _Val0

noncomputable def _bccaba7 : SortK → SortK → Option SortBool
  | K1, K2 => do
    let _Val0 <- «_==K_» K1 K2
    let _Val1 <- notBool_ _Val0
    return _Val1

noncomputable def chop (x0 : SortInt) : Option SortInt := _85aa67b x0

noncomputable def «_=/=K_» (x0 : SortK) (x1 : SortK) : Option SortBool := _bccaba7 x0 x1

-- Necessary to have the following `mutual` block passing without a `decreasing_by` proof
attribute [local simp] Prod.lex_def SortScheduleConst.toNat SortSchedule.toNat

mutual
  noncomputable def SCHEDULE_GsstoreresetBerlin : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SortSchedule.BERLIN_EVM
      let _Val1 <- «_-Int_» 5000 _Val0
      return _Val1
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTMerge : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.MERGE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rb_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.LONDON_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTTangerine : SortScheduleConst → SortSchedule → Option SortInt
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

  noncomputable def SCHEDULE_SCHEDCONSTByzantium : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.BYZANTIUM_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rb_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.SPURIOUS_DRAGON_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTDragon : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.SPURIOUS_DRAGON_EVM => do
      let _Val0 <- «_=/=K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_=/=K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _andBool_ _Val0 _Val1
      let _Val3 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.TANGERINE_WHISTLE_EVM
      guard _Val2
      return _Val3
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_GsloadBerlin : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SortSchedule.BERLIN_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTBerlin : SortScheduleConst → SortSchedule → Option SortInt
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

  noncomputable def SCHEDULE_GwarmstoragedirtystoreCancun : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Gwarmstoragedirtystore_SCHEDULE_ScheduleConst, SortSchedule.CANCUN_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SortSchedule.CANCUN_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTPetersburg : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.PETERSBURG_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.CONSTANTINOPLE_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTLondon : SortScheduleConst → SortSchedule → Option SortInt
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

  noncomputable def SCHEDULE_SCHEDCONSTIstanbul : SortScheduleConst → SortSchedule → Option SortInt
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

  noncomputable def «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (x0 : SortScheduleConst) (x1 : SortSchedule) : Option SortInt := (SCHEDULE_GaccesslistaddressBerlin x0 x1) <|> (SCHEDULE_GaccesslistaddressDefault x0 x1) <|> (SCHEDULE_GaccessliststoragekeyBerlin x0 x1) <|> (SCHEDULE_GaccessliststoragekeyDefault x0 x1) <|> (SCHEDULE_GbalanceDefault x0 x1) <|> (SCHEDULE_GbalanceIstanbul x0 x1) <|> (SCHEDULE_GbalanceTangerine x0 x1) <|> (SCHEDULE_GbaseDefault x0 x1) <|> (SCHEDULE_GblockhashDefault x0 x1) <|> (SCHEDULE_GcallDefault x0 x1) <|> (SCHEDULE_GcallTangerine x0 x1) <|> (SCHEDULE_GcallstipendDefault x0 x1) <|> (SCHEDULE_GcallvalueDefault x0 x1) <|> (SCHEDULE_GcodedepositDefault x0 x1) <|> (SCHEDULE_GcoldaccountaccessBerlin x0 x1) <|> (SCHEDULE_GcoldaccountaccessDefault x0 x1) <|> (SCHEDULE_GcoldsloadBerlin x0 x1) <|> (SCHEDULE_GcoldsloadDefault x0 x1) <|> (SCHEDULE_GcopyDefault x0 x1) <|> (SCHEDULE_GcreateDefault x0 x1) <|> (SCHEDULE_GecaddDefault x0 x1) <|> (SCHEDULE_GecaddIstanbul x0 x1) <|> (SCHEDULE_GecmulDefault x0 x1) <|> (SCHEDULE_GecmulIstanbul x0 x1) <|> (SCHEDULE_GecpaircoeffDefault x0 x1) <|> (SCHEDULE_GecpaircoeffIstanbul x0 x1) <|> (SCHEDULE_GecpairconstDefault x0 x1) <|> (SCHEDULE_GecpairconstIstanbul x0 x1) <|> (SCHEDULE_GexpDefault x0 x1) <|> (SCHEDULE_GexpbyteDefault x0 x1) <|> (SCHEDULE_GexpbyteDragon x0 x1) <|> (SCHEDULE_GextcodecopyDefault x0 x1) <|> (SCHEDULE_GextcodecopyTangerine x0 x1) <|> (SCHEDULE_GextcodesizeDefault x0 x1) <|> (SCHEDULE_GextcodesizeTangerine x0 x1) <|> (SCHEDULE_GfroundDefault x0 x1) <|> (SCHEDULE_GhighDefault x0 x1) <|> (SCHEDULE_GinitcodewordcostDefault x0 x1) <|> (SCHEDULE_GinitcodewordcostShanghai x0 x1) <|> (SCHEDULE_GjumpdestDefault x0 x1) <|> (SCHEDULE_GlogDefault x0 x1) <|> (SCHEDULE_GlogdataDefault x0 x1) <|> (SCHEDULE_GlogtopicDefault x0 x1) <|> (SCHEDULE_GlowDefault x0 x1) <|> (SCHEDULE_GmemoryDefault x0 x1) <|> (SCHEDULE_GmidDefault x0 x1) <|> (SCHEDULE_GnewaccountDefault x0 x1) <|> (SCHEDULE_GpointevalCancun x0 x1) <|> (SCHEDULE_GpointevalDefault x0 x1) <|> (SCHEDULE_GquadcoeffDefault x0 x1) <|> (SCHEDULE_GquaddivisorBerlin x0 x1) <|> (SCHEDULE_GquaddivisorDefault x0 x1) <|> (SCHEDULE_GselfdestructDefault x0 x1) <|> (SCHEDULE_GselfdestructTangerine x0 x1) <|> (SCHEDULE_Gsha3Default x0 x1) <|> (SCHEDULE_Gsha3wordDefault x0 x1) <|> (SCHEDULE_GsloadBerlin x0 x1) <|> (SCHEDULE_GsloadDefault x0 x1) <|> (SCHEDULE_GsloadIstanbul x0 x1) <|> (SCHEDULE_GsloadTangerine x0 x1) <|> (SCHEDULE_GsstoreresetBerlin x0 x1) <|> (SCHEDULE_GsstoreresetDefault x0 x1) <|> (SCHEDULE_GsstoresetDefault x0 x1) <|> (SCHEDULE_GtransactionDefault x0 x1) <|> (SCHEDULE_GtxcreateDefault x0 x1) <|> (SCHEDULE_GtxcreateFrontier x0 x1) <|> (SCHEDULE_GtxdatanonzeroDefault x0 x1) <|> (SCHEDULE_GtxdatanonzeroIstanbul x0 x1) <|> (SCHEDULE_GtxdatazeroDefault x0 x1) <|> (SCHEDULE_GverylowDefault x0 x1) <|> (SCHEDULE_GwarmstoragedirtystoreCancun x0 x1) <|> (SCHEDULE_GwarmstoragedirtystoreDefault x0 x1) <|> (SCHEDULE_GwarmstoragereadBerlin x0 x1) <|> (SCHEDULE_GwarmstoragereadDefault x0 x1) <|> (SCHEDULE_GzeroDefault x0 x1) <|> (SCHEDULE_RbByzantium x0 x1) <|> (SCHEDULE_RbConstantinople x0 x1) <|> (SCHEDULE_RbDefault x0 x1) <|> (SCHEDULE_RbMerge x0 x1) <|> (SCHEDULE_RmaxquotientDefault x0 x1) <|> (SCHEDULE_RmaxquotientLondon x0 x1) <|> (SCHEDULE_RselfdestructDefault x0 x1) <|> (SCHEDULE_RselfdestructLondon x0 x1) <|> (SCHEDULE_RsstoreclearDefault x0 x1) <|> (SCHEDULE_RsstoreclearLondon x0 x1) <|> (SCHEDULE_SCHEDCONSTBerlin x0 x1) <|> (SCHEDULE_SCHEDCONSTByzantium x0 x1) <|> (SCHEDULE_SCHEDCONSTCancun x0 x1) <|> (SCHEDULE_SCHEDCONSTConstantinople x0 x1) <|> (SCHEDULE_SCHEDCONSTDragon x0 x1) <|> (SCHEDULE_SCHEDCONSTFrontier x0 x1) <|> (SCHEDULE_SCHEDCONSTHomestead x0 x1) <|> (SCHEDULE_SCHEDCONSTIstanbul x0 x1) <|> (SCHEDULE_SCHEDCONSTLondon x0 x1) <|> (SCHEDULE_SCHEDCONSTMerge x0 x1) <|> (SCHEDULE_SCHEDCONSTPetersburg x0 x1) <|> (SCHEDULE_SCHEDCONSTShanghai x0 x1) <|> (SCHEDULE_SCHEDCONSTTangerine x0 x1) <|> (SCHEDULE_maxCodeSizeDefault x0 x1) <|> (SCHEDULE_maxCodeSizeDragon x0 x1) <|> (SCHEDULE_maxInitCodeSizeDefault x0 x1) <|> (SCHEDULE_maxInitCodeSizeShanghai x0 x1)
  termination_by (x1.toNat, x0.toNat + 1)

  noncomputable def SCHEDULE_RsstoreclearLondon : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst, SortSchedule.LONDON_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst SortSchedule.LONDON_EVM
      let _Val1 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst SortSchedule.LONDON_EVM
      let _Val2 <- «_+Int_» _Val0 _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_maxInitCodeSizeShanghai : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.maxInitCodeSize_SCHEDULE_ScheduleConst, SortSchedule.SHANGHAI_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst SortSchedule.SHANGHAI_EVM
      let _Val1 <- «_*Int_» 2 _Val0
      return _Val1
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTShanghai : SortScheduleConst → SortSchedule → Option SortInt
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

  noncomputable def SCHEDULE_SCHEDCONSTFrontier : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.FRONTIER_EVM => do
      let _Val0 <- «_=/=K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gtxcreate_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.DEFAULT_EVM
      guard _Val0
      return _Val1
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTCancun : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.CANCUN_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gwarmstoragedirtystore_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gpointeval_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- notBool_ _Val2
      let _Val4 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.SHANGHAI_EVM
      guard _Val3
      return _Val4
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTConstantinople : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.CONSTANTINOPLE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rb_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.BYZANTIUM_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTHomestead : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.HOMESTEAD_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.DEFAULT_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)
end

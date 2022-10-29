{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module MainContract where

import Control.Applicative (Applicative (pure))
import Control.Monad (void)
import Data.Default (Default (def))
import Data.Text (Text)
import Ledger (POSIXTime, POSIXTimeRange, PaymentPubKeyHash (unPaymentPubKeyHash), ScriptContext (..), TxInfo (..),
               Validator, getCardanoTxId)
import Ledger qualified
import Ledger.Contexts qualified as V
import Ledger.Interval qualified as Interval
import Ledger.Scripts qualified as Scripts
import Ledger.TimeSlot qualified as TimeSlot
import Ledger.Typed.Scripts qualified as Scripts hiding (validatorHash)
import Ledger.Value (Value)
import Playground.Contract
import Plutus.Contract
import Plutus.Contract.Constraints qualified as Constraints
import Plutus.Contract.Typed.Tx qualified as Typed
import PlutusTx qualified
import PlutusTx.Prelude hiding (Applicative (..), Semigroup (..))
import Prelude (Semigroup (..))
import Prelude qualified as Haskell
import Wallet.Emulator qualified as Emulator


data Event = Event {
    eventDeadline :: POSIXTime,
    eventCollectionDeadline :: POSIXTime,
    eventOwner :: PaymentPubKeyHash
} deriving (Generic, ToJSON , FromJSON , ToSchema)

PlutusTx.makeLift ''Event

data EventAction = Collect | Refund

PlutusTx.unstableMakeIsData ''EventAction
PlutusTx.makeLift ''EventAction

type EventFundingSchema =
            Endpoint "schedule donation" ()
        .\/ Endpoint "donate" Donation

newtype Donation = Donation
        { donationValue :: Value} 
        deriving stock (Haskell.Eq, Show, Generic)
        deriving anyclass (ToJSON, FromJSON, ToSchema, ToArgument)

mkEvent :: POSIXTime -> POSIXTime -> Wallet -> Event
mkEvent ddl colddl ownerWallet =  
    Event 
    {eventDeadline = ddl
    , eventCollectionDeadline = colddl
    , eventOwner = Emulator.mockWalletPaymentPubKeyHash ownerWallet
    }

donationRange :: Event -> POSIXTimeRange
donationRange event = 
    Interval.interval (eventDeadline event) (eventCollectionDeadline event - 1)

refundRange :: Event -> POSIXTimeRange
refundRange event =
    Interval.from (eventCollectionDeadline event)

data Crowdfunding
instance Scripts.ValidatorTypes Crowdfunding where
    type instance RedeemerType Crowdfunding = EventAction
    type instance DatumType Crowdfunding = PaymentPubKeyHash

typedValidator :: Event -> Scripts.TypedValidator Crowdfunding
typedValidator = Scripts.mkTypedValidatorParam @Crowdfunding
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

{-# INLINABLE validRefund #-}
validRefund :: Event -> PaymentPubKeyHash -> TxInfo -> Bool
validRefund event contributor txinfo =
    (refundRange event `Interval.contains` txInfoValidRange txinfo)
    && (txinfo `V.txSignedBy` unPaymentPubKeyHash contributor)

validCollection :: Event -> TxInfo -> Bool
validCollection event txinfo =
    (collectionRange event `Interval.contains` txInfoValidRange txinfo)
    && (txinfo `V.txSignedBy` unPaymentPubKeyHash (eventOwner event))

mkValidator :: Event -> PaymentPubKeyHash -> EventAction -> ScriptContext -> Bool
mkValidator e con action p = case act of
    Refund  -> validRefund e con (scriptContextTxInfo p)
    Collect -> validCollection e (scriptContextTxInfo p)

donationScript :: Event -> Validator
donationScript = Scripts.validatorScript . typedValidator

eventAddress :: Event -> Ledger.ValidatorHash
eventAddress = Scripts.validatorHash . donationScript

crowdfunding :: AsContractError e => Event -> Contract () eventFundingSchema e ()
crowdfunding ev = selectList [contribute ev, scheduleCollection ev]

theEvent :: POSIXTime -> Event
theEvent startTime = Event
    { eventDeadline = startTime + 40000
    , eventCollectionDeadline = startTime + 60000
    , eventOwner = Emulator.mockWalletPaymentPubKeyHash (Emulator.knownWallet 1)
    }

contribute :: AsContractError e => Event -> Promise () eventFundingSchema e ()
contribute ev = endpoint @"donate" $ \Donation{donationValue} -> do
    contributor <- ownPaymentPubKeyHash
    let inst = typedValidator ev
        tx = Constraints.mustPayToTheScript contributor donationValue
                <> Constraints.mustValidateIn (Interval.to (eventDeadline ev))
    txid <- fmap getCardanoTxId $ mkTxConstraints (Constraints.typedValidatorLookups inst) tx
        >>= submitUnbalancedTx . Constraints.adjustUnbalancedTx

    utxo <- watchAddressUntilTime (Scripts.validatorAddress inst) (eventCollectionDeadline cmp)

    let flt Ledger.TxOutRef{txOutRefId} _ = txid Haskell.== txOutRefId
        tx' = Typed.collectFromScriptFilter flt utxo Refund
                <> Constraints.mustValidateIn (refundRange cmp)
                <> Constraints.mustBeSignedBy contributor
    if Constraints.modifiesUtxoSet tx'
    then do
        logInfo @Text "Claiming refund"
        void $ mkTxConstraints (Constraints.typedValidatorLookups inst
                             <> Constraints.unspentOutputs utxo) tx'
            >>= submitUnbalancedTx . Constraints.adjustUnbalancedTx
    else pure ()

scheduleCollection :: AsContractError e => Event -> Promise () eventFundingSchema e ()
scheduleCollection ev =
    endpoint @"schedule collection" $ \() -> do
        let inst = typedValidator ev

        _ <- awaitTime $ campaignDeadline ev
        unspentOutputs <- utxosAt (Scripts.validatorAddress inst)

        let tx = Typed.collectFromScript unspentOutputs Collect
                <> Constraints.mustValidateIn (collectionRange ev)
        void $ submitTxConstraintsSpending inst unspentOutputs tx

endpoints :: AsContractError e => Contract () eventFundingSchema e ()
endpoints = crowdfunding (theEvent $ TimeSlot.scSlotZeroTime def)

mkSchemaDefinitions ''eventFundingSchema

$(mkKnownCurrencies [])

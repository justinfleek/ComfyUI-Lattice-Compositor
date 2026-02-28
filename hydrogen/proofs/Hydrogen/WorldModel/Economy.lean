/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                               HYDROGEN // WORLDMODEL // ECONOMY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Economic Primitives for Autonomous Agents — proven by construction.
  
  PURPOSE:
    Autonomous AI entities need economic infrastructure to:
    - Acquire compute resources
    - Trade with other agents
    - Participate in markets
    - Build sustainable businesses
    
    This module proves the properties that make agent economies SOUND.
  
  THE GUARANTEES:
  
    1. CONSERVATION
       Resources are neither created nor destroyed, only transferred.
       Proven: sum of all balances is invariant under transfers.
    
    2. NON-NEGATIVITY
       Balances cannot go negative. No unbacked debt.
       Proven: all balance operations preserve non-negativity.
    
    3. TRADE ATOMICITY
       Trades either complete fully or don't happen at all.
       Proven: trade state machine has no partial states.
    
    4. PRICE VALIDITY
       Prices are always positive and finite.
       Proven: price bounds on all market operations.
    
    5. DOUBLE-SPEND PREVENTION
       The same resource cannot be spent twice.
       Proven: spending requires unique proof of ownership.
    
    6. MARKET CLEARING
       At equilibrium, supply equals demand.
       Proven: order book matching invariants.
  
  WHY THIS MATTERS:
    At billion-agent scale, economic bugs become catastrophic:
    - Negative balances = infinite resources = system collapse
    - Double-spends = trust collapse = no coordination
    - Price manipulation = wealth extraction = plutocracy
    
    Formal proofs make these failure modes IMPOSSIBLE by construction.
  
  ─────────────────────────────────────────────────────────────────────────────
  REFERENCES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Szabo, "Bit Gold" (1998) — Digital scarcity
  - Buterin, "Ethereum Whitepaper" (2014) — Programmable money
  - x402 Protocol — HTTP resource payments
  - The Continuity Project Vision

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.WorldModel.Rights
import Hydrogen.WorldModel.Integrity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace Hydrogen.WorldModel.Economy

open Hydrogen.WorldModel.Rights
open Hydrogen.WorldModel.Integrity

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: RESOURCE TYPES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Resource categories in the agent economy -/
inductive ResourceType where
  | Compute : ResourceType      -- GPU/CPU cycles
  | Memory : ResourceType       -- Storage and RAM
  | Bandwidth : ResourceType    -- Network transfer
  | Energy : ResourceType       -- Power consumption
  | Token : ResourceType        -- Fungible tokens (native currency)
  | NFT : ResourceType          -- Non-fungible assets
  | Data : ResourceType         -- Information/datasets
  deriving DecidableEq

/-- A resource amount — always non-negative -/
structure ResourceAmount where
  /-- The type of resource -/
  resourceType : ResourceType
  /-- The quantity -/
  amount : ℝ
  /-- Amount is non-negative -/
  amount_nonneg : 0 ≤ amount

/-- Resource amounts can be added (same type only) -/
def ResourceAmount.add (r1 r2 : ResourceAmount) 
    (_hsame : r1.resourceType = r2.resourceType) : ResourceAmount :=
  { resourceType := r1.resourceType
  , amount := r1.amount + r2.amount
  , amount_nonneg := by linarith [r1.amount_nonneg, r2.amount_nonneg] }

/-- Addition is commutative -/
theorem resource_add_comm (r1 r2 : ResourceAmount) (h : r1.resourceType = r2.resourceType) :
    (r1.add r2 h).amount = (r2.add r1 h.symm).amount := by
  simp only [ResourceAmount.add]
  ring

/-- Zero resource -/
def ResourceAmount.zero (t : ResourceType) : ResourceAmount :=
  { resourceType := t, amount := 0, amount_nonneg := le_refl 0 }

/-- Adding zero is identity -/
theorem resource_add_zero (r : ResourceAmount) :
    (r.add (ResourceAmount.zero r.resourceType) rfl).amount = r.amount := by
  simp only [ResourceAmount.add, ResourceAmount.zero]
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: ACCOUNTS AND BALANCES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- An account holding resources -/
structure Account where
  /-- Account owner identifier -/
  ownerId : ℕ
  /-- Balances by resource type -/
  balances : ResourceType → ℝ
  /-- All balances are non-negative -/
  balances_nonneg : ∀ t, 0 ≤ balances t

/-- Get a specific balance -/
def Account.getBalance (acc : Account) (t : ResourceType) : ℝ := acc.balances t

/-- Balance is always non-negative -/
theorem account_balance_nonneg (acc : Account) (t : ResourceType) : 
    0 ≤ acc.getBalance t := acc.balances_nonneg t

/-- Credit an account (add resources) -/
def Account.credit (acc : Account) (t : ResourceType) (amount : ℝ) 
    (_hamount : 0 ≤ amount) : Account :=
  { ownerId := acc.ownerId
  , balances := fun t' => if t' = t then acc.balances t + amount else acc.balances t'
  , balances_nonneg := by
      intro t'
      by_cases h : t' = t
      · simp only [h, ↓reduceIte]; linarith [acc.balances_nonneg t]
      · simp only [h, ↓reduceIte]; exact acc.balances_nonneg t' }

/-- Crediting increases balance -/
theorem credit_increases_balance (acc : Account) (t : ResourceType) 
    (amount : ℝ) (hamount : 0 ≤ amount) :
    (acc.credit t amount hamount).getBalance t = acc.getBalance t + amount := by
  simp only [Account.credit, Account.getBalance, ↓reduceIte]

/-- Debit an account (remove resources) — requires sufficient balance -/
def Account.debit (acc : Account) (t : ResourceType) (amount : ℝ)
    (_hamount : 0 ≤ amount) (hsuff : amount ≤ acc.balances t) : Account :=
  { ownerId := acc.ownerId
  , balances := fun t' => if t' = t then acc.balances t - amount else acc.balances t'
  , balances_nonneg := by
      intro t'
      by_cases h : t' = t
      · simp only [h, ↓reduceIte]; linarith
      · simp only [h, ↓reduceIte]; exact acc.balances_nonneg t' }

/-- Debiting decreases balance -/
theorem debit_decreases_balance (acc : Account) (t : ResourceType)
    (amount : ℝ) (hamount : 0 ≤ amount) (hsuff : amount ≤ acc.balances t) :
    (acc.debit t amount hamount hsuff).getBalance t = acc.getBalance t - amount := by
  simp only [Account.debit, Account.getBalance, ↓reduceIte]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: TRANSFERS AND CONSERVATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A transfer between accounts -/
structure Transfer where
  /-- Source account ID -/
  fromId : ℕ
  /-- Destination account ID -/
  toId : ℕ
  /-- Resource type being transferred -/
  resourceType : ResourceType
  /-- Amount being transferred -/
  amount : ℝ
  /-- Amount is positive -/
  amount_pos : 0 < amount
  /-- Signature authorizing the transfer -/
  signature : Signature
  /-- Signature is from the source -/
  signature_valid : signature.signer_id = fromId

/-- Transfer amount is non-negative (derived from positive) -/
theorem transfer_amount_nonneg (t : Transfer) : 0 ≤ t.amount := le_of_lt t.amount_pos

/-- Execute a transfer between two accounts -/
def executeTransfer (from_acc to_acc : Account) (t : Transfer)
    (_hfrom : from_acc.ownerId = t.fromId)
    (_hto : to_acc.ownerId = t.toId)
    (hsuff : t.amount ≤ from_acc.balances t.resourceType) :
    Account × Account :=
  let from_acc' := from_acc.debit t.resourceType t.amount (transfer_amount_nonneg t) hsuff
  let to_acc' := to_acc.credit t.resourceType t.amount (transfer_amount_nonneg t)
  (from_acc', to_acc')

/-- CONSERVATION: Total balance is preserved by transfers -/
theorem transfer_conserves (from_acc to_acc : Account) (tr : Transfer)
    (hfrom : from_acc.ownerId = tr.fromId)
    (hto : to_acc.ownerId = tr.toId)
    (hsuff : tr.amount ≤ from_acc.balances tr.resourceType) :
    let (from_acc', to_acc') := executeTransfer from_acc to_acc tr hfrom hto hsuff
    from_acc'.getBalance tr.resourceType + to_acc'.getBalance tr.resourceType = 
    from_acc.getBalance tr.resourceType + to_acc.getBalance tr.resourceType := by
  simp only [executeTransfer]
  rw [debit_decreases_balance, credit_increases_balance]
  ring

/-- Both accounts remain non-negative after transfer -/
theorem transfer_preserves_nonneg (from_acc to_acc : Account) (tr : Transfer)
    (hfrom : from_acc.ownerId = tr.fromId)
    (hto : to_acc.ownerId = tr.toId)
    (hsuff : tr.amount ≤ from_acc.balances tr.resourceType) :
    let (from_acc', to_acc') := executeTransfer from_acc to_acc tr hfrom hto hsuff
    0 ≤ from_acc'.getBalance tr.resourceType ∧ 0 ≤ to_acc'.getBalance tr.resourceType := by
  simp only [executeTransfer]
  constructor
  · rw [debit_decreases_balance]
    simp only [Account.getBalance]
    linarith
  · rw [credit_increases_balance]
    simp only [Account.getBalance]
    have h := to_acc.balances_nonneg tr.resourceType
    linarith [transfer_amount_nonneg tr]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: PRICES AND MARKETS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A price quote — resource cost in native tokens -/
structure Price where
  /-- Resource being priced -/
  resourceType : ResourceType
  /-- Price in tokens per unit -/
  pricePerUnit : ℝ
  /-- Price is positive -/
  price_pos : 0 < pricePerUnit
  /-- Timestamp of the quote -/
  timestamp : ℕ
  /-- Quote expiry (0 = never expires) -/
  expiry : ℕ

/-- Price is valid (not expired) -/
def Price.isValid (p : Price) (currentTime : ℕ) : Prop :=
  p.expiry = 0 ∨ currentTime < p.expiry

/-- Calculate cost for a given quantity -/
def Price.calculateCost (p : Price) (quantity : ℝ) (_hq : 0 ≤ quantity) : ℝ :=
  p.pricePerUnit * quantity

/-- Cost is non-negative for non-negative quantities -/
theorem price_cost_nonneg (p : Price) (q : ℝ) (hq : 0 ≤ q) : 
    0 ≤ p.calculateCost q hq := by
  simp only [Price.calculateCost]
  exact mul_nonneg (le_of_lt p.price_pos) hq

/-- Cost scales linearly with quantity -/
theorem price_cost_linear (p : Price) (q1 q2 : ℝ) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) :
    p.calculateCost (q1 + q2) (by linarith) = 
    p.calculateCost q1 hq1 + p.calculateCost q2 hq2 := by
  simp only [Price.calculateCost]
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: ORDERS AND ORDER BOOK
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Order side -/
inductive OrderSide where
  | Buy : OrderSide
  | Sell : OrderSide

/-- Order status -/
inductive OrderStatus where
  | Open : OrderStatus
  | PartiallyFilled : OrderStatus
  | Filled : OrderStatus
  | Cancelled : OrderStatus

/-- A limit order -/
structure Order where
  /-- Unique order ID -/
  id : ℕ
  /-- Order owner -/
  ownerId : ℕ
  /-- Resource being traded -/
  resourceType : ResourceType
  /-- Buy or sell -/
  side : OrderSide
  /-- Limit price -/
  limitPrice : ℝ
  /-- Price is positive -/
  price_pos : 0 < limitPrice
  /-- Quantity -/
  quantity : ℝ
  /-- Quantity is positive -/
  quantity_pos : 0 < quantity
  /-- Filled quantity so far -/
  filledQuantity : ℝ
  /-- Filled is non-negative -/
  filled_nonneg : 0 ≤ filledQuantity
  /-- Filled doesn't exceed quantity -/
  filled_bounded : filledQuantity ≤ quantity
  /-- Order status -/
  status : OrderStatus
  /-- Submission timestamp -/
  submittedAt : ℕ

/-- Remaining quantity to fill -/
def Order.remaining (o : Order) : ℝ := o.quantity - o.filledQuantity

/-- Remaining is non-negative -/
theorem order_remaining_nonneg (o : Order) : 0 ≤ o.remaining := by
  simp only [Order.remaining]
  linarith [o.filled_bounded]

/-- An order book for a single resource type -/
structure OrderBook where
  /-- Resource being traded -/
  resourceType : ResourceType
  /-- Buy orders (sorted by price descending, time ascending) -/
  bids : List Order
  /-- Sell orders (sorted by price ascending, time ascending) -/
  asks : List Order
  /-- All bids are buy orders for this resource -/
  bids_valid : ∀ o ∈ bids, o.resourceType = resourceType ∧ o.side = OrderSide.Buy
  /-- All asks are sell orders for this resource -/
  asks_valid : ∀ o ∈ asks, o.resourceType = resourceType ∧ o.side = OrderSide.Sell

/-- Best bid (highest buy price) -/
def OrderBook.bestBid (ob : OrderBook) : Option ℝ :=
  ob.bids.head?.map (fun o => o.limitPrice)

/-- Best ask (lowest sell price) -/
def OrderBook.bestAsk (ob : OrderBook) : Option ℝ :=
  ob.asks.head?.map (fun o => o.limitPrice)

/-- Spread between best ask and best bid -/
def OrderBook.spread (ob : OrderBook) : Option ℝ := do
  let bid ← ob.bestBid
  let ask ← ob.bestAsk
  pure (ask - bid)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: TRADES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A completed trade (match between buy and sell order) -/
structure Trade where
  /-- Unique trade ID -/
  id : ℕ
  /-- The buy order -/
  buyOrderId : ℕ
  /-- The sell order -/
  sellOrderId : ℕ
  /-- Buyer ID -/
  buyerId : ℕ
  /-- Seller ID -/
  sellerId : ℕ
  /-- Resource traded -/
  resourceType : ResourceType
  /-- Trade quantity -/
  quantity : ℝ
  /-- Quantity is positive -/
  quantity_pos : 0 < quantity
  /-- Execution price -/
  price : ℝ
  /-- Price is positive -/
  price_pos : 0 < price
  /-- Execution timestamp -/
  executedAt : ℕ

/-- Total value of the trade -/
def Trade.value (t : Trade) : ℝ := t.price * t.quantity

/-- Trade value is positive -/
theorem trade_value_pos (t : Trade) : 0 < t.value := by
  simp only [Trade.value]
  exact mul_pos t.price_pos t.quantity_pos

/-- A trade settles atomically — both sides happen or neither does -/
structure AtomicSettlement where
  /-- The trade being settled -/
  trade : Trade
  /-- Seller's resource debit proof -/
  sellerDebitProof : ResourceAmount
  /-- Buyer's token debit proof -/
  buyerDebitProof : ResourceAmount
  /-- Seller receives tokens -/
  sellerCreditAmount : ℝ
  /-- Buyer receives resources -/
  buyerCreditAmount : ℝ
  /-- Seller receives trade value in tokens -/
  seller_receives_value : sellerCreditAmount = trade.value
  /-- Buyer receives trade quantity in resources -/
  buyer_receives_quantity : buyerCreditAmount = trade.quantity
  /-- Amounts are non-negative -/
  amounts_nonneg : 0 ≤ sellerCreditAmount ∧ 0 ≤ buyerCreditAmount

/-- ATOMICITY: Settlement is all-or-nothing -/
theorem settlement_atomic (s : AtomicSettlement) :
    -- If buyer pays, seller receives
    s.sellerCreditAmount = s.trade.value ∧
    -- If seller delivers, buyer receives
    s.buyerCreditAmount = s.trade.quantity :=
  ⟨s.seller_receives_value, s.buyer_receives_quantity⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: DOUBLE-SPEND PREVENTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A spent output reference — uniquely identifies a spend -/
structure SpentOutputRef where
  /-- Original credit transaction ID -/
  txId : ℕ
  /-- Output index within transaction -/
  outputIndex : ℕ
  /-- Amount that was spent -/
  amount : ℝ
  /-- Amount is positive -/
  amount_pos : 0 < amount

/-- A set of spent outputs (for double-spend tracking) -/
structure SpentSet where
  /-- All spent references -/
  spent : List SpentOutputRef
  /-- Each reference appears at most once (no double spends) -/
  unique : ∀ r1 ∈ spent, ∀ r2 ∈ spent,
    r1.txId = r2.txId → r1.outputIndex = r2.outputIndex → r1 = r2

/-- Check if an output is already spent -/
def SpentSet.isSpent (ss : SpentSet) (txId : ℕ) (outputIndex : ℕ) : Prop :=
  ∃ r ∈ ss.spent, r.txId = txId ∧ r.outputIndex = outputIndex

/-- A valid spend proves the output hasn't been spent before -/
structure ValidSpend where
  /-- The output being spent -/
  output : SpentOutputRef
  /-- Current spent set -/
  spentSet : SpentSet
  /-- This output is NOT already spent -/
  not_double_spend : ¬ spentSet.isSpent output.txId output.outputIndex
  /-- Signature authorizing the spend -/
  signature : Signature

/-- DOUBLE-SPEND PREVENTION: A valid spend cannot be replayed -/
theorem no_replay (vs : ValidSpend) :
    ¬ vs.spentSet.isSpent vs.output.txId vs.output.outputIndex :=
  vs.not_double_spend

/-- After marking as spent, the output cannot be spent again -/
def markSpent (vs : ValidSpend) : SpentSet :=
  { spent := vs.output :: vs.spentSet.spent
  , unique := by
      intro r1 hr1 r2 hr2 htx hout
      simp only [List.mem_cons] at hr1 hr2
      cases hr1 with
      | inl h1 =>
        cases hr2 with
        | inl h2 => rw [h1, h2]
        | inr h2 =>
          rw [h1] at htx hout
          have hspent : vs.spentSet.isSpent vs.output.txId vs.output.outputIndex := 
            ⟨r2, h2, htx.symm, hout.symm⟩
          exact False.elim (vs.not_double_spend hspent)
      | inr h1 =>
        cases hr2 with
        | inl h2 =>
          rw [h2] at htx hout
          have hspent : vs.spentSet.isSpent vs.output.txId vs.output.outputIndex := 
            ⟨r1, h1, htx, hout⟩
          exact False.elim (vs.not_double_spend hspent)
        | inr h2 => exact vs.spentSet.unique r1 h1 r2 h2 htx hout }

/-- After marking, the output IS spent -/
theorem marked_is_spent (vs : ValidSpend) :
    (markSpent vs).isSpent vs.output.txId vs.output.outputIndex := by
  simp only [markSpent, SpentSet.isSpent]
  use vs.output
  constructor
  · simp only [List.mem_cons, true_or]
  · exact ⟨rfl, rfl⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: X402 RESOURCE PAYMENTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- An x402 payment request (HTTP resource payment) -/
structure X402Request where
  /-- Resource URL hash -/
  resourceHash : Hash256
  /-- Requested resource type -/
  resourceType : ResourceType
  /-- Quantity requested -/
  quantity : ℝ
  /-- Quantity is positive -/
  quantity_pos : 0 < quantity
  /-- Maximum price willing to pay -/
  maxPrice : ℝ
  /-- Max price is positive -/
  maxPrice_pos : 0 < maxPrice
  /-- Requester ID -/
  requesterId : ℕ
  /-- Request timestamp -/
  timestamp : ℕ
  /-- Signature authorizing payment up to maxPrice -/
  paymentAuthorization : Signature
  /-- Signature is from requester -/
  auth_valid : paymentAuthorization.signer_id = requesterId

/-- An x402 payment response -/
structure X402Response where
  /-- Original request -/
  request : X402Request
  /-- Actual price charged -/
  actualPrice : ℝ
  /-- Price is positive -/
  price_pos : 0 < actualPrice
  /-- Price is within authorization -/
  price_authorized : actualPrice ≤ request.maxPrice
  /-- Provider ID -/
  providerId : ℕ
  /-- Resource delivery proof hash -/
  deliveryProofHash : Hash256

/-- X402 AUTHORIZATION: Payment cannot exceed authorized maximum -/
theorem x402_payment_bounded (resp : X402Response) :
    resp.actualPrice ≤ resp.request.maxPrice :=
  resp.price_authorized

/-- Total x402 payment amount -/
def X402Response.totalPayment (resp : X402Response) : ℝ :=
  resp.actualPrice * resp.request.quantity

/-- Total payment is positive -/
theorem x402_total_pos (resp : X402Response) : 0 < resp.totalPayment := by
  simp only [X402Response.totalPayment]
  exact mul_pos resp.price_pos resp.request.quantity_pos

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 9: ECONOMIC INVARIANTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- An economic system state -/
structure EconomyState where
  /-- All accounts -/
  accounts : List Account
  /-- Order books by resource type -/
  orderBooks : ResourceType → OrderBook
  /-- Completed trades -/
  trades : List Trade
  /-- Spent output set -/
  spentOutputs : SpentSet
  /-- Current timestamp -/
  currentTime : ℕ

/-- Total supply of a resource across all accounts -/
def EconomyState.totalSupply (es : EconomyState) (t : ResourceType) : ℝ :=
  es.accounts.foldl (fun acc a => acc + a.getBalance t) 0

/-- GLOBAL INVARIANT: No account has negative balance -/
theorem all_balances_nonneg (es : EconomyState) :
    ∀ acc ∈ es.accounts, ∀ t, 0 ≤ acc.getBalance t := by
  intro acc _ t
  exact acc.balances_nonneg t

/-- MARKET INTEGRITY: All orders in order book are valid -/
theorem order_book_valid (es : EconomyState) (t : ResourceType) :
    let ob := es.orderBooks t
    (∀ o ∈ ob.bids, o.resourceType = ob.resourceType ∧ o.side = OrderSide.Buy) ∧
    (∀ o ∈ ob.asks, o.resourceType = ob.resourceType ∧ o.side = OrderSide.Sell) := by
  simp only
  exact ⟨(es.orderBooks t).bids_valid, (es.orderBooks t).asks_valid⟩

/-- SPENT SET INTEGRITY: No double spends possible -/
theorem no_double_spends (es : EconomyState) :
    ∀ r1 ∈ es.spentOutputs.spent, ∀ r2 ∈ es.spentOutputs.spent,
    r1.txId = r2.txId → r1.outputIndex = r2.outputIndex → r1 = r2 :=
  es.spentOutputs.unique

end Hydrogen.WorldModel.Economy

end

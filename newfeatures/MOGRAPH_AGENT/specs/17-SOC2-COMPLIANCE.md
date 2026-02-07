# Specification 17: SOC2 Compliance
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-17  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Compliance Critical  

---

## 1. Overview

This specification defines SOC2 Type II compliance controls for the Lattice Lottie Generation Engine covering:

1. **Security** - Protection of data and systems
2. **Availability** - System uptime and reliability
3. **Processing Integrity** - Accurate and complete processing
4. **Confidentiality** - Protection of confidential information
5. **Privacy** - Personal information handling

---

## 2. Trust Service Criteria Mapping

### 2.1 Applicable Criteria

| Category | Criteria | Applicability |
|----------|----------|---------------|
| CC1 | Control Environment | ✓ Full |
| CC2 | Communication & Information | ✓ Full |
| CC3 | Risk Assessment | ✓ Full |
| CC4 | Monitoring Activities | ✓ Full |
| CC5 | Control Activities | ✓ Full |
| CC6 | Logical & Physical Access | ✓ Full |
| CC7 | System Operations | ✓ Full |
| CC8 | Change Management | ✓ Full |
| CC9 | Risk Mitigation | ✓ Full |
| A1 | Availability | ✓ Full |
| PI1 | Processing Integrity | ✓ Full |
| C1 | Confidentiality | ✓ Full |
| P1-P8 | Privacy | Partial |

---

## 3. Security Controls

### 3.1 Access Control (CC6)

```haskell
-- | Access control types
data AccessLevel
  = AccessPublic       -- Unauthenticated access
  | AccessUser         -- Authenticated user
  | AccessAdmin        -- System administrator
  | AccessAudit        -- Audit/compliance read-only
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | Permission types
data Permission
  = PermRead           -- Read data
  | PermWrite          -- Write data
  | PermDelete         -- Delete data
  | PermExecute        -- Execute operations
  | PermAdmin          -- Administrative actions
  deriving (Eq, Show, Enum, Bounded)

-- | Access control entry
data ACE = ACE
  { aceSubject    :: !SubjectId      -- User or service
  , aceResource   :: !ResourceId     -- Target resource
  , acePermission :: !Permission     -- Allowed action
  , aceCondition  :: !(Maybe Condition)  -- Optional condition
  , aceExpiry     :: !(Maybe UTCTime)    -- Optional expiration
  } deriving (Eq, Show)

-- | Check access permission
checkAccess :: SubjectId -> ResourceId -> Permission -> AccessControl -> Bool
checkAccess subject resource perm ac =
  any (matchesACE subject resource perm) (acEntries ac) &&
  not (any (matchesDeny subject resource perm) (acDenyList ac))

-- | Log access attempt
logAccessAttempt :: SubjectId -> ResourceId -> Permission -> Bool -> IO ()
logAccessAttempt subject resource perm granted = do
  timestamp <- getCurrentTime
  let entry = AccessLog
        { alTimestamp = timestamp
        , alSubject = subject
        , alResource = resource
        , alPermission = perm
        , alGranted = granted
        , alSourceIP = Nothing  -- Populated at runtime
        }
  appendAuditLog entry
```

### 3.2 Authentication (CC6.1)

```haskell
-- | Authentication methods
data AuthMethod
  = AuthAPIKey !Text               -- API key authentication
  | AuthJWT !JWTClaims            -- JWT token
  | AuthMTLS !Certificate         -- Mutual TLS
  | AuthServiceAccount !Text      -- Service account
  deriving (Eq, Show)

-- | Authenticate request
authenticate :: Request -> IO (Either AuthError AuthResult)
authenticate req = do
  method <- extractAuthMethod req
  case method of
    AuthAPIKey key -> validateAPIKey key
    AuthJWT claims -> validateJWT claims
    AuthMTLS cert -> validateCertificate cert
    AuthServiceAccount sa -> validateServiceAccount sa

-- | Authentication result
data AuthResult = AuthResult
  { arSubject     :: !SubjectId
  , arAccessLevel :: !AccessLevel
  , arExpiry      :: !UTCTime
  , arScopes      :: ![Scope]
  } deriving (Eq, Show)

-- | API key requirements
apiKeyRequirements :: APIKeyPolicy
apiKeyRequirements = APIKeyPolicy
  { akpMinLength = 32          -- Minimum 32 characters
  , akpEntropy = 256           -- 256 bits of entropy
  , akpRotationDays = 90       -- Rotate every 90 days
  , akpHashAlgorithm = SHA256  -- Stored as SHA256 hash
  }
```

### 3.3 Encryption (CC6.7)

```haskell
-- | Encryption requirements
data EncryptionPolicy = EncryptionPolicy
  { epAtRest       :: !EncryptionSpec    -- Data at rest
  , epInTransit    :: !EncryptionSpec    -- Data in transit
  , epKeyRotation  :: !Int               -- Key rotation (days)
  } deriving (Eq, Show)

-- | Encryption specification
data EncryptionSpec = EncryptionSpec
  { esAlgorithm    :: !Algorithm         -- AES-256-GCM
  , esKeySize      :: !Int               -- 256 bits
  , esMode         :: !Mode              -- GCM
  } deriving (Eq, Show)

-- | Default encryption policy
defaultEncryptionPolicy :: EncryptionPolicy
defaultEncryptionPolicy = EncryptionPolicy
  { epAtRest = EncryptionSpec AES256 256 GCM
  , epInTransit = EncryptionSpec TLS13 256 AEAD
  , epKeyRotation = 365  -- Annual key rotation
  }

-- | Encrypt data at rest
encryptAtRest :: ByteString -> IO EncryptedData
encryptAtRest plaintext = do
  key <- getCurrentEncryptionKey
  nonce <- generateNonce 12  -- 96-bit nonce for GCM
  let ciphertext = AES.encrypt key nonce plaintext
  pure $ EncryptedData
    { edCiphertext = ciphertext
    , edNonce = nonce
    , edKeyVersion = keyVersion key
    , edAlgorithm = "AES-256-GCM"
    }
```

---

## 4. Processing Integrity Controls

### 4.1 Input Validation (PI1.1)

```haskell
-- | Input validation configuration
data ValidationConfig = ValidationConfig
  { vcMaxInputSize    :: !Int          -- Maximum input size (bytes)
  , vcAllowedTypes    :: ![ContentType] -- Allowed content types
  , vcSchemaVersion   :: !Text         -- Schema version
  , vcStrictMode      :: !Bool         -- Strict validation
  } deriving (Eq, Show)

-- | Default validation config
defaultValidationConfig :: ValidationConfig
defaultValidationConfig = ValidationConfig
  { vcMaxInputSize = 10 * 1024 * 1024  -- 10 MB
  , vcAllowedTypes = [ApplicationJSON, TextPlain]
  , vcSchemaVersion = "1.0.0"
  , vcStrictMode = True
  }

-- | Validate input
validateInput :: ValidationConfig -> ByteString -> Either ValidationError ValidatedInput
validateInput cfg input = do
  -- Size check
  when (BS.length input > vcMaxInputSize cfg) $
    Left $ VEInputTooLarge (BS.length input) (vcMaxInputSize cfg)
  
  -- Parse JSON
  json <- case decode input of
    Just j -> Right j
    Nothing -> Left VEInvalidJSON
  
  -- Schema validation
  case validateSchema (vcSchemaVersion cfg) json of
    Left err -> Left $ VESchemaViolation err
    Right () -> Right $ ValidatedInput json

-- | Log validation result
logValidation :: ValidationResult -> IO ()
logValidation result = do
  timestamp <- getCurrentTime
  let entry = ValidationLog
        { vlTimestamp = timestamp
        , vlInputHash = hashInput (vrInput result)
        , vlResult = vrSuccess result
        , vlErrors = vrErrors result
        }
  appendAuditLog entry
```

### 4.2 Determinism Verification (PI1.2)

```haskell
-- | Determinism verification
data DeterminismCheck = DeterminismCheck
  { dcInput      :: !SAMDocument
  , dcOutputHash :: !ByteString      -- SHA256 of output
  , dcTimestamp  :: !UTCTime
  , dcIterations :: !Int             -- Number of runs checked
  } deriving (Eq, Show)

-- | Verify determinism
verifyDeterminism :: SAMDocument -> IO DeterminismResult
verifyDeterminism sam = do
  -- Run compilation multiple times
  results <- replicateM 3 $ do
    output <- compileSAM sam
    pure $ SHA256.hash $ encode output
  
  -- Check all hashes match
  let allMatch = all (== head results) results
  
  timestamp <- getCurrentTime
  pure $ DeterminismResult
    { drMatch = allMatch
    , drHash = head results
    , drTimestamp = timestamp
    , drIterations = length results
    }

-- | Determinism assertion in production
assertDeterminism :: SAMDocument -> LottieAnimation -> IO ()
assertDeterminism sam output = do
  let outputHash = SHA256.hash $ encode output
  
  -- Check against cached hash if exists
  cached <- lookupDeterminismCache sam
  case cached of
    Just cachedHash | cachedHash /= outputHash ->
      throwIO $ DeterminismViolation sam outputHash cachedHash
    _ -> do
      -- Cache the hash
      storeDeterminismCache sam outputHash
```

### 4.3 Data Integrity (PI1.3)

```haskell
-- | Data integrity record
data IntegrityRecord = IntegrityRecord
  { irDocumentId  :: !Text
  , irVersion     :: !Int
  , irContentHash :: !ByteString    -- SHA256
  , irTimestamp   :: !UTCTime
  , irAuthor      :: !SubjectId
  , irSignature   :: !ByteString    -- ECDSA signature
  } deriving (Eq, Show)

-- | Create integrity record
createIntegrityRecord :: Document -> SubjectId -> IO IntegrityRecord
createIntegrityRecord doc author = do
  timestamp <- getCurrentTime
  let contentHash = SHA256.hash $ encode doc
  signature <- signWithPrivateKey contentHash
  
  pure $ IntegrityRecord
    { irDocumentId = docId doc
    , irVersion = docVersion doc
    , irContentHash = contentHash
    , irTimestamp = timestamp
    , irAuthor = author
    , irSignature = signature
    }

-- | Verify integrity
verifyIntegrity :: Document -> IntegrityRecord -> Either IntegrityError ()
verifyIntegrity doc record = do
  -- Verify content hash
  let currentHash = SHA256.hash $ encode doc
  when (currentHash /= irContentHash record) $
    Left $ IEHashMismatch currentHash (irContentHash record)
  
  -- Verify signature
  unless (verifySignature (irContentHash record) (irSignature record)) $
    Left IEInvalidSignature
  
  pure ()
```

---

## 5. Audit Logging

### 5.1 Audit Log Structure

```haskell
-- | Audit event types
data AuditEventType
  = AETAccess          -- Access attempt
  | AETAuthentication  -- Authentication event
  | AETAuthorization   -- Authorization decision
  | AETDataChange      -- Data modification
  | AETSystemEvent     -- System event
  | AETSecurityEvent   -- Security-related event
  | AETComplianceEvent -- Compliance-related event
  deriving (Eq, Show, Enum, Bounded)

-- | Audit log entry
data AuditLogEntry = AuditLogEntry
  { aleId           :: !UUID              -- Unique event ID
  , aleTimestamp    :: !UTCTime           -- Event timestamp
  , aleEventType    :: !AuditEventType    -- Event category
  , aleActor        :: !Maybe SubjectId   -- Who performed action
  , aleResource     :: !Maybe ResourceId  -- Affected resource
  , aleAction       :: !Text              -- Action performed
  , aleOutcome      :: !Outcome           -- Success/failure
  , aleSourceIP     :: !Maybe Text        -- Source IP address
  , aleUserAgent    :: !Maybe Text        -- User agent
  , aleDetails      :: !Value             -- Additional details (JSON)
  , aleHash         :: !ByteString        -- Entry hash for integrity
  } deriving (Eq, Show, Generic)

-- | Outcome type
data Outcome = OutcomeSuccess | OutcomeFailure !Text
  deriving (Eq, Show)

-- | Write audit log entry
writeAuditLog :: AuditLogEntry -> IO ()
writeAuditLog entry = do
  -- Compute hash for integrity
  let entryWithHash = entry { aleHash = computeEntryHash entry }
  
  -- Write to primary log
  appendToAuditLog entryWithHash
  
  -- Write to backup (async)
  async $ appendToBackupLog entryWithHash
  
  -- Send to SIEM if configured
  whenM siemEnabled $
    sendToSIEM entryWithHash

-- | Compute entry hash (for tamper detection)
computeEntryHash :: AuditLogEntry -> ByteString
computeEntryHash entry =
  SHA256.hash $ encode entry { aleHash = "" }
```

### 5.2 Required Audit Events

| Event | Trigger | Data Captured |
|-------|---------|---------------|
| AUTH_SUCCESS | Successful auth | User, method, timestamp |
| AUTH_FAILURE | Failed auth | User, method, reason, IP |
| ACCESS_GRANTED | Permission check pass | User, resource, action |
| ACCESS_DENIED | Permission check fail | User, resource, action, reason |
| DATA_CREATE | New document | User, doc ID, hash |
| DATA_UPDATE | Document modified | User, doc ID, old/new hash |
| DATA_DELETE | Document deleted | User, doc ID, hash |
| CONFIG_CHANGE | Configuration modified | User, setting, old/new value |
| COMPILE_START | Compilation initiated | User, input hash |
| COMPILE_SUCCESS | Compilation completed | User, input hash, output hash |
| COMPILE_FAILURE | Compilation failed | User, input hash, error |
| KEY_ROTATION | Encryption key rotated | Old key ID, new key ID |
| SECURITY_ALERT | Security event detected | Event type, details |

### 5.3 Audit Log Retention

```haskell
-- | Retention policy
data RetentionPolicy = RetentionPolicy
  { rpHotStorage     :: !Int    -- Days in hot storage
  , rpWarmStorage    :: !Int    -- Days in warm storage
  , rpColdStorage    :: !Int    -- Days in cold storage
  , rpArchiveStorage :: !Int    -- Days in archive
  } deriving (Eq, Show)

-- | Default retention (SOC2 requires 1 year minimum)
defaultRetention :: RetentionPolicy
defaultRetention = RetentionPolicy
  { rpHotStorage = 30        -- 30 days hot
  , rpWarmStorage = 90       -- 90 days warm
  , rpColdStorage = 275      -- 275 days cold
  , rpArchiveStorage = 2555  -- 7 years archive
  }

-- | Total retention days
totalRetention :: RetentionPolicy -> Int
totalRetention rp = 
  rpHotStorage rp + rpWarmStorage rp + rpColdStorage rp + rpArchiveStorage rp
```

---

## 6. Change Management (CC8)

### 6.1 Change Control Process

```haskell
-- | Change request
data ChangeRequest = ChangeRequest
  { crId            :: !UUID
  , crTitle         :: !Text
  , crDescription   :: !Text
  , crType          :: !ChangeType
  , crRiskLevel     :: !RiskLevel
  , crRequestor     :: !SubjectId
  , crApprovers     :: ![SubjectId]
  , crStatus        :: !ChangeStatus
  , crCreatedAt     :: !UTCTime
  , crScheduledFor  :: !(Maybe UTCTime)
  , crAffectedSystems :: ![SystemId]
  , crRollbackPlan  :: !Text
  , crTestEvidence  :: ![TestEvidence]
  } deriving (Eq, Show, Generic)

-- | Change types
data ChangeType
  = CTEmergency     -- Critical fix, expedited approval
  | CTStandard      -- Normal change, full approval
  | CTMinor         -- Low-risk, single approval
  deriving (Eq, Show, Enum, Bounded)

-- | Risk levels
data RiskLevel
  = RLLow          -- Minimal impact
  | RLMedium       -- Moderate impact
  | RLHigh         -- Significant impact
  | RLCritical     -- Major impact
  deriving (Eq, Show, Enum, Bounded)

-- | Approval requirements by risk
approvalRequirements :: RiskLevel -> ApprovalRequirements
approvalRequirements = \case
  RLLow -> ApprovalRequirements 1 False False
  RLMedium -> ApprovalRequirements 2 True False
  RLHigh -> ApprovalRequirements 2 True True
  RLCritical -> ApprovalRequirements 3 True True

data ApprovalRequirements = ApprovalRequirements
  { arMinApprovers    :: !Int     -- Minimum approvers
  , arRequireTest     :: !Bool    -- Test evidence required
  , arRequireRollback :: !Bool    -- Rollback test required
  } deriving (Eq, Show)
```

### 6.2 Code Review Requirements

```haskell
-- | Code review policy
data CodeReviewPolicy = CodeReviewPolicy
  { crpMinReviewers       :: !Int           -- Minimum reviewers
  , crpRequireProofCheck  :: !Bool          -- Lean4 proof verification
  , crpRequireTestPass    :: !Bool          -- All tests must pass
  , crpRequireCoverage    :: !(Maybe Int)   -- Minimum coverage %
  , crpBlockingLabels     :: ![Text]        -- Labels that block merge
  } deriving (Eq, Show)

-- | Default review policy
defaultReviewPolicy :: CodeReviewPolicy
defaultReviewPolicy = CodeReviewPolicy
  { crpMinReviewers = 2
  , crpRequireProofCheck = True
  , crpRequireTestPass = True
  , crpRequireCoverage = Just 100
  , crpBlockingLabels = ["wip", "do-not-merge", "security-review-needed"]
  }

-- | Validate PR meets policy
validatePR :: PullRequest -> CodeReviewPolicy -> Either PolicyViolation ()
validatePR pr policy = do
  -- Check reviewer count
  when (length (prApprovals pr) < crpMinReviewers policy) $
    Left $ PVInsufficientReviewers (length $ prApprovals pr) (crpMinReviewers policy)
  
  -- Check proofs if required
  when (crpRequireProofCheck policy && not (prProofsVerified pr)) $
    Left PVProofsNotVerified
  
  -- Check tests
  when (crpRequireTestPass policy && not (prTestsPassing pr)) $
    Left PVTestsNotPassing
  
  -- Check coverage
  case crpRequireCoverage policy of
    Just minCov | prCoverage pr < minCov ->
      Left $ PVInsufficientCoverage (prCoverage pr) minCov
    _ -> pure ()
  
  -- Check blocking labels
  let blockers = filter (`elem` crpBlockingLabels policy) (prLabels pr)
  unless (null blockers) $
    Left $ PVBlockingLabels blockers
```

---

## 7. Monitoring & Alerting (CC4)

### 7.1 Metrics Collection

```haskell
-- | System metrics
data SystemMetrics = SystemMetrics
  { smTimestamp       :: !UTCTime
  , smCpuUsage        :: !Double          -- 0-100%
  , smMemoryUsage     :: !Double          -- 0-100%
  , smDiskUsage       :: !Double          -- 0-100%
  , smRequestRate     :: !Double          -- Requests/second
  , smErrorRate       :: !Double          -- Errors/second
  , smLatencyP50      :: !Double          -- 50th percentile (ms)
  , smLatencyP95      :: !Double          -- 95th percentile (ms)
  , smLatencyP99      :: !Double          -- 99th percentile (ms)
  , smActiveConnections :: !Int
  } deriving (Eq, Show, Generic)

-- | Application metrics
data AppMetrics = AppMetrics
  { amTimestamp          :: !UTCTime
  , amCompilationsTotal  :: !Int
  , amCompilationsSuccess :: !Int
  , amCompilationsFailed :: !Int
  , amAvgCompileTime     :: !Double       -- Milliseconds
  , amCacheHitRate       :: !Double       -- 0-100%
  , amLLMRequestsTotal   :: !Int
  , amLLMTokensUsed      :: !Int
  } deriving (Eq, Show, Generic)

-- | Collect metrics
collectMetrics :: IO (SystemMetrics, AppMetrics)
collectMetrics = do
  timestamp <- getCurrentTime
  sysMetrics <- collectSystemMetrics timestamp
  appMetrics <- collectAppMetrics timestamp
  
  -- Store for retention
  storeMetrics sysMetrics appMetrics
  
  -- Check thresholds
  checkAlertThresholds sysMetrics appMetrics
  
  pure (sysMetrics, appMetrics)
```

### 7.2 Alert Thresholds

| Metric | Warning | Critical | Action |
|--------|---------|----------|--------|
| CPU Usage | 70% | 90% | Scale/investigate |
| Memory Usage | 80% | 95% | Scale/investigate |
| Disk Usage | 70% | 90% | Cleanup/expand |
| Error Rate | 1% | 5% | Investigate |
| Latency P95 | 500ms | 2000ms | Investigate |
| Auth Failures | 10/min | 50/min | Security review |
| Compilation Failures | 5% | 20% | Investigate |

### 7.3 Alerting Implementation

```haskell
-- | Alert definition
data AlertRule = AlertRule
  { arId          :: !Text
  , arName        :: !Text
  , arMetric      :: !MetricName
  , arCondition   :: !AlertCondition
  , arSeverity    :: !AlertSeverity
  , arChannels    :: ![NotificationChannel]
  , arCooldown    :: !Int            -- Seconds between alerts
  } deriving (Eq, Show)

-- | Alert severity
data AlertSeverity = SevInfo | SevWarning | SevCritical | SevEmergency
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | Check and fire alerts
checkAlerts :: SystemMetrics -> AppMetrics -> IO [Alert]
checkAlerts sys app = do
  rules <- loadAlertRules
  alerts <- catMaybes <$> mapM (checkRule sys app) rules
  
  -- Record alerts
  mapM_ recordAlert alerts
  
  -- Send notifications
  mapM_ sendAlertNotifications alerts
  
  pure alerts

-- | Default alert rules
defaultAlertRules :: [AlertRule]
defaultAlertRules =
  [ AlertRule "cpu_high" "High CPU Usage" 
      (MetricCPU) (CondGreaterThan 90) SevCritical 
      [ChannelPagerDuty, ChannelSlack] 300
  
  , AlertRule "error_rate" "High Error Rate"
      (MetricErrorRate) (CondGreaterThan 0.05) SevCritical
      [ChannelPagerDuty, ChannelSlack] 60
  
  , AlertRule "auth_failures" "Authentication Failures Spike"
      (MetricAuthFailures) (CondGreaterThan 50) SevCritical
      [ChannelPagerDuty, ChannelSlack, ChannelSecurityTeam] 30
  ]
```

---

## 8. Compliance Evidence

### 8.1 Evidence Collection

```haskell
-- | Evidence types
data EvidenceType
  = ETAccessLog           -- Access control logs
  | ETAuditLog            -- Audit trail
  | ETChangeRecord        -- Change management records
  | ETTestResults         -- Test execution results
  | ETSecurityScan        -- Security scan results
  | ETReviewRecord        -- Code review records
  | ETIncidentReport      -- Incident reports
  | ETRiskAssessment      -- Risk assessment documents
  deriving (Eq, Show, Enum, Bounded)

-- | Evidence record
data Evidence = Evidence
  { evId          :: !UUID
  , evType        :: !EvidenceType
  , evPeriod      :: !(UTCTime, UTCTime)  -- Start, end
  , evContentHash :: !ByteString
  , evLocation    :: !Text               -- Storage location
  , evCreatedAt   :: !UTCTime
  , evCreatedBy   :: !SubjectId
  } deriving (Eq, Show, Generic)

-- | Generate compliance report
generateComplianceReport :: (UTCTime, UTCTime) -> IO ComplianceReport
generateComplianceReport period = do
  -- Collect all evidence
  evidence <- collectEvidence period
  
  -- Generate attestations
  attestations <- generateAttestations evidence
  
  -- Check control effectiveness
  controlStatus <- evaluateControls evidence
  
  pure $ ComplianceReport
    { crPeriod = period
    , crEvidence = evidence
    , crAttestations = attestations
    , crControlStatus = controlStatus
    , crExceptions = findExceptions controlStatus
    }
```

### 8.2 Control Attestation

| Control | Evidence | Frequency | Owner |
|---------|----------|-----------|-------|
| CC6.1 Access Control | Access logs | Daily | Security |
| CC6.7 Encryption | Key rotation logs | Monthly | Security |
| CC7.2 Monitoring | Alert logs | Daily | Operations |
| CC8.1 Change Management | Change records | Per change | Engineering |
| PI1.1 Input Validation | Validation logs | Daily | Engineering |
| PI1.4 Output Verification | Test results | Per release | QA |
| A1.2 Availability | Uptime metrics | Daily | Operations |

---

## 9. Incident Response

### 9.1 Incident Classification

```haskell
-- | Incident severity
data IncidentSeverity
  = ISLow          -- Minor impact, no SLA breach
  | ISMedium       -- Moderate impact, potential SLA breach
  | ISHigh         -- Major impact, SLA breach likely
  | ISCritical     -- Severe impact, immediate action required
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | Incident record
data Incident = Incident
  { incId           :: !UUID
  , incTitle        :: !Text
  , incDescription  :: !Text
  , incSeverity     :: !IncidentSeverity
  , incStatus       :: !IncidentStatus
  , incDetectedAt   :: !UTCTime
  , incResolvedAt   :: !(Maybe UTCTime)
  , incAssignee     :: !(Maybe SubjectId)
  , incAffectedUsers :: !Int
  , incRootCause    :: !(Maybe Text)
  , incResolution   :: !(Maybe Text)
  , incTimeline     :: ![IncidentEvent]
  } deriving (Eq, Show, Generic)

-- | Response time SLAs
responseTimeSLA :: IncidentSeverity -> Int  -- Minutes
responseTimeSLA = \case
  ISCritical -> 15
  ISHigh -> 30
  ISMedium -> 120
  ISLow -> 480
```

---

## 10. Constraint Summary

| Control | Requirement | Implementation |
|---------|-------------|----------------|
| Password Length | ≥12 characters | Enforced in AuthPolicy |
| API Key Entropy | 256 bits | Enforced in KeyGen |
| Key Rotation | ≤365 days | Automated rotation |
| Session Timeout | ≤24 hours | JWT expiry |
| Audit Retention | ≥1 year | 7 year policy |
| Backup Frequency | Daily | Automated |
| Recovery Time | ≤4 hours | Tested quarterly |
| Uptime SLA | 99.9% | Monitored |

---

*End of Specification 17*

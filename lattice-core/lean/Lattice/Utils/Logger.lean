/-
  Lattice.Utils.Logger - Logging utility

  Centralized logging with configurable log levels.
  In production, only warnings and errors are shown.
  In development, all logs are shown.

  Source: ui/src/utils/logger.ts
-/

namespace Lattice.Utils.Logger

/-! ## Log Levels -/

/-- Log level enumeration -/
inductive LogLevel where
  | debug
  | info
  | warn
  | error
  | none
  deriving Repr, BEq, Ord

/-- Convert log level to string -/
def LogLevel.toString : LogLevel → String
  | .debug => "DEBUG"
  | .info => "INFO"
  | .warn => "WARN"
  | .error => "ERROR"
  | .none => "NONE"

instance : ToString LogLevel where
  toString := LogLevel.toString

/-- Log level priority (lower number = more verbose) -/
def LogLevel.priority : LogLevel → Nat
  | .debug => 0
  | .info => 1
  | .warn => 2
  | .error => 3
  | .none => 4

/-! ## Logger Configuration -/

/-- Logger configuration -/
structure LoggerConfig where
  level : LogLevel
  prefix : String
  enableTimestamp : Bool
  deriving Repr, BEq

/-- Default logger configuration -/
def defaultConfig : LoggerConfig :=
  { level := LogLevel.warn
  , prefix := "[Lattice]"
  , enableTimestamp := false }

/-- Development configuration (all logs shown) -/
def devConfig : LoggerConfig :=
  { level := LogLevel.debug
  , prefix := "[Lattice]"
  , enableTimestamp := true }

/-! ## Log Entry -/

/-- A log entry ready to be outputted -/
structure LogEntry where
  level : LogLevel
  context : String
  message : String
  timestamp : Option String
  prefix : String
  deriving Repr, BEq

/-- Create a log entry -/
def mkLogEntry (level : LogLevel) (context message : String)
               (config : LoggerConfig) (timestamp : Option String := none) : LogEntry :=
  { level
  , context
  , message
  , timestamp := if config.enableTimestamp then timestamp else none
  , prefix := config.prefix }

/-- Format a log entry as a string -/
def LogEntry.format (entry : LogEntry) : String :=
  let parts : List String := []
  let parts := match entry.timestamp with
    | some ts => parts ++ [s!"[{ts}]"]
    | none => parts
  let parts := if entry.prefix.isEmpty then parts else parts ++ [entry.prefix]
  let parts := if entry.context.isEmpty then parts else parts ++ [s!"[{entry.context}]"]
  let parts := parts ++ [entry.message]
  " ".intercalate parts

/-! ## Logger -/

/-- Should this log level be shown given the config? -/
def shouldLog (level : LogLevel) (config : LoggerConfig) : Bool :=
  level.priority >= config.level.priority

/-- A logger instance with a specific context -/
structure Logger where
  context : String
  config : LoggerConfig
  deriving Repr

/-- Create a logger with a specific context -/
def createLogger (context : String) (config : LoggerConfig := defaultConfig) : Logger :=
  { context, config }

/-- Update logger config -/
def Logger.withConfig (logger : Logger) (config : LoggerConfig) : Logger :=
  { logger with config }

/-- Set log level -/
def Logger.setLevel (logger : Logger) (level : LogLevel) : Logger :=
  { logger with config := { logger.config with level } }

/-! ## Logging Functions (Pure) -/

/-- Create a debug log entry (returns None if level too low) -/
def Logger.debugEntry (logger : Logger) (message : String) : Option LogEntry :=
  if shouldLog .debug logger.config
  then some (mkLogEntry .debug logger.context message logger.config)
  else none

/-- Create an info log entry (returns None if level too low) -/
def Logger.infoEntry (logger : Logger) (message : String) : Option LogEntry :=
  if shouldLog .info logger.config
  then some (mkLogEntry .info logger.context message logger.config)
  else none

/-- Create a warn log entry (returns None if level too low) -/
def Logger.warnEntry (logger : Logger) (message : String) : Option LogEntry :=
  if shouldLog .warn logger.config
  then some (mkLogEntry .warn logger.context message logger.config)
  else none

/-- Create an error log entry (returns None if level too low) -/
def Logger.errorEntry (logger : Logger) (message : String) : Option LogEntry :=
  if shouldLog .error logger.config
  then some (mkLogEntry .error logger.context message logger.config)
  else none

/-! ## Pre-configured Loggers -/

/-- Default app logger -/
def appLogger : Logger := createLogger "App"

/-- Store logger -/
def storeLogger : Logger := createLogger "Store"

/-- Engine logger -/
def engineLogger : Logger := createLogger "Engine"

/-- Layer logger -/
def layerLogger : Logger := createLogger "Layer"

/-- Render logger -/
def renderLogger : Logger := createLogger "Render"

/-- Audio logger -/
def audioLogger : Logger := createLogger "Audio"

/-- Export logger -/
def exportLogger : Logger := createLogger "Export"

end Lattice.Utils.Logger

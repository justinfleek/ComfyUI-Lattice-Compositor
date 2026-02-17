/**
 * Logging Utility
 *
 * Centralized logging with configurable log levels.
 * In production, only warnings and errors are shown.
 * In development, all logs are shown.
 */

export type LogLevel = "debug" | "info" | "warn" | "error" | "none";

interface LoggerConfig {
  level: LogLevel;
  prefix: string;
  enableTimestamp: boolean;
}

const LOG_LEVELS: Record<LogLevel, number> = {
  debug: 0,
  info: 1,
  warn: 2,
  error: 3,
  none: 4,
};

// Default configuration - can be overridden
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
const importMetaEnv = (import.meta != null && typeof import.meta === "object" && "env" in import.meta && import.meta.env != null && typeof import.meta.env === "object") ? import.meta.env : undefined;
const envDev = (importMetaEnv != null && typeof importMetaEnv === "object" && "DEV" in importMetaEnv && typeof importMetaEnv.DEV === "boolean" && importMetaEnv.DEV) ? true : false;
const config: LoggerConfig = {
  level: envDev ? "debug" : "warn",
  prefix: "[Lattice]",
  enableTimestamp: false,
};

/**
 * Set the global log level
 */
export function setLogLevel(level: LogLevel): void {
  config.level = level;
}

/**
 * Set the log prefix
 */
export function setLogPrefix(prefix: string): void {
  config.prefix = prefix;
}

/**
 * Enable/disable timestamps in logs
 */
export function setTimestampEnabled(enabled: boolean): void {
  config.enableTimestamp = enabled;
}

/**
 * Get current log level
 */
export function getLogLevel(): LogLevel {
  return config.level;
}

function shouldLog(level: LogLevel): boolean {
  return LOG_LEVELS[level] >= LOG_LEVELS[config.level];
}

function formatMessage(
  _level: string,
  context: string,
  message: string,
): string {
  const parts: string[] = [];

  if (config.enableTimestamp) {
    parts.push(`[${new Date().toISOString()}]`);
  }

  if (config.prefix) {
    parts.push(config.prefix);
  }

  if (context) {
    parts.push(`[${context}]`);
  }

  parts.push(message);

  return parts.join(" ");
}

/**
 * Create a logger instance with a specific context
 */
export function createLogger(context: string) {
  return {
    debug(message: string, ...args: unknown[]): void {
      if (shouldLog("debug")) {
        console.log(formatMessage("DEBUG", context, message), ...args);
      }
    },

    info(message: string, ...args: unknown[]): void {
      if (shouldLog("info")) {
        console.info(formatMessage("INFO", context, message), ...args);
      }
    },

    warn(message: string, ...args: unknown[]): void {
      if (shouldLog("warn")) {
        console.warn(formatMessage("WARN", context, message), ...args);
      }
    },

    error(message: string, ...args: unknown[]): void {
      if (shouldLog("error")) {
        console.error(formatMessage("ERROR", context, message), ...args);
      }
    },

    /**
     * Log with a specific level
     */
    log(level: LogLevel, message: string, ...args: unknown[]): void {
      switch (level) {
        case "debug":
          this.debug(message, ...args);
          break;
        case "info":
          this.info(message, ...args);
          break;
        case "warn":
          this.warn(message, ...args);
          break;
        case "error":
          this.error(message, ...args);
          break;
      }
    },

    /**
     * Group related logs (collapsible in console)
     */
    group(label: string): void {
      if (shouldLog("debug")) {
        console.group(formatMessage("", context, label));
      }
    },

    groupEnd(): void {
      if (shouldLog("debug")) {
        console.groupEnd();
      }
    },

    /**
     * Log a table (useful for arrays/objects)
     * Accepts any serializable data structure
     */
    table(data: unknown): void {
      if (shouldLog("debug")) {
        console.log(formatMessage("", context, "Table:"));
        console.table(data);
      }
    },

    /**
     * Measure time for an operation
     */
    time(label: string): void {
      if (shouldLog("debug")) {
        console.time(`${config.prefix} [${context}] ${label}`);
      }
    },

    timeEnd(label: string): void {
      if (shouldLog("debug")) {
        console.timeEnd(`${config.prefix} [${context}] ${label}`);
      }
    },
  };
}

// Default logger instance
export const logger = createLogger("App");

// Pre-configured loggers for common modules
export const storeLogger = createLogger("Store");
export const engineLogger = createLogger("Engine");
export const layerLogger = createLogger("Layer");
export const renderLogger = createLogger("Render");
export const audioLogger = createLogger("Audio");
export const exportLogger = createLogger("Export");

export default logger;

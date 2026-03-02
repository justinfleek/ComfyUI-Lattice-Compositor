/**
 * Property tests for ui/src/types/dataAsset.ts
 * Tests: isJSONAsset, isCSVAsset, isSupportedDataFile, getDataFileType
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  isJSONAsset,
  isCSVAsset,
  isSupportedDataFile,
  getDataFileType,
  type DataAsset,
  type JSONDataAsset,
  type CSVDataAsset,
} from "@/types/dataAsset";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // test // fixtures
// ════════════════════════════════════════════════════════════════════════════

function createJSONAsset(): JSONDataAsset {
  return {
    id: "test-json",
    name: "Test JSON",
    type: "json",
    filePath: "/path/to/file.json",
    sourceData: { key: "value" },
    lastModified: Date.now(),
    rawContent: '{"key":"value"}',
  };
}

function createMGJSONAsset(): JSONDataAsset {
  return {
    id: "test-mgjson",
    name: "Test MGJSON",
    type: "mgjson",
    filePath: "/path/to/file.mgjson",
    sourceData: { key: "value" },
    lastModified: Date.now(),
    rawContent: '{"key":"value"}',
  };
}

function createCSVAsset(): CSVDataAsset {
  return {
    id: "test-csv",
    name: "Test CSV",
    type: "csv",
    filePath: "/path/to/file.csv",
    headers: ["col1", "col2"],
    rows: [["a", "b"], ["c", "d"]],
    numRows: 3,
    numColumns: 2,
    lastModified: Date.now(),
    rawContent: 'col1,col2\na,b\nc,d',
  };
}

function createTSVAsset(): CSVDataAsset {
  return {
    id: "test-tsv",
    name: "Test TSV",
    type: "tsv",
    filePath: "/path/to/file.tsv",
    headers: ["col1", "col2"],
    rows: [["a", "b"]],
    numRows: 2,
    numColumns: 2,
    lastModified: Date.now(),
    rawContent: 'col1\tcol2\na\tb',
  };
}

// ════════════════════════════════════════════════════════════════════════════
// isJSONAsset TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: isJSONAsset", () => {
  it("returns true for json type", () => {
    const asset = createJSONAsset();
    expect(isJSONAsset(asset)).toBe(true);
  });

  it("returns true for mgjson type", () => {
    const asset = createMGJSONAsset();
    expect(isJSONAsset(asset)).toBe(true);
  });

  it("returns false for csv type", () => {
    const asset = createCSVAsset();
    expect(isJSONAsset(asset)).toBe(false);
  });

  it("returns false for tsv type", () => {
    const asset = createTSVAsset();
    expect(isJSONAsset(asset)).toBe(false);
  });

  it("is mutually exclusive with isCSVAsset for non-JSON types", () => {
    const csvAsset = createCSVAsset();
    expect(isJSONAsset(csvAsset)).toBe(false);
    expect(isCSVAsset(csvAsset)).toBe(true);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// isCSVAsset TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: isCSVAsset", () => {
  it("returns true for csv type", () => {
    const asset = createCSVAsset();
    expect(isCSVAsset(asset)).toBe(true);
  });

  it("returns true for tsv type", () => {
    const asset = createTSVAsset();
    expect(isCSVAsset(asset)).toBe(true);
  });

  it("returns false for json type", () => {
    const asset = createJSONAsset();
    expect(isCSVAsset(asset)).toBe(false);
  });

  it("returns false for mgjson type", () => {
    const asset = createMGJSONAsset();
    expect(isCSVAsset(asset)).toBe(false);
  });

  it("is mutually exclusive with isJSONAsset", () => {
    const jsonAsset = createJSONAsset();
    const csvAsset = createCSVAsset();
    
    // If JSON, not CSV
    expect(isJSONAsset(jsonAsset)).toBe(true);
    expect(isCSVAsset(jsonAsset)).toBe(false);
    
    // If CSV, not JSON
    expect(isJSONAsset(csvAsset)).toBe(false);
    expect(isCSVAsset(csvAsset)).toBe(true);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// isSupportedDataFile TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: isSupportedDataFile", () => {
  it("returns true for .json files", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        (basename) => {
          expect(isSupportedDataFile(`${basename}.json`)).toBe(true);
          expect(isSupportedDataFile(`${basename}.JSON`)).toBe(true);
        }
      )
    );
  });

  it("returns true for .csv files", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        (basename) => {
          expect(isSupportedDataFile(`${basename}.csv`)).toBe(true);
          expect(isSupportedDataFile(`${basename}.CSV`)).toBe(true);
        }
      )
    );
  });

  it("returns true for .tsv files", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        (basename) => {
          expect(isSupportedDataFile(`${basename}.tsv`)).toBe(true);
          expect(isSupportedDataFile(`${basename}.TSV`)).toBe(true);
        }
      )
    );
  });

  it("returns true for .mgjson files", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        (basename) => {
          expect(isSupportedDataFile(`${basename}.mgjson`)).toBe(true);
          expect(isSupportedDataFile(`${basename}.MGJSON`)).toBe(true);
        }
      )
    );
  });

  it("returns false for unsupported extensions", () => {
    expect(isSupportedDataFile("file.txt")).toBe(false);
    expect(isSupportedDataFile("file.xml")).toBe(false);
    expect(isSupportedDataFile("file.mp4")).toBe(false);
    expect(isSupportedDataFile("file.png")).toBe(false);
    expect(isSupportedDataFile("file.js")).toBe(false);
  });

  it("returns false for files without extension", () => {
    expect(isSupportedDataFile("filename")).toBe(false);
  });

  it("is case insensitive", () => {
    expect(isSupportedDataFile("data.JSON")).toBe(true);
    expect(isSupportedDataFile("data.Json")).toBe(true);
    expect(isSupportedDataFile("data.CSV")).toBe(true);
    expect(isSupportedDataFile("data.Csv")).toBe(true);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// getDataFileType TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: getDataFileType", () => {
  it("returns 'json' for .json files", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        (basename) => {
          expect(getDataFileType(`${basename}.json`)).toBe("json");
          expect(getDataFileType(`${basename}.JSON`)).toBe("json");
        }
      )
    );
  });

  it("returns 'csv' for .csv files", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        (basename) => {
          expect(getDataFileType(`${basename}.csv`)).toBe("csv");
          expect(getDataFileType(`${basename}.CSV`)).toBe("csv");
        }
      )
    );
  });

  it("returns 'tsv' for .tsv files", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        (basename) => {
          expect(getDataFileType(`${basename}.tsv`)).toBe("tsv");
          expect(getDataFileType(`${basename}.TSV`)).toBe("tsv");
        }
      )
    );
  });

  it("returns 'mgjson' for .mgjson files", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        (basename) => {
          expect(getDataFileType(`${basename}.mgjson`)).toBe("mgjson");
          expect(getDataFileType(`${basename}.MGJSON`)).toBe("mgjson");
        }
      )
    );
  });

  it("returns null for unsupported extensions", () => {
    expect(getDataFileType("file.txt")).toBeNull();
    expect(getDataFileType("file.xml")).toBeNull();
    expect(getDataFileType("file.mp4")).toBeNull();
  });

  it("returns null for files without extension", () => {
    expect(getDataFileType("filename")).toBeNull();
  });

  it("is consistent with isSupportedDataFile", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        fc.constantFrom(".json", ".csv", ".tsv", ".mgjson", ".txt", ".xml", ""),
        (basename, ext) => {
          const filename = basename + ext;
          const fileType = getDataFileType(filename);
          const isSupported = isSupportedDataFile(filename);
          
          // If getDataFileType returns non-null, isSupportedDataFile should return true
          if (fileType !== null) {
            expect(isSupported).toBe(true);
          }
          // If isSupportedDataFile returns false, getDataFileType should return null
          if (!isSupported) {
            expect(fileType).toBeNull();
          }
        }
      )
    );
  });
});

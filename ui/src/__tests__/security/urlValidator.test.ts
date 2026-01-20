/**
 * URL Validator Tests
 *
 * Tests security validation for URLs to prevent XSS, code execution,
 * and other URL-based attacks.
 */

import { describe, expect, it } from "vitest";
import {
  extractAndValidateURLs,
  isTrustedDomain,
  sanitizeURLForHTML,
  validateURL,
  validateURLs,
} from "@/services/security/urlValidator";

describe("URL Validator - Security", () => {
  describe("validateURL - Blocked Protocols", () => {
    it("should BLOCK javascript: URLs", () => {
      const result = validateURL("javascript:alert(1)");
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
      expect(result.error).toContain("javascript:");
    });

    it("should BLOCK vbscript: URLs", () => {
      const result = validateURL('vbscript:msgbox("test")');
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
    });

    it("should BLOCK file: URLs", () => {
      const result = validateURL("file:///etc/passwd");
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
    });

    it("should BLOCK ftp: URLs", () => {
      const result = validateURL("ftp://ftp.example.com/file.txt");
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
    });

    it("should BLOCK chrome: URLs", () => {
      const result = validateURL("chrome://settings");
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
    });

    it("should BLOCK about: URLs", () => {
      const result = validateURL("about:blank");
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
    });

    it("should BLOCK ws: WebSocket URLs for assets", () => {
      const result = validateURL("ws://example.com/socket");
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
    });
  });

  describe("validateURL - Data URLs", () => {
    it("should BLOCK data:text/html (XSS vector)", () => {
      const result = validateURL("data:text/html,<script>alert(1)</script>");
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
      expect(result.error).toContain("blocked content type");
    });

    it("should BLOCK data:application/javascript", () => {
      const result = validateURL("data:application/javascript,alert(1)");
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
    });

    it("should BLOCK data:image/svg+xml with script tags", () => {
      const result = validateURL(
        "data:image/svg+xml,<svg><script>alert(1)</script></svg>",
      );
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
    });

    it("should ALLOW data:image/png", () => {
      const result = validateURL("data:image/png;base64,iVBORw0KGgo=");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
    });

    it("should ALLOW data:image/jpeg", () => {
      const result = validateURL("data:image/jpeg;base64,/9j/4AAQ");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
    });

    it("should ALLOW data:image/svg+xml without script", () => {
      const result = validateURL(
        'data:image/svg+xml,<svg><rect width="100" height="100"/></svg>',
      );
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
    });

    it("should ALLOW data:audio/mp3", () => {
      const result = validateURL("data:audio/mp3;base64,//uQ");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
    });

    it("should ALLOW data:video/mp4", () => {
      const result = validateURL("data:video/mp4;base64,AAAA");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
    });

    it("should ALLOW data:application/json", () => {
      const result = validateURL('data:application/json,{"test":true}');
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
    });

    it("should BLOCK unknown data MIME types", () => {
      const result = validateURL("data:application/x-unknown,test");
      expect(result.valid).toBe(false);
      expect(result.riskLevel).toBe("blocked");
    });
  });

  describe("validateURL - Safe Protocols", () => {
    it("should ALLOW https: URLs", () => {
      const result = validateURL("https://example.com/image.png");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
      expect(result.protocol).toBe("https:");
    });

    it("should ALLOW http: URLs with warning", () => {
      const result = validateURL("http://example.com/image.png");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("warning");
      expect(result.warning).toContain("Unencrypted");
    });

    it("should ALLOW blob: URLs", () => {
      const result = validateURL("blob:https://example.com/abc-123");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
    });

    it("should ALLOW relative URLs starting with /", () => {
      const result = validateURL("/images/photo.png");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
      expect(result.protocol).toBe("relative");
    });

    it("should ALLOW relative URLs starting with ./", () => {
      const result = validateURL("./assets/image.png");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
    });

    it("should ALLOW relative URLs starting with ../", () => {
      const result = validateURL("../images/photo.png");
      expect(result.valid).toBe(true);
      expect(result.riskLevel).toBe("safe");
    });
  });

  describe("validateURL - Edge Cases", () => {
    it("should BLOCK empty string and whitespace", () => {
      // Function signature requires string, so test with empty/whitespace strings
      expect(validateURL("").valid).toBe(false);
      expect(validateURL("   ").valid).toBe(false);
    });

    it("should BLOCK empty string", () => {
      expect(validateURL("").valid).toBe(false);
      expect(validateURL("   ").valid).toBe(false);
    });

    it("should BLOCK extremely long URLs (DoS prevention)", () => {
      const longUrl = `https://example.com/${"a".repeat(3_000_000)}`;
      expect(validateURL(longUrl).valid).toBe(false);
    });

    it("should BLOCK unknown protocols", () => {
      const result = validateURL("custom://something");
      expect(result.valid).toBe(false);
      expect(result.error).toContain("Unknown protocol");
    });

    it("should handle case-insensitive protocol check", () => {
      expect(validateURL("JAVASCRIPT:alert(1)").valid).toBe(false);
      expect(validateURL("JavaScript:alert(1)").valid).toBe(false);
      expect(validateURL("HTTPS://example.com").valid).toBe(true);
    });
  });

  describe("sanitizeURLForHTML", () => {
    it("should return null for blocked URLs", () => {
      expect(sanitizeURLForHTML("javascript:alert(1)")).toBeNull();
    });

    it("should escape HTML special characters", () => {
      const result = sanitizeURLForHTML(
        'https://example.com?foo=<bar>&x="test"',
      );
      expect(result).not.toContain("<");
      expect(result).not.toContain(">");
      expect(result).not.toContain('"');
      expect(result).toContain("&lt;");
      expect(result).toContain("&gt;");
      expect(result).toContain("&quot;");
    });
  });

  describe("validateURLs - Batch Validation", () => {
    it("should validate multiple URLs and return map", () => {
      const urls = [
        "https://safe.com/image.png",
        "javascript:alert(1)",
        "data:image/png;base64,ABC",
      ];
      const results = validateURLs(urls);

      expect(results.get(urls[0])?.valid).toBe(true);
      expect(results.get(urls[1])?.valid).toBe(false);
      expect(results.get(urls[2])?.valid).toBe(true);
    });
  });

  describe("isTrustedDomain", () => {
    const trustedDomains = ["example.com", "cdn.trusted.org"];

    it("should match exact domain", () => {
      expect(isTrustedDomain("https://example.com/path", trustedDomains)).toBe(
        true,
      );
    });

    it("should match subdomain", () => {
      expect(
        isTrustedDomain("https://api.example.com/path", trustedDomains),
      ).toBe(true);
      expect(
        isTrustedDomain("https://static.cdn.trusted.org/file", trustedDomains),
      ).toBe(true);
    });

    it("should NOT match partial domain name", () => {
      expect(
        isTrustedDomain("https://fakeexample.com/path", trustedDomains),
      ).toBe(false);
    });

    it("should return false for invalid URLs", () => {
      expect(isTrustedDomain("not-a-url", trustedDomains)).toBe(false);
    });
  });

  describe("extractAndValidateURLs", () => {
    it("should extract and validate URLs from text", () => {
      const text = `
        Check out https://safe.com/image.png
        and also http://another.com/video.mp4
        Also here is data:image/png;base64,ABC
      `;

      const results = extractAndValidateURLs(text);

      // Extracts https, http, and data URLs
      expect(results.length).toBe(3);
      expect(results[0].valid).toBe(true); // https
      expect(results[1].valid).toBe(true); // http (with warning)
      expect(results[2].valid).toBe(true); // data:image/png is safe
    });

    it("should identify dangerous data URLs when extracted", () => {
      const text = `data:text/html,<script>alert(1)</script>`;
      const results = extractAndValidateURLs(text);

      expect(results.length).toBe(1);
      expect(results[0].valid).toBe(false);
      expect(results[0].riskLevel).toBe("blocked");
    });
  });
});

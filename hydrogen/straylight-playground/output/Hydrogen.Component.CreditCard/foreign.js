// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // creditcard
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Credit card input handling and validation

/**
 * Card type patterns
 */
const cardPatterns = {
  visa: /^4/,
  mastercard: /^5[1-5]|^2[2-7]/,
  amex: /^3[47]/,
  discover: /^6(?:011|5)/,
  dinersclub: /^3(?:0[0-5]|[68])/,
  jcb: /^35/,
  unionpay: /^62/,
};

/**
 * Detect card type from number
 */
const detectCardType = (number) => {
  const digits = number.replace(/\D/g, "");
  if (cardPatterns.visa.test(digits)) return "Visa";
  if (cardPatterns.mastercard.test(digits)) return "Mastercard";
  if (cardPatterns.amex.test(digits)) return "Amex";
  if (cardPatterns.discover.test(digits)) return "Discover";
  if (cardPatterns.dinersclub.test(digits)) return "DinersClub";
  if (cardPatterns.jcb.test(digits)) return "JCB";
  if (cardPatterns.unionpay.test(digits)) return "UnionPay";
  return "Unknown";
};

/**
 * Initialize credit card input
 */
export const initCreditCardImpl = (container, onChange) => {
  const cardInput = container.querySelector('[autocomplete="cc-number"]');
  const expiryInput = container.querySelector('[autocomplete="cc-exp"]');
  const cvvInput = container.querySelector('[autocomplete="cc-csc"]');
  const nameInput = container.querySelector('[autocomplete="cc-name"]');

  const getValue = () => ({
    cardNumber: cardInput?.value.replace(/\D/g, "") || "",
    expiryDate: expiryInput?.value || "",
    cvv: cvvInput?.value || "",
    cardholderName: nameInput?.value || "",
    cardType: detectCardType(cardInput?.value || ""),
    isValid: validateCard(cardInput?.value, expiryInput?.value, cvvInput?.value),
  });

  const handleCardInput = (e) => {
    let value = e.target.value.replace(/\D/g, "");
    const cardType = detectCardType(value);

    // Format based on card type
    if (cardType === "Amex") {
      // 4-6-5 format for Amex
      value = value.slice(0, 15);
      let formatted = "";
      if (value.length > 0) formatted += value.slice(0, 4);
      if (value.length > 4) formatted += " " + value.slice(4, 10);
      if (value.length > 10) formatted += " " + value.slice(10, 15);
      e.target.value = formatted;
    } else {
      // 4-4-4-4 format for others
      value = value.slice(0, 16);
      let formatted = "";
      for (let i = 0; i < value.length; i += 4) {
        if (i > 0) formatted += " ";
        formatted += value.slice(i, i + 4);
      }
      e.target.value = formatted;
    }

    onChange(getValue())();
  };

  const handleExpiryInput = (e) => {
    let value = e.target.value.replace(/\D/g, "");
    value = value.slice(0, 4);

    if (value.length >= 2) {
      let month = parseInt(value.slice(0, 2), 10);
      if (month > 12) month = 12;
      if (month < 1 && value.length >= 2) month = 1;
      value =
        String(month).padStart(2, "0") + (value.length > 2 ? value.slice(2) : "");
    }

    if (value.length > 2) {
      value = value.slice(0, 2) + "/" + value.slice(2);
    }

    e.target.value = value;
    onChange(getValue())();
  };

  const handleCvvInput = (e) => {
    const cardType = detectCardType(cardInput?.value || "");
    const maxLen = cardType === "Amex" ? 4 : 3;
    e.target.value = e.target.value.replace(/\D/g, "").slice(0, maxLen);
    onChange(getValue())();
  };

  const handleNameInput = () => {
    onChange(getValue())();
  };

  // Attach event listeners
  if (cardInput) {
    cardInput.addEventListener("input", handleCardInput);
  }
  if (expiryInput) {
    expiryInput.addEventListener("input", handleExpiryInput);
  }
  if (cvvInput) {
    cvvInput.addEventListener("input", handleCvvInput);
  }
  if (nameInput) {
    nameInput.addEventListener("input", handleNameInput);
  }

  return {
    container,
    cleanup: () => {
      if (cardInput) cardInput.removeEventListener("input", handleCardInput);
      if (expiryInput) expiryInput.removeEventListener("input", handleExpiryInput);
      if (cvvInput) cvvInput.removeEventListener("input", handleCvvInput);
      if (nameInput) nameInput.removeEventListener("input", handleNameInput);
    },
  };
};

/**
 * Validate all card fields
 */
const validateCard = (number, expiry, cvv) => {
  const digits = (number || "").replace(/\D/g, "");
  const cardType = detectCardType(digits);

  const validNumber = luhnCheck(digits) && digits.length >= 13;
  const validExpiry = validateExpiry(expiry);
  const validCvv = validateCvv(cvv, cardType);

  return validNumber && validExpiry && validCvv;
};

/**
 * Luhn algorithm check
 */
const luhnCheck = (number) => {
  if (!number || number.length < 13) return false;

  let sum = 0;
  let isEven = false;

  for (let i = number.length - 1; i >= 0; i--) {
    let digit = parseInt(number[i], 10);

    if (isEven) {
      digit *= 2;
      if (digit > 9) digit -= 9;
    }

    sum += digit;
    isEven = !isEven;
  }

  return sum % 10 === 0;
};

/**
 * Export Luhn check for PureScript
 */
export const luhnCheckImpl = (number) => luhnCheck(number);

/**
 * Validate expiry date
 */
const validateExpiry = (expiry) => {
  if (!expiry || !expiry.includes("/")) return false;

  const [monthStr, yearStr] = expiry.split("/");
  const month = parseInt(monthStr, 10);
  const year = parseInt(yearStr, 10);

  if (isNaN(month) || isNaN(year)) return false;
  if (month < 1 || month > 12) return false;

  // Check if not expired
  const now = new Date();
  const currentYear = now.getFullYear() % 100;
  const currentMonth = now.getMonth() + 1;

  if (year < currentYear) return false;
  if (year === currentYear && month < currentMonth) return false;

  return true;
};

/**
 * Validate CVV
 */
const validateCvv = (cvv, cardType) => {
  if (!cvv) return false;
  const expectedLen = cardType === "Amex" ? 4 : 3;
  return cvv.length === expectedLen && /^\d+$/.test(cvv);
};

/**
 * Format card number
 */
export const formatCardNumberImpl = (number) => (cardType) => {
  const digits = number.replace(/\D/g, "");

  if (cardType === "Amex") {
    let formatted = "";
    if (digits.length > 0) formatted += digits.slice(0, 4);
    if (digits.length > 4) formatted += " " + digits.slice(4, 10);
    if (digits.length > 10) formatted += " " + digits.slice(10, 15);
    return formatted;
  }

  let formatted = "";
  for (let i = 0; i < digits.length && i < 16; i += 4) {
    if (i > 0) formatted += " ";
    formatted += digits.slice(i, i + 4);
  }
  return formatted;
};

/**
 * Check if string contains only digits
 */
export const digitsOnlyCheck = (str) => /^\d+$/.test(str);

/**
 * Cleanup credit card input
 */
export const destroyCreditCardImpl = (cardObj) => {
  if (cardObj && cardObj.cleanup) {
    cardObj.cleanup();
  }
};

/**
 * Filter implementation for arrays
 */
export const filterImpl = (f) => (arr) => arr.filter(f);

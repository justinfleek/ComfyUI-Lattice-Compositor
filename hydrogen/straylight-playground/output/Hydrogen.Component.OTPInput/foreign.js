// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // otpinput
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// OTP input interaction handling

/**
 * Initialize OTP input handling
 */
export const initOTPInputImpl = (container, onChange, opts) => {
  const inputs = container.querySelectorAll("input[data-otp-index]");

  const handleInput = (e, index) => {
    const value = e.target.value;
    const char = value.slice(-1); // Get last character

    // Validate input
    if (opts.numeric && !/^\d$/.test(char)) {
      e.target.value = "";
      return;
    }
    if (!opts.numeric && !/^[a-zA-Z0-9]$/.test(char)) {
      e.target.value = "";
      return;
    }

    e.target.value = char;

    // Collect all values
    const allValues = Array.from(inputs)
      .map((input) => input.value)
      .join("");
    onChange(allValues)();

    // Auto-focus next input
    if (char && index < inputs.length - 1) {
      inputs[index + 1].focus();
    }
  };

  const handleKeyDown = (e, index) => {
    if (e.key === "Backspace") {
      if (e.target.value === "" && index > 0) {
        // Move to previous input on backspace if empty
        inputs[index - 1].focus();
        inputs[index - 1].value = "";

        // Update value
        const allValues = Array.from(inputs)
          .map((input) => input.value)
          .join("");
        onChange(allValues)();

        e.preventDefault();
      }
    } else if (e.key === "ArrowLeft" && index > 0) {
      inputs[index - 1].focus();
      e.preventDefault();
    } else if (e.key === "ArrowRight" && index < inputs.length - 1) {
      inputs[index + 1].focus();
      e.preventDefault();
    }
  };

  const handlePaste = (e) => {
    e.preventDefault();
    const pasteData = (e.clipboardData || window.clipboardData)
      .getData("text")
      .trim();

    let filtered = pasteData;
    if (opts.numeric) {
      filtered = pasteData.replace(/\D/g, "");
    } else {
      filtered = pasteData.replace(/[^a-zA-Z0-9]/g, "");
    }

    // Fill inputs with pasted data
    const chars = filtered.slice(0, opts.length).split("");
    chars.forEach((char, i) => {
      if (inputs[i]) {
        inputs[i].value = char;
      }
    });

    // Focus last filled or next empty
    const focusIndex = Math.min(chars.length, inputs.length - 1);
    inputs[focusIndex].focus();

    // Update value
    const allValues = Array.from(inputs)
      .map((input) => input.value)
      .join("");
    onChange(allValues)();
  };

  const handleFocus = (e) => {
    e.target.select();
  };

  // Attach event listeners
  inputs.forEach((input, index) => {
    input.addEventListener("input", (e) => handleInput(e, index));
    input.addEventListener("keydown", (e) => handleKeyDown(e, index));
    input.addEventListener("paste", handlePaste);
    input.addEventListener("focus", handleFocus);
  });

  // Focus first input
  if (inputs[0]) {
    inputs[0].focus();
  }

  return {
    container,
    cleanup: () => {
      inputs.forEach((input, index) => {
        input.removeEventListener("input", (e) => handleInput(e, index));
        input.removeEventListener("keydown", (e) => handleKeyDown(e, index));
        input.removeEventListener("paste", handlePaste);
        input.removeEventListener("focus", handleFocus);
      });
    },
  };
};

/**
 * Handle paste event and extract valid characters
 */
export const handlePasteImpl = (event, opts) => {
  const pasteData = (event.clipboardData || window.clipboardData)
    .getData("text")
    .trim();

  if (opts.numeric) {
    return pasteData.replace(/\D/g, "").slice(0, opts.length);
  }
  return pasteData.replace(/[^a-zA-Z0-9]/g, "").slice(0, opts.length);
};

/**
 * Focus a specific digit input
 */
export const focusDigitImpl = (container, index) => {
  const inputs = container.querySelectorAll("input[data-otp-index]");
  if (inputs[index]) {
    inputs[index].focus();
  }
};

/**
 * Cleanup OTP input
 */
export const destroyOTPInputImpl = (otpObj) => {
  if (otpObj && otpObj.cleanup) {
    otpObj.cleanup();
  }
};

/**
 * Start resend timer
 */
export const startResendTimerImpl = (seconds, onTick) => {
  let remaining = seconds;

  const tick = () => {
    remaining -= 1;
    onTick(remaining)();

    if (remaining > 0) {
      setTimeout(tick, 1000);
    }
  };

  onTick(remaining)();
  setTimeout(tick, 1000);
};

/**
 * Map implementation for arrays
 */
export const mapImpl = (f) => (arr) => arr.map(f);

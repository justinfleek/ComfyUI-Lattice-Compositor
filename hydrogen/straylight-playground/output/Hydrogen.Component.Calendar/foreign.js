// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // calendar
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Calendar FFI for locale-aware formatting and date operations

/**
 * Get localized month names
 * @param {string} locale - BCP 47 locale string
 * @returns {string[]} Array of 12 month names
 */
export const getMonthNamesImpl = (locale) => () => {
  try {
    const formatter = new Intl.DateTimeFormat(locale, { month: "long" });
    const months = [];
    for (let i = 0; i < 12; i++) {
      const date = new Date(2024, i, 1);
      months.push(formatter.format(date));
    }
    return months;
  } catch (e) {
    return [
      "January", "February", "March", "April", "May", "June",
      "July", "August", "September", "October", "November", "December"
    ];
  }
};

/**
 * Get short localized month names
 * @param {string} locale - BCP 47 locale string
 * @returns {string[]} Array of 12 short month names
 */
export const getMonthNamesShortImpl = (locale) => () => {
  try {
    const formatter = new Intl.DateTimeFormat(locale, { month: "short" });
    const months = [];
    for (let i = 0; i < 12; i++) {
      const date = new Date(2024, i, 1);
      months.push(formatter.format(date));
    }
    return months;
  } catch (e) {
    return ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
  }
};

/**
 * Get localized day names starting from Sunday
 * @param {string} locale - BCP 47 locale string
 * @returns {string[]} Array of 7 day names
 */
export const getDayNamesImpl = (locale) => () => {
  try {
    const formatter = new Intl.DateTimeFormat(locale, { weekday: "long" });
    const days = [];
    // Start from a known Sunday (Jan 7, 2024)
    for (let i = 0; i < 7; i++) {
      const date = new Date(2024, 0, 7 + i);
      days.push(formatter.format(date));
    }
    return days;
  } catch (e) {
    return ["Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"];
  }
};

/**
 * Get short localized day names starting from Sunday
 * @param {string} locale - BCP 47 locale string
 * @returns {string[]} Array of 7 short day names
 */
export const getDayNamesShortImpl = (locale) => () => {
  try {
    const formatter = new Intl.DateTimeFormat(locale, { weekday: "short" });
    const days = [];
    for (let i = 0; i < 7; i++) {
      const date = new Date(2024, 0, 7 + i);
      days.push(formatter.format(date));
    }
    return days;
  } catch (e) {
    return ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
  }
};

/**
 * Get narrow localized day names (single letter) starting from Sunday
 * @param {string} locale - BCP 47 locale string
 * @returns {string[]} Array of 7 narrow day names
 */
export const getDayNamesNarrowImpl = (locale) => () => {
  try {
    const formatter = new Intl.DateTimeFormat(locale, { weekday: "narrow" });
    const days = [];
    for (let i = 0; i < 7; i++) {
      const date = new Date(2024, 0, 7 + i);
      days.push(formatter.format(date));
    }
    return days;
  } catch (e) {
    return ["S", "M", "T", "W", "T", "F", "S"];
  }
};

/**
 * Get today's date as { year, month, day }
 * Month is 1-indexed (1 = January)
 */
export const getTodayImpl = () => {
  const now = new Date();
  return {
    year: now.getFullYear(),
    month: now.getMonth() + 1,
    day: now.getDate()
  };
};

/**
 * Get the number of days in a month
 * @param {number} year
 * @param {number} month - 1-indexed (1 = January)
 * @returns {number}
 */
export const getDaysInMonthImpl = (year) => (month) => {
  // Day 0 of next month = last day of this month
  return new Date(year, month, 0).getDate();
};

/**
 * Get the day of week for the first day of a month
 * @param {number} year
 * @param {number} month - 1-indexed (1 = January)
 * @returns {number} 0 = Sunday, 6 = Saturday
 */
export const getFirstDayOfMonthImpl = (year) => (month) => {
  return new Date(year, month - 1, 1).getDay();
};

/**
 * Format a date according to locale
 * @param {string} locale
 * @param {object} date - { year, month, day }
 * @param {string} format - "short", "medium", "long", "full"
 * @returns {string}
 */
export const formatDateImpl = (locale) => (date) => (format) => () => {
  try {
    const d = new Date(date.year, date.month - 1, date.day);
    const options = {};
    
    switch (format) {
      case "short":
        options.dateStyle = "short";
        break;
      case "medium":
        options.dateStyle = "medium";
        break;
      case "long":
        options.dateStyle = "long";
        break;
      case "full":
        options.dateStyle = "full";
        break;
      case "iso":
        return d.toISOString().split("T")[0];
      default:
        options.dateStyle = "medium";
    }
    
    return new Intl.DateTimeFormat(locale, options).format(d);
  } catch (e) {
    return `${date.year}-${String(date.month).padStart(2, "0")}-${String(date.day).padStart(2, "0")}`;
  }
};

/**
 * Parse a date string into { year, month, day }
 * @param {string} dateStr
 * @returns {{ year: number, month: number, day: number } | null}
 */
export const parseDateImpl = (dateStr) => () => {
  try {
    // Try ISO format first (YYYY-MM-DD)
    const isoMatch = dateStr.match(/^(\d{4})-(\d{2})-(\d{2})$/);
    if (isoMatch) {
      return {
        year: parseInt(isoMatch[1], 10),
        month: parseInt(isoMatch[2], 10),
        day: parseInt(isoMatch[3], 10)
      };
    }
    
    // Try common formats
    const date = new Date(dateStr);
    if (!isNaN(date.getTime())) {
      return {
        year: date.getFullYear(),
        month: date.getMonth() + 1,
        day: date.getDate()
      };
    }
    
    return null;
  } catch (e) {
    return null;
  }
};

/**
 * Compare two dates
 * @returns {number} -1 if a < b, 0 if equal, 1 if a > b
 */
export const compareDatesImpl = (a) => (b) => {
  const dateA = new Date(a.year, a.month - 1, a.day);
  const dateB = new Date(b.year, b.month - 1, b.day);
  
  if (dateA < dateB) return -1;
  if (dateA > dateB) return 1;
  return 0;
};

/**
 * Check if two dates are the same
 */
export const sameDateImpl = (a) => (b) => {
  return a.year === b.year && a.month === b.month && a.day === b.day;
};

/**
 * Add days to a date
 */
export const addDaysImpl = (date) => (days) => {
  const d = new Date(date.year, date.month - 1, date.day);
  d.setDate(d.getDate() + days);
  return {
    year: d.getFullYear(),
    month: d.getMonth() + 1,
    day: d.getDate()
  };
};

/**
 * Add months to a date
 */
export const addMonthsImpl = (date) => (months) => {
  const d = new Date(date.year, date.month - 1 + months, date.day);
  // Handle month overflow (e.g., Jan 31 + 1 month)
  const targetMonth = (date.month - 1 + months) % 12;
  if (d.getMonth() !== (targetMonth >= 0 ? targetMonth : targetMonth + 12)) {
    d.setDate(0); // Go to last day of previous month
  }
  return {
    year: d.getFullYear(),
    month: d.getMonth() + 1,
    day: d.getDate()
  };
};

/**
 * Get week number (ISO 8601)
 */
export const getWeekNumberImpl = (date) => {
  const d = new Date(date.year, date.month - 1, date.day);
  d.setHours(0, 0, 0, 0);
  d.setDate(d.getDate() + 4 - (d.getDay() || 7));
  const yearStart = new Date(d.getFullYear(), 0, 1);
  return Math.ceil((((d - yearStart) / 86400000) + 1) / 7);
};

/**
 * Check if a year is a leap year
 */
export const isLeapYearImpl = (year) => {
  return (year % 4 === 0 && year % 100 !== 0) || (year % 400 === 0);
};

/**
 * Convert nullable to Maybe
 */
export const toMaybeImpl = (just) => (nothing) => (value) => {
  return value === null || value === undefined ? nothing : just(value);
};

/**
 * Text Animator Expressions
 *
 * Per-character animation support for text layers.
 * Provides context and evaluation for text animator expressions.
 */

import type { ExpressionContext, TextAnimatorContext } from './types';

// Re-export types
export type { TextAnimatorContext } from './types';

// ============================================================
// TEXT ANIMATOR CONTEXT
// ============================================================

/**
 * Create a text animator context for per-character animation
 *
 * @param baseCtx - Base expression context
 * @param text - Full text string
 * @param charIndex - Current character index
 * @param selectorValue - Selector value (0-1)
 * @returns Extended context with text animator variables
 */
export function createTextAnimatorContext(
  baseCtx: ExpressionContext,
  text: string,
  charIndex: number,
  selectorValue: number = 1
): TextAnimatorContext {
  const char = text[charIndex] || '';

  // Calculate word and line positions
  let wordIndex = 0;
  let lineIndex = 0;
  let charInWord = 0;
  let charInLine = 0;
  let currentWordStart = 0;
  let currentLineStart = 0;

  for (let i = 0; i <= charIndex && i < text.length; i++) {
    if (text[i] === ' ' || text[i] === '\t') {
      if (i < charIndex) {
        wordIndex++;
        currentWordStart = i + 1;
      }
    }
    if (text[i] === '\n') {
      if (i < charIndex) {
        lineIndex++;
        currentLineStart = i + 1;
        wordIndex++;
        currentWordStart = i + 1;
      }
    }
  }

  charInWord = charIndex - currentWordStart;
  charInLine = charIndex - currentLineStart;

  return {
    ...baseCtx,
    textIndex: charIndex,
    textTotal: text.length,
    char,
    selectorValue,
    wordIndex,
    lineIndex,
    charInWord,
    charInLine
  };
}

/**
 * Evaluate expression with text animator context
 *
 * This allows expressions like:
 *   position[0] + Math.sin(textIndex * 0.5) * 50
 *   opacity * selectorValue
 *   scale + [textIndex * 5, textIndex * 5]
 */
export function evaluateTextAnimatorExpression(
  code: string,
  ctx: TextAnimatorContext,
  evaluateCustomExpression: (code: string, ctx: ExpressionContext) => number | number[] | string
): number | number[] | string {
  // Add text animator variables to context
  // BUG-017: Use JSON.stringify to properly escape ALL special characters
  const extendedCode = `
    const textIndex = ${ctx.textIndex};
    const textTotal = ${ctx.textTotal};
    const selectorValue = ${ctx.selectorValue};
    const char = ${JSON.stringify(ctx.char)};
    const wordIndex = ${ctx.wordIndex || 0};
    const lineIndex = ${ctx.lineIndex || 0};
    const charInWord = ${ctx.charInWord || 0};
    const charInLine = ${ctx.charInLine || 0};
    ${code}
  `;

  return evaluateCustomExpression(extendedCode, ctx);
}

// ============================================================
// TEXT ANIMATOR NAMESPACE
// ============================================================

/**
 * Text animator namespace
 */
export const textAnimator = {
  createContext: createTextAnimatorContext,
  // Note: evaluate requires the evaluateCustomExpression function to be passed
};

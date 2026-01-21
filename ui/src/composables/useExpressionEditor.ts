import { ref, shallowRef } from "vue";
import { isExpressionSafe } from "@/services/expressions/expressionValidator";
import { useKeyframeStore } from "@/stores/keyframeStore";
import type { AnimatableProperty, PropertyExpression } from "@/types/project";

// Global state for expression editor
const isVisible = ref(false);
const currentProperty = shallowRef<AnimatableProperty<any> | null>(null);
const currentLayerId = ref<string>("");
const currentPropertyPath = ref<string>("");

/**
 * Composable for global expression editor state
 * Use this to open the expression editor from any component
 */
export function useExpressionEditor() {
  /**
   * Open the expression editor for a specific property
   */
  function openExpressionEditor(
    property: AnimatableProperty<any>,
    layerId: string,
    propertyPath: string = "",
  ) {
    currentProperty.value = property;
    currentLayerId.value = layerId;
    currentPropertyPath.value = propertyPath;
    isVisible.value = true;
  }

  /**
   * Close the expression editor
   */
  function closeExpressionEditor() {
    isVisible.value = false;
  }

  /**
   * Apply expression to the current property.
   * Uses store action instead of direct mutation for undo/redo support.
   * SECURITY: Validates custom expressions before applying to prevent DoS.
   */
  async function applyExpression(
    expression: PropertyExpression,
  ): Promise<boolean> {
    if (!currentLayerId.value || !currentPropertyPath.value) {
      closeExpressionEditor();
      return false;
    }

    // SECURITY: Validate custom expressions before applying
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    if (expression.type === "custom" && expression.params !== undefined && typeof expression.params === "object" && "code" in expression.params && expression.params.code !== null && expression.params.code !== undefined) {
      const code = expression.params.code as string;
      const safe = await isExpressionSafe(code);
      if (!safe) {
        console.error(
          "[SECURITY] Expression blocked - timeout detected (possible infinite loop)",
        );
        alert(
          "Expression blocked: This expression appears to contain an infinite loop and could hang your browser.",
        );
        return false;
      }
    }

    useKeyframeStore().setPropertyExpression(
      currentLayerId.value,
      currentPropertyPath.value,
      expression,
    );
    closeExpressionEditor();
    return true;
  }

  /**
   * Remove expression from the current property.
   * Uses store action instead of direct mutation for undo/redo support.
   */
  function removeExpression() {
    if (currentLayerId.value && currentPropertyPath.value) {
      useKeyframeStore().removePropertyExpression(
        currentLayerId.value,
        currentPropertyPath.value,
      );
    }
    closeExpressionEditor();
  }

  return {
    // State
    isVisible,
    currentProperty,
    currentLayerId,
    currentPropertyPath,
    // Actions
    openExpressionEditor,
    closeExpressionEditor,
    applyExpression,
    removeExpression,
  };
}

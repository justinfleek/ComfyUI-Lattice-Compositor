// FFI implementation for Lattice.Services.ComfyUI.WorkflowUtilities
//
// @module Lattice.Services.ComfyUI.WorkflowUtilities
// @description JavaScript FFI for workflow parsing and serialization.
//
// This file provides the bridge between PureScript and JavaScript for:
// - Parsing ComfyUI workflow JSON
// - Serializing workflow nodes to JSON

"use strict";

/**
 * Parse workflow JSON string to array of nodes
 *
 * @param {string} json - JSON string representing ComfyUI workflow
 * @returns {function} EffectFnAff that resolves to Either String (Array WorkflowNode)
 */
export const parseWorkflowImpl = (json) => (onError, onSuccess) => {
  try {
    const workflow = JSON.parse(json);
    const nodes = [];

    // ComfyUI workflows are objects with node IDs as keys
    for (const [nodeId, nodeData] of Object.entries(workflow)) {
      // Skip metadata keys
      if (nodeId === '_meta' || nodeId === 'extra' || nodeId === 'version') {
        continue;
      }

      const connections = [];

      // Parse inputs - inputs are in nodeData.inputs
      if (nodeData.inputs) {
        for (const [inputName, inputValue] of Object.entries(nodeData.inputs)) {
          // Connections are arrays: [refNodeId, outputIndex]
          if (Array.isArray(inputValue) && inputValue.length >= 2) {
            connections.push({
              inputName: inputName,
              refNodeId: String(inputValue[0]),
              outputIndex: inputValue[1]
            });
          }
        }
      }

      nodes.push({
        id: nodeId,
        classType: nodeData.class_type || '',
        connections: connections
      });
    }

    // Return Right (success)
    onSuccess({ tag: 'Right', value: nodes })();
  } catch (e) {
    // Return Left (error)
    onSuccess({ tag: 'Left', value: e.message })();
  }

  // Return canceler (no-op)
  return (cancelError, onCancelerError, onCancelerSuccess) => {
    onCancelerSuccess()();
  };
};

/**
 * Serialize workflow nodes to JSON string
 *
 * @param {Array} nodes - Array of workflow nodes
 * @returns {string} JSON string
 */
export const serializeWorkflowImpl = (nodes) => {
  const workflow = {};

  for (const node of nodes) {
    const inputs = {};

    // Convert connections back to ComfyUI format
    for (const conn of node.connections) {
      inputs[conn.inputName] = [conn.refNodeId, conn.outputIndex];
    }

    workflow[node.id] = {
      class_type: node.classType,
      inputs: inputs
    };
  }

  return JSON.stringify(workflow, null, 2);
};

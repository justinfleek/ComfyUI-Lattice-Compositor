import * as vscode from "vscode";
import { ThemeGeneratorPanel } from "./themeGeneratorPanel";
import { ThemePreviewPanel } from "./themePreviewPanel";

export function activate(context: vscode.ExtensionContext) {
  console.log("Prism Theme Generator extension is now active");

  // Register command: Generate Theme
  const generateCommand = vscode.commands.registerCommand(
    "prismTheme.generate",
    () => {
      ThemeGeneratorPanel.createOrShow(context.extensionUri);
    }
  );

  // Register command: Preview Theme
  const previewCommand = vscode.commands.registerCommand(
    "prismTheme.preview",
    () => {
      ThemePreviewPanel.createOrShow(context.extensionUri);
    }
  );

  // Register command: Export Theme
  const exportCommand = vscode.commands.registerCommand(
    "prismTheme.export",
    async () => {
      const themeData = await vscode.window.showInputBox({
        prompt: "Enter theme name",
        placeHolder: "my-theme"
      });
      if (themeData) {
        // TODO: Implement export
        vscode.window.showInformationMessage("Theme export not yet implemented");
      }
    }
  );

  context.subscriptions.push(generateCommand, previewCommand, exportCommand);
}

export function deactivate() {}

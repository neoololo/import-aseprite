import { doGeneration } from "./vite.js";
import fs from "fs";

export const testImportModuleSpecifier = /** @type {ImportablePlugin['testImportModuleSpecifier']} */ (moduleName) => (
	moduleName.endsWith('.aseprite')
);

export const testImportAttributes = /** @type {ImportablePlugin['testImportAttributes']} */ (importAttributes) => true;

export const generateTypeScriptDefinition = /** @type {ImportablePlugin['generateTypeScriptDefinition']} */ (_fileName, _importAttributes, code) => {
	return doGeneration(_fileName, fs.readFileSync(_fileName)).code;
};

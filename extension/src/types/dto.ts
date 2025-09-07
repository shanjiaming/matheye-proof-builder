// DTO types mirrored from MathEye.SyntaxNodeDto (Lean side)

export interface RangeDto {
  start: { line: number; character: number };
  stop: { line: number; character: number };
}

export interface SyntaxNodeDto {
  kind: string;
  children?: SyntaxNodeDto[];
  value?: string;
  // Optional spacing hints
  leading?: string | null;
  trailing?: string | null;
  // Optional range (present on server responses like getASTAtPosition)
  range?: RangeDto | null;
}

export interface TextConversionResult {
  text: string;
  success: boolean;
  errorMsg?: string;
}


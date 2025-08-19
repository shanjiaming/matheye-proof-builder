import * as vscode from 'vscode';

export interface TranslationResult {
    original: string;
    translated: string;
    error?: string;
}

/**
 * Service for translating Lean goals to natural language using OpenAI API
 */
export class TranslationService {
    private cache = new Map<string, TranslationResult>();
    private outputChannel: vscode.OutputChannel;
    private pendingRequests = new Map<string, Promise<TranslationResult>>();

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel("MathEye Translation");
    }

    /**
     * Get OpenAI API configuration from settings
     */
    private getConfig() {
        const config = vscode.workspace.getConfiguration('matheye');
        const apiKeyFromSettings = config.get<string>('openai.apiKey', '');
        const apiKeyFromEnv = process.env.OPENAI_API_KEY || '';
        
        return {
            apiKey: apiKeyFromSettings || apiKeyFromEnv,
            model: config.get<string>('openai.model', 'gpt-5-nano'),
            baseUrl: config.get<string>('openai.baseUrl', 'https://api.openai.com'),
            timeout: config.get<number>('openai.timeout', 60000)
        };
    }

    /**
     * Check if translation is enabled globally
     */
    isTranslationEnabled(): boolean {
        return vscode.workspace.getConfiguration('matheye').get<boolean>('translation.enabled', false);
    }

    /**
     * Toggle translation enabled state
     */
    async toggleTranslation(): Promise<boolean> {
        const config = vscode.workspace.getConfiguration('matheye');
        const current = this.isTranslationEnabled();
        await config.update('translation.enabled', !current, vscode.ConfigurationTarget.Global);
        return !current;
    }

    /**
     * Get cached translation or create new one
     */
    async translateGoal(goalText: string): Promise<TranslationResult> {
        if (!goalText.trim()) {
            return { original: goalText, translated: goalText };
        }

        // Check cache first
        const cached = this.cache.get(goalText);
        if (cached) {
            return cached;
        }

        // Check if request is already pending to avoid duplicate API calls
        const pending = this.pendingRequests.get(goalText);
        if (pending) {
            return pending;
        }

        // Create new translation request
        const promise = this.performTranslation(goalText);
        this.pendingRequests.set(goalText, promise);

        try {
            const result = await promise;
            this.cache.set(goalText, result);
            return result;
        } finally {
            this.pendingRequests.delete(goalText);
        }
    }

    /**
     * Perform actual translation via OpenAI API
     */
    private async performTranslation(goalText: string): Promise<TranslationResult> {
        const config = this.getConfig();
        
        if (!config.apiKey) {
            const error = 'OpenAI API key not configured. Please set matheye.openai.apiKey in settings or OPENAI_API_KEY environment variable.';
            this.outputChannel.appendLine(error);
            return { original: goalText, translated: goalText, error };
        }

        try {
            this.outputChannel.appendLine(`Translating goal: ${goalText.substring(0, 100)}...`);
            
            const prompt = `我给你一些Lean 4的状态，你能不能帮我把它们翻译成数学家能看懂的中文版本？然后用markdown写出来。对于每一道题，输出的每个语言的markdown文件包括两部分：已知（Assumptions）和目标（Goal）。要求：
- 数学家都看不懂Lean代码的，所以不要把任何Lean内置有特殊含义的写法或者代码放进输出当中，尽量使用其对应的数学含义
- 不要擅自省略任何条件，原版有什么条件，就原原本本包含进来
- 如果一个条件重复了很多次，那就只保留一次就行，并且你不需要注明它重复之类的
- 数学公式使用$和$$进行转义
- 如果数学中有约定俗成的标记，比如\mathbb{N}表示自然数集，可以说明然后使用
- 表达尽量简洁
- 直接输出markdown代码给我，不要用代码框包住

${goalText}`;

            const response = await fetch(`${config.baseUrl}/v1/chat/completions`, {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                    'Authorization': `Bearer ${config.apiKey}`
                },
                body: JSON.stringify({
                    model: config.model,
                    messages: [
                        {
                            role: 'user',
                            content: prompt
                        }
                    ]
                }),
                signal: AbortSignal.timeout(config.timeout)
            });

            if (!response.ok) {
                const errorText = await response.text();
                this.outputChannel.appendLine(`API Error Details: ${errorText}`);
                throw new Error(`OpenAI API error: ${response.status} ${response.statusText} - ${errorText}`);
            }

            const data: any = await response.json();
            const translated = data.choices?.[0]?.message?.content?.trim() || goalText;
            
            this.outputChannel.appendLine(`Translation completed: ${translated.substring(0, 100)}...`);
            
            return {
                original: goalText,
                translated: translated
            };

        } catch (error) {
            const errorMsg = `Translation failed: ${error}`;
            this.outputChannel.appendLine(errorMsg);
            return {
                original: goalText,
                translated: goalText,
                error: errorMsg
            };
        }
    }

    /**
     * Clear translation cache
     */
    clearCache(): void {
        this.cache.clear();
        this.outputChannel.appendLine('Translation cache cleared');
    }

    /**
     * Get cache statistics
     */
    getCacheStats(): { size: number; keys: string[] } {
        return {
            size: this.cache.size,
            keys: Array.from(this.cache.keys()).map(k => k.substring(0, 50) + '...')
        };
    }

    /**
     * Show translation output channel
     */
    showOutput(): void {
        this.outputChannel.show();
    }

    dispose(): void {
        this.cache.clear();
        this.pendingRequests.clear();
        this.outputChannel.dispose();
    }
}
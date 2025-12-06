#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdarg.h>
#include <math.h>
#include <time.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <netdb.h>
#include <openssl/ssl.h>
#include <openssl/err.h>
#include <cjson/cJSON.h>
#define PCRE2_CODE_UNIT_WIDTH 8
#include <pcre2.h>

#define MAX_TOKENS 10000
#define MAX_VARIABLES 1000
#define MAX_FUNCTIONS 500
#define MAX_STRING_LEN 4096
#define MAX_STACK_FRAMES 1000
// --- START: GC DYNAMIC THRESHOLD CONSTANTS ---
#define GC_MIN_THRESHOLD 10       // Minimum threshold to ensure collection runs under memory pressure
#define GC_DEFAULT_THRESHOLD 1000 // Initial threshold
// --- END: GC DYNAMIC THRESHOLD CONSTANTS ---

typedef enum {
    TOKEN_EOF, TOKEN_NUMBER, TOKEN_STRING, TOKEN_IDENT, TOKEN_LPAREN, TOKEN_RPAREN,
    TOKEN_LBRACE, TOKEN_RBRACE, TOKEN_LBRACKET, TOKEN_RBRACKET, TOKEN_COMMA, TOKEN_COLON,
    TOKEN_SEMICOLON, TOKEN_DOT, TOKEN_PIPE, TOKEN_ARROW, TOKEN_EQUALS, TOKEN_PLUS,
    TOKEN_MINUS, TOKEN_MULTIPLY, TOKEN_DIVIDE, TOKEN_MODULO, TOKEN_POWER, TOKEN_LESS,
    TOKEN_GREATER, TOKEN_LESS_EQ, TOKEN_GREATER_EQ, TOKEN_EQ, TOKEN_NOT_EQ, TOKEN_AND,
    TOKEN_OR, TOKEN_NOT, TOKEN_QUESTION, TOKEN_NEWLINE, TOKEN_INDENT, TOKEN_DEDENT,
    TOKEN_IF, TOKEN_ELSE, TOKEN_WHILE, TOKEN_FOR, TOKEN_REPEAT, TOKEN_BREAK, TOKEN_CONTINUE,
    TOKEN_FUNCTION, TOKEN_RETURN, TOKEN_TRY, TOKEN_CATCH, TOKEN_FINALLY, TOKEN_THROW,
    TOKEN_WHEN, TOKEN_FETCH, TOKEN_TELL, TOKEN_ASK, TOKEN_READ, TOKEN_WRITE, TOKEN_CREATE,
    TOKEN_SEND, TOKEN_RECEIVE, TOKEN_CONNECT, TOKEN_LISTEN, TOKEN_TRUE, TOKEN_FALSE,
    TOKEN_NULL, TOKEN_AND_WORD, TOKEN_OR_WORD, TOKEN_NOT_WORD, TOKEN_IS, TOKEN_AS,
    TOKEN_IN, TOKEN_FROM, TOKEN_TO, TOKEN_THROUGH, TOKEN_ON, TOKEN_WITH, TOKEN_LAMBDA
} TokenType;

typedef struct {
    TokenType type;
    char value[MAX_STRING_LEN];
    int line;
    int column;
} Token;

typedef struct Value Value;

typedef struct {
    char name[256];
    Value *value;
} Variable;

typedef struct {
    char name[256];
    struct ASTNode *body;
    Variable *params;
    int param_count;
    Variable *locals;
    int local_count;
} Function;

typedef struct {
    Variable *vars;
    int count;
} Scope;

typedef enum {
    VAL_NULL, VAL_NUMBER, VAL_STRING, VAL_BOOL, VAL_LIST, VAL_MAP, VAL_FUNCTION, VAL_OBJECT
} ValueType;

typedef struct Value {
    ValueType type;
    union {
        double number;
        char *string;
        int boolean;
        struct {
            Value **items;
            int count;
            int capacity;
        } list;
        struct {
            char **keys;
            Value **values;
            int count;
        } map;
        Function function;
    } data;
    int marked;
    struct Value *next;
} Value;

typedef struct ASTNode {
    enum {
        AST_NUMBER, AST_STRING, AST_IDENT, AST_BOOL, AST_NULL, AST_LIST, AST_MAP,
        AST_BINARY_OP, AST_UNARY_OP, AST_IF, AST_WHILE, AST_FOR, AST_FUNCTION_DEF,
        AST_FUNCTION_CALL, AST_RETURN, AST_BREAK, AST_CONTINUE, AST_TRY_CATCH,
        AST_BLOCK, AST_INDEX, AST_MEMBER, AST_ASSIGN, AST_LAMBDA, AST_REPEAT
    } type;

    union {
        double number;
        char *string;
        char ident[256];
        int boolean;

        struct {
            struct ASTNode **items;
            int count;
        } list;

        struct {
            char **keys;
            struct ASTNode **values;
            int count;
        } map;

        struct {
            char op[16];
            struct ASTNode *left;
            struct ASTNode *right;
        } binary_op;

        struct {
            char op[16];
            struct ASTNode *operand;
        } unary_op;

        struct {
            struct ASTNode *condition;
            struct ASTNode *then_body;
            struct ASTNode *else_body;
        } if_stmt;

        struct {
            struct ASTNode *condition;
            struct ASTNode *body;
        } while_stmt;

        struct {
            char var_name[256];
            struct ASTNode *iterable;
            struct ASTNode *body;
        } for_stmt;

        struct {
            struct ASTNode *count;
            struct ASTNode *body;
        } repeat_stmt;

        struct {
            char name[256];
            char **params;
            int param_count;
            struct ASTNode *body;
        } function_def;

        struct {
            struct ASTNode *function;
            struct ASTNode **args;
            int arg_count;
        } function_call;

        struct {
            struct ASTNode *value;
        } return_stmt;

        struct {
            struct ASTNode *try_body;
            char error_var[256];
            struct ASTNode *catch_body;
            struct ASTNode *finally_body;
        } try_catch;

        struct {
            struct ASTNode **statements;
            int count;
        } block;

        struct {
            struct ASTNode *object;
            struct ASTNode *index;
        } index_op;

        struct {
            struct ASTNode *object;
            char member[256];
        } member_op;

        struct {
            char var_name[256];
            struct ASTNode *value;
        } assign;

        struct {
            char **params;
            int param_count;
            struct ASTNode *body;
        } lambda;
    } data;
} ASTNode;

typedef struct {
    Token *tokens;
    int count;
    int current;
} Lexer;

typedef struct {
    Lexer lexer;
    int current_line;
    int indent_level;
} Parser;

// --- START: GC DYNAMIC THRESHOLD STRUCT EDIT ---
typedef struct {
    Value *head;
    int count;
    int collections_count;
    int threshold; // The current dynamic allocation threshold
} GarbageCollector;
// --- END: GC DYNAMIC THRESHOLD STRUCT EDIT ---

typedef struct {
    Variable *variables;
    int var_count;
    Scope scopes[MAX_STACK_FRAMES];
    int scope_count;
    GarbageCollector gc;
} Interpreter;

Interpreter *global_interp = NULL;

void gc_collect();

Value *value_new(ValueType type) {
    Value *v = malloc(sizeof(Value));
    v->type = type;
    v->marked = 0;
    v->next = global_interp->gc.head;
    global_interp->gc.head = v;

    global_interp->gc.count++;

    // Dynamic GC Check: Trigger collection if object count exceeds the current threshold
    if (global_interp->gc.count >= global_interp->gc.threshold) {
        gc_collect();
    }

    return v;
}
// --- END: GC DYNAMIC THRESHOLD value_new EDIT ---

Value *value_number(double num) {
    Value *v = value_new(VAL_NUMBER);
    v->data.number = num;
    return v;
}

Value *value_string(const char *str) {
    Value *v = value_new(VAL_STRING);
    v->data.string = malloc(strlen(str) + 1);
    strcpy(v->data.string, str);
    return v;
}

Value *value_bool(int b) {
    Value *v = value_new(VAL_BOOL);
    v->data.boolean = b;
    return v;
}

Value *value_null() {
    return value_new(VAL_NULL);
}

Value *value_list() {
    Value *v = value_new(VAL_LIST);
    v->data.list.items = malloc(10 * sizeof(Value*));
    v->data.list.count = 0;
    v->data.list.capacity = 10;
    return v;
}

Value *value_map() {
    Value *v = value_new(VAL_MAP);
    v->data.map.keys = malloc(10 * sizeof(char*));
    v->data.map.values = malloc(10 * sizeof(Value*));
    v->data.map.count = 0;
    return v;
}

void value_list_append(Value *list, Value *item) {
    if (list->type != VAL_LIST) return;
    if (list->data.list.count >= list->data.list.capacity) {
        list->data.list.capacity *= 2;
        list->data.list.items = realloc(list->data.list.items, list->data.list.capacity * sizeof(Value*));
    }
    list->data.list.items[list->data.list.count++] = item;
}

void value_map_set(Value *map, const char *key, Value *val) {
    if (map->type != VAL_MAP) return;
    for (int i = 0; i < map->data.map.count; i++) {
        if (strcmp(map->data.map.keys[i], key) == 0) {
            map->data.map.values[i] = val;
            return;
        }
    }
    map->data.map.keys[map->data.map.count] = malloc(strlen(key) + 1);
    strcpy(map->data.map.keys[map->data.map.count], key);
    map->data.map.values[map->data.map.count] = val;
    map->data.map.count++;
}

Value *value_map_get(Value *map, const char *key) {
    if (map->type != VAL_MAP) return value_null();
    for (int i = 0; i < map->data.map.count; i++) {
        if (strcmp(map->data.map.keys[i], key) == 0) {
            return map->data.map.values[i];
        }
    }
    return value_null();
}

void gc_mark(Value *v) {
    if (!v || v->marked) return;
    v->marked = 1;
    if (v->type == VAL_LIST) {
        for (int i = 0; i < v->data.list.count; i++) {
            gc_mark(v->data.list.items[i]);
        }
    } else if (v->type == VAL_MAP) {
        for (int i = 0; i < v->data.map.count; i++) {
            gc_mark(v->data.map.values[i]);
        }
    }
}

void gc_sweep() {
    Value **pp = &global_interp->gc.head;
    while (*pp) {
        if ((*pp)->marked) {
            (*pp)->marked = 0;
            pp = &(*pp)->next;
        } else {
            Value *temp = *pp;
            *pp = temp->next;
            if (temp->type == VAL_STRING) free(temp->data.string);
            else if (temp->type == VAL_LIST) free(temp->data.list.items);
            else if (temp->type == VAL_MAP) {
                for (int i = 0; i < temp->data.map.count; i++) free(temp->data.map.keys[i]);
                free(temp->data.map.keys);
                free(temp->data.map.values);
            }
            free(temp);
            global_interp->gc.count--;
        }
    }
}

// --- START: GC DYNAMIC THRESHOLD gc_collect EDIT ---
void gc_collect() {
    global_interp->gc.collections_count++; // Increment collection counter

    // 1. Mark Phase 
    for (int i = 0; i < global_interp->var_count; i++) {
        gc_mark(global_interp->variables[i].value);
    }
    for (int i = 0; i < global_interp->scope_count; i++) {
        for (int j = 0; j < global_interp->scopes[i].count; j++) {
            gc_mark(global_interp->scopes[i].vars[j].value);
        }
    }

    // 2. Sweep Phase (gc_sweep updates global_interp->gc.count to the number of *live* objects)
    gc_sweep();

    // 3. Dynamic Threshold Calculation
    int live_objects = global_interp->gc.count;

    // New threshold is twice the number of live objects (a 2x 'safety buffer')
    int new_threshold = live_objects * 2; 

    // Ensure the new threshold is at least the minimum safe value
    if (new_threshold < GC_MIN_THRESHOLD) {
        new_threshold = GC_MIN_THRESHOLD;
    }

    // Apply the new dynamic threshold
    global_interp->gc.threshold = new_threshold;
}
// --- END: GC DYNAMIC THRESHOLD gc_collect EDIT ---

void error(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    printf("ERROR: ");
    vprintf(fmt, args);
    printf("\n");
    va_end(args);
}

Token *lexer_tokenize(const char *code) {
    Token *tokens = malloc(MAX_TOKENS * sizeof(Token));
    int token_count = 0;
    int line = 1, column = 1;

    const char *keywords[] = {
        "if", "else", "while", "for", "repeat", "break", "continue", "function",
        "return", "try", "catch", "finally", "throw", "when", "fetch", "tell",
        "ask", "read", "write", "create", "send", "receive", "connect", "listen",
        "true", "false", "null", "and", "or", "not", "is", "as", "in", "from",
        "to", "through", "on", "with"
    };

    int i = 0;
    while (code[i] && token_count < MAX_TOKENS) {
        if (isspace(code[i])) {
            if (code[i] == '\n') { line++; column = 1; }
            else column++;
            i++;
            continue;
        }

        tokens[token_count].line = line;
        tokens[token_count].column = column;

        if (isdigit(code[i])) {
            char num_str[256] = {0};
            int j = 0;
            while (isdigit(code[i]) || code[i] == '.') {
                num_str[j++] = code[i++];
                column++;
            }
            tokens[token_count].type = TOKEN_NUMBER;
            strcpy(tokens[token_count].value, num_str);
            token_count++;
        } else if (code[i] == '"') {
            i++;
            char str[4096] = {0};
            int j = 0;
            while (code[i] && code[i] != '"') {
                if (code[i] == '\\' && code[i+1]) {
                    i++;
                    if (code[i] == 'n') str[j++] = '\n';
                    else if (code[i] == 't') str[j++] = '\t';
                    else str[j++] = code[i];
                } else {
                    str[j++] = code[i];
                }
                i++;
                column++;
            }
            if (code[i] == '"') { i++; column++; }
            tokens[token_count].type = TOKEN_STRING;
            strcpy(tokens[token_count].value, str);
            token_count++;
        } else if (isalpha(code[i]) || code[i] == '_') {
            char ident[256] = {0};
            int j = 0;
            while (isalnum(code[i]) || code[i] == '_') {
                ident[j++] = code[i++];
                column++;
            }
            tokens[token_count].value[0] = 0;
            strcpy(tokens[token_count].value, ident);

            int is_keyword = 0;
            int num_keywords = sizeof(keywords) / sizeof(keywords[0]);
            for (int k = 0; k < num_keywords; k++) {
                if (strcmp(ident, keywords[k]) == 0) {
                    is_keyword = 1;
                    if (strcmp(ident, "if") == 0) tokens[token_count].type = TOKEN_IF;
                    else if (strcmp(ident, "else") == 0) tokens[token_count].type = TOKEN_ELSE;
                    else if (strcmp(ident, "while") == 0) tokens[token_count].type = TOKEN_WHILE;
                    else if (strcmp(ident, "for") == 0) tokens[token_count].type = TOKEN_FOR;
                    else if (strcmp(ident, "repeat") == 0) tokens[token_count].type = TOKEN_REPEAT;
                    else if (strcmp(ident, "break") == 0) tokens[token_count].type = TOKEN_BREAK;
                    else if (strcmp(ident, "continue") == 0) tokens[token_count].type = TOKEN_CONTINUE;
                    else if (strcmp(ident, "function") == 0) tokens[token_count].type = TOKEN_FUNCTION;
                    else if (strcmp(ident, "return") == 0) tokens[token_count].type = TOKEN_RETURN;
                    else if (strcmp(ident, "try") == 0) tokens[token_count].type = TOKEN_TRY;
                    else if (strcmp(ident, "catch") == 0) tokens[token_count].type = TOKEN_CATCH;
                    else if (strcmp(ident, "finally") == 0) tokens[token_count].type = TOKEN_FINALLY;
                    else if (strcmp(ident, "throw") == 0) tokens[token_count].type = TOKEN_THROW;
                    else if (strcmp(ident, "when") == 0) tokens[token_count].type = TOKEN_WHEN;
                    else if (strcmp(ident, "fetch") == 0) tokens[token_count].type = TOKEN_FETCH;
                    else if (strcmp(ident, "tell") == 0) tokens[token_count].type = TOKEN_TELL;
                    else if (strcmp(ident, "ask") == 0) tokens[token_count].type = TOKEN_ASK;
                    else if (strcmp(ident, "read") == 0) tokens[token_count].type = TOKEN_READ;
                    else if (strcmp(ident, "write") == 0) tokens[token_count].type = TOKEN_WRITE;
                    else if (strcmp(ident, "create") == 0) tokens[token_count].type = TOKEN_CREATE;
                    else if (strcmp(ident, "send") == 0) tokens[token_count].type = TOKEN_SEND;
                    else if (strcmp(ident, "receive") == 0) tokens[token_count].type = TOKEN_RECEIVE;
                    else if (strcmp(ident, "connect") == 0) tokens[token_count].type = TOKEN_CONNECT;
                    else if (strcmp(ident, "listen") == 0) tokens[token_count].type = TOKEN_LISTEN;
                    else if (strcmp(ident, "true") == 0) tokens[token_count].type = TOKEN_TRUE;
                    else if (strcmp(ident, "false") == 0) tokens[token_count].type = TOKEN_FALSE;
                    else if (strcmp(ident, "null") == 0) tokens[token_count].type = TOKEN_NULL;
                    else if (strcmp(ident, "and") == 0) tokens[token_count].type = TOKEN_AND_WORD;
                    else if (strcmp(ident, "or") == 0) tokens[token_count].type = TOKEN_OR_WORD;
                    else if (strcmp(ident, "not") == 0) tokens[token_count].type = TOKEN_NOT_WORD;
                    else if (strcmp(ident, "is") == 0) tokens[token_count].type = TOKEN_IS;
                    else if (strcmp(ident, "as") == 0) tokens[token_count].type = TOKEN_AS;
                    else if (strcmp(ident, "in") == 0) tokens[token_count].type = TOKEN_IN;
                    else if (strcmp(ident, "from") == 0) tokens[token_count].type = TOKEN_FROM;
                    else if (strcmp(ident, "to") == 0) tokens[token_count].type = TOKEN_TO;
                    else if (strcmp(ident, "through") == 0) tokens[token_count].type = TOKEN_THROUGH;
                    else if (strcmp(ident, "on") == 0) tokens[token_count].type = TOKEN_ON;
                    else if (strcmp(ident, "with") == 0) tokens[token_count].type = TOKEN_WITH;
                    break;
                }
            }
            if (!is_keyword) tokens[token_count].type = TOKEN_IDENT;
            token_count++;
        } else {
            switch (code[i]) {
                case '(': tokens[token_count].type = TOKEN_LPAREN; i++; column++; token_count++; break;
                case ')': tokens[token_count].type = TOKEN_RPAREN; i++; column++; token_count++; break;
                case '{': tokens[token_count].type = TOKEN_LBRACE; i++; column++; token_count++; break;
                case '}': tokens[token_count].type = TOKEN_RBRACE; i++; column++; token_count++; break;
                case '[': tokens[token_count].type = TOKEN_LBRACKET; i++; column++; token_count++; break;
                case ']': tokens[token_count].type = TOKEN_RBRACKET; i++; column++; token_count++; break;
                case ',': tokens[token_count].type = TOKEN_COMMA; i++; column++; token_count++; break;
                case ':': tokens[token_count].type = TOKEN_COLON; i++; column++; token_count++; break;
                case ';': tokens[token_count].type = TOKEN_SEMICOLON; i++; column++; token_count++; break;
                case '.': tokens[token_count].type = TOKEN_DOT; i++; column++; token_count++; break;
                case '|': tokens[token_count].type = TOKEN_PIPE; i++; column++; token_count++; break;
                case '?': tokens[token_count].type = TOKEN_QUESTION; i++; column++; token_count++; break;
                case '+': tokens[token_count].type = TOKEN_PLUS; i++; column++; token_count++; break;
                case '-':
                    if (code[i+1] == '>') {
                        tokens[token_count].type = TOKEN_ARROW;
                        i += 2; column += 2;
                    } else {
                        tokens[token_count].type = TOKEN_MINUS;
                        i++; column++;
                    }
                    token_count++;
                    break;
                case '*': tokens[token_count].type = TOKEN_MULTIPLY; i++; column++; token_count++; break;
                case '/': tokens[token_count].type = TOKEN_DIVIDE; i++; column++; token_count++; break;
                case '%': tokens[token_count].type = TOKEN_MODULO; i++; column++; token_count++; break;
                case '^': tokens[token_count].type = TOKEN_POWER; i++; column++; token_count++; break;
                case '<':
                    if (code[i+1] == '=') {
                        tokens[token_count].type = TOKEN_LESS_EQ;
                        i += 2; column += 2;
                    } else {
                        tokens[token_count].type = TOKEN_LESS;
                        i++; column++;
                    }
                    token_count++;
                    break;
                case '>':
                    if (code[i+1] == '=') {
                        tokens[token_count].type = TOKEN_GREATER_EQ;
                        i += 2; column += 2;
                    } else {
                        tokens[token_count].type = TOKEN_GREATER;
                        i++; column++;
                    }
                    token_count++;
                    break;
                case '=':
                    if (code[i+1] == '=') {
                        tokens[token_count].type = TOKEN_EQ;
                        i += 2; column += 2;
                    } else {
                        tokens[token_count].type = TOKEN_EQUALS;
                        i++; column++;
                    }
                    token_count++;
                    break;
                case '!':
                    if (code[i+1] == '=') {
                        tokens[token_count].type = TOKEN_NOT_EQ;
                        i += 2; column += 2;
                    } else {
                        tokens[token_count].type = TOKEN_NOT;
                        i++; column++;
                    }
                    token_count++;
                    break;
                case '&':
                    if (code[i+1] == '&') {
                        tokens[token_count].type = TOKEN_AND;
                        i += 2; column += 2;
                    }
                    token_count++;
                    break;
                default:
                    i++; column++;
            }
        }
    }

    tokens[token_count].type = TOKEN_EOF;
    return tokens;
}

ASTNode *ast_number(double n) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_NUMBER;
    node->data.number = n;
    return node;
}

ASTNode *ast_string(const char *s) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_STRING;
    node->data.string = malloc(strlen(s) + 1);
    strcpy(node->data.string, s);
    return node;
}

ASTNode *ast_ident(const char *name) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_IDENT;
    strcpy(node->data.ident, name);
    return node;
}

ASTNode *ast_binary_op(const char *op, ASTNode *left, ASTNode *right) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_BINARY_OP;
    strcpy(node->data.binary_op.op, op);
    node->data.binary_op.left = left;
    node->data.binary_op.right = right;
    return node;
}

ASTNode *ast_unary_op(const char *op, ASTNode *operand) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_UNARY_OP;
    strcpy(node->data.unary_op.op, op);
    node->data.unary_op.operand = operand;
    return node;
}

ASTNode *ast_list() {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_LIST;
    node->data.list.items = malloc(100 * sizeof(ASTNode*));
    node->data.list.count = 0;
    return node;
}

ASTNode *ast_map() {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_MAP;
    node->data.map.keys = malloc(100 * sizeof(char*));
    node->data.map.values = malloc(100 * sizeof(ASTNode*));
    node->data.map.count = 0;
    return node;
}

ASTNode *ast_function_call(ASTNode *func, ASTNode **args, int arg_count) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_FUNCTION_CALL;
    node->data.function_call.function = func;
    node->data.function_call.args = args;
    node->data.function_call.arg_count = arg_count;
    return node;
}

ASTNode *ast_if(ASTNode *cond, ASTNode *then_body, ASTNode *else_body) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_IF;
    node->data.if_stmt.condition = cond;
    node->data.if_stmt.then_body = then_body;
    node->data.if_stmt.else_body = else_body;
    return node;
}

ASTNode *ast_while(ASTNode *cond, ASTNode *body) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_WHILE;
    node->data.while_stmt.condition = cond;
    node->data.while_stmt.body = body;
    return node;
}

ASTNode *ast_block(ASTNode **stmts, int count) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = AST_BLOCK;
    node->data.block.statements = stmts;
    node->data.block.count = count;
    return node;
}

Parser *parser_new(Token *tokens) {
    Parser *p = malloc(sizeof(Parser));
    p->lexer.tokens = tokens;
    p->lexer.current = 0;
    int count = 0;
    while (tokens[count].type != TOKEN_EOF) count++;
    p->lexer.count = count + 1;
    p->current_line = 1;
    p->indent_level = 0;
    return p;
}

Token *parser_current(Parser *p) {
    if (p->lexer.current >= p->lexer.count) return &p->lexer.tokens[p->lexer.count - 1];
    return &p->lexer.tokens[p->lexer.current];
}

Token *parser_peek(Parser *p, int offset) {
    int idx = p->lexer.current + offset;
    if (idx >= p->lexer.count) return &p->lexer.tokens[p->lexer.count - 1];
    return &p->lexer.tokens[idx];
}

void parser_advance(Parser *p) {
    if (p->lexer.current < p->lexer.count - 1) p->lexer.current++;
}

int parser_match(Parser *p, TokenType type) {
    if (parser_current(p)->type == type) {
        parser_advance(p);
        return 1;
    }
    return 0;
}

ASTNode *parser_parse_primary(Parser *p);
ASTNode *parser_parse_expression(Parser *p);
ASTNode *parser_parse_statement(Parser *p);

ASTNode *parser_parse_primary(Parser *p) {
    Token *tok = parser_current(p);

    if (tok->type == TOKEN_NUMBER) {
        parser_advance(p);
        return ast_number(atof(tok->value));
    }

    if (tok->type == TOKEN_STRING) {
        parser_advance(p);
        return ast_string(tok->value);
    }

    if (tok->type == TOKEN_TRUE) {
        parser_advance(p);
        ASTNode *node = malloc(sizeof(ASTNode));
        node->type = AST_BOOL;
        node->data.boolean = 1;
        return node;
    }

    if (tok->type == TOKEN_FALSE) {
        parser_advance(p);
        ASTNode *node = malloc(sizeof(ASTNode));
        node->type = AST_BOOL;
        node->data.boolean = 0;
        return node;
    }

    if (tok->type == TOKEN_NULL) {
        parser_advance(p);
        ASTNode *node = malloc(sizeof(ASTNode));
        node->type = AST_NULL;
        return node;
    }

    if (tok->type == TOKEN_IDENT) {
        parser_advance(p);
        return ast_ident(tok->value);
    }

    if (tok->type == TOKEN_LBRACKET) {
        parser_advance(p);
        ASTNode *list = ast_list();
        while (parser_current(p)->type != TOKEN_RBRACKET && parser_current(p)->type != TOKEN_EOF) {
            list->data.list.items[list->data.list.count++] = parser_parse_expression(p);
            if (parser_current(p)->type == TOKEN_COMMA) parser_advance(p);
        }
        if (parser_current(p)->type == TOKEN_RBRACKET) parser_advance(p);
        return list;
    }

    if (tok->type == TOKEN_LBRACE) {
        parser_advance(p);
        ASTNode *map = ast_map();
        while (parser_current(p)->type != TOKEN_RBRACE && parser_current(p)->type != TOKEN_EOF) {
            Token *key_tok = parser_current(p);
            parser_advance(p);
            if (parser_current(p)->type == TOKEN_COLON) parser_advance(p);
            map->data.map.keys[map->data.map.count] = malloc(strlen(key_tok->value) + 1);
            strcpy(map->data.map.keys[map->data.map.count], key_tok->value);
            map->data.map.values[map->data.map.count] = parser_parse_expression(p);
            map->data.map.count++;
            if (parser_current(p)->type == TOKEN_COMMA) parser_advance(p);
        }
        if (parser_current(p)->type == TOKEN_RBRACE) parser_advance(p);
        return map;
    }

    if (tok->type == TOKEN_LPAREN) {
        parser_advance(p);
        ASTNode *expr = parser_parse_expression(p);
        if (parser_current(p)->type == TOKEN_RPAREN) parser_advance(p);
        return expr;
    }

    return ast_number(0);
}

ASTNode *parser_parse_postfix(Parser *p) {
    ASTNode *expr = parser_parse_primary(p);

    while (1) {
        if (parser_current(p)->type == TOKEN_LBRACKET) {
            parser_advance(p);
            ASTNode *index = parser_parse_expression(p);
            if (parser_current(p)->type == TOKEN_RBRACKET) parser_advance(p);
            ASTNode *node = malloc(sizeof(ASTNode));
            node->type = AST_INDEX;
            node->data.index_op.object = expr;
            node->data.index_op.index = index;
            expr = node;
        } else if (parser_current(p)->type == TOKEN_DOT) {
            parser_advance(p);
            Token *member = parser_current(p);
            parser_advance(p);
            ASTNode *node = malloc(sizeof(ASTNode));
            node->type = AST_MEMBER;
            node->data.member_op.object = expr;
            strcpy(node->data.member_op.member, member->value);
            expr = node;
        } else if (parser_current(p)->type == TOKEN_LPAREN) {
            parser_advance(p);
            ASTNode **args = malloc(100 * sizeof(ASTNode*));
            int arg_count = 0;
            while (parser_current(p)->type != TOKEN_RPAREN && parser_current(p)->type != TOKEN_EOF) {
                args[arg_count++] = parser_parse_expression(p);
                if (parser_current(p)->type == TOKEN_COMMA) parser_advance(p);
            }
            if (parser_current(p)->type == TOKEN_RPAREN) parser_advance(p);
            expr = ast_function_call(expr, args, arg_count);
        } else {
            break;
        }
    }

    return expr;
}

ASTNode *parser_parse_unary(Parser *p) {
    if (parser_current(p)->type == TOKEN_NOT || parser_current(p)->type == TOKEN_NOT_WORD) {
        parser_advance(p);
        return ast_unary_op("!", parser_parse_unary(p));
    }

    if (parser_current(p)->type == TOKEN_MINUS) {
        parser_advance(p);
        return ast_unary_op("-", parser_parse_unary(p));
    }

    return parser_parse_postfix(p);
}

ASTNode *parser_parse_power(Parser *p) {
    ASTNode *left = parser_parse_unary(p);

    while (parser_current(p)->type == TOKEN_POWER) {
        parser_advance(p);
        ASTNode *right = parser_parse_unary(p);
        left = ast_binary_op("^", left, right);
    }

    return left;
}

ASTNode *parser_parse_multiplicative(Parser *p) {
    ASTNode *left = parser_parse_power(p);

    while (parser_current(p)->type == TOKEN_MULTIPLY || parser_current(p)->type == TOKEN_DIVIDE || parser_current(p)->type == TOKEN_MODULO) {
        Token *op = parser_current(p);
        parser_advance(p);
        ASTNode *right = parser_parse_power(p);
        char op_str[2] = {0};
        if (op->type == TOKEN_MULTIPLY) op_str[0] = '*';
        else if (op->type == TOKEN_DIVIDE) op_str[0] = '/';
        else if (op->type == TOKEN_MODULO) op_str[0] = '%';
        left = ast_binary_op(op_str, left, right);
    }

    return left;
}

ASTNode *parser_parse_additive(Parser *p) {
    ASTNode *left = parser_parse_multiplicative(p);

    while (parser_current(p)->type == TOKEN_PLUS || parser_current(p)->type == TOKEN_MINUS) {
        Token *op = parser_current(p);
        parser_advance(p);
        ASTNode *right = parser_parse_multiplicative(p);
        char op_str[2] = {0};
        if (op->type == TOKEN_PLUS) op_str[0] = '+';
        else if (op->type == TOKEN_MINUS) op_str[0] = '-';
        left = ast_binary_op(op_str, left, right);
    }

    return left;
}

ASTNode *parser_parse_relational(Parser *p) {
    ASTNode *left = parser_parse_additive(p);

    while (parser_current(p)->type == TOKEN_LESS || parser_current(p)->type == TOKEN_LESS_EQ ||
           parser_current(p)->type == TOKEN_GREATER || parser_current(p)->type == TOKEN_GREATER_EQ) {
        Token *op = parser_current(p);
        parser_advance(p);
        ASTNode *right = parser_parse_additive(p);
        char op_str[3] = {0};
        if (op->type == TOKEN_LESS) strcpy(op_str, "<");
        else if (op->type == TOKEN_LESS_EQ) strcpy(op_str, "<=");
        else if (op->type == TOKEN_GREATER) strcpy(op_str, ">");
        else if (op->type == TOKEN_GREATER_EQ) strcpy(op_str, ">=");
        left = ast_binary_op(op_str, left, right);
    }

    return left;
}

ASTNode *parser_parse_equality(Parser *p) {
    ASTNode *left = parser_parse_relational(p);

    while (parser_current(p)->type == TOKEN_EQ || parser_current(p)->type == TOKEN_NOT_EQ || parser_current(p)->type == TOKEN_IS) {
        Token *op = parser_current(p);
        parser_advance(p);
        ASTNode *right = parser_parse_relational(p);
        char op_str[3] = {0};
        if (op->type == TOKEN_EQ) strcpy(op_str, "==");
        else if (op->type == TOKEN_NOT_EQ) strcpy(op_str, "!=");
        else if (op->type == TOKEN_IS) strcpy(op_str, "is");
        left = ast_binary_op(op_str, left, right);
    }

    return left;
}

ASTNode *parser_parse_logical_and(Parser *p) {
    ASTNode *left = parser_parse_equality(p);

    while (parser_current(p)->type == TOKEN_AND || parser_current(p)->type == TOKEN_AND_WORD) {
        parser_advance(p);
        ASTNode *right = parser_parse_equality(p);
        left = ast_binary_op("&&", left, right);
    }

    return left;
}

ASTNode *parser_parse_logical_or(Parser *p) {
    ASTNode *left = parser_parse_logical_and(p);

    while (parser_current(p)->type == TOKEN_OR || parser_current(p)->type == TOKEN_OR_WORD) {
        parser_advance(p);
        ASTNode *right = parser_parse_logical_and(p);
        left = ast_binary_op("||", left, right);
    }

    return left;
}

ASTNode *parser_parse_expression(Parser *p) {
    return parser_parse_logical_or(p);
}

ASTNode *parser_parse_statement(Parser *p) {
    Token *tok = parser_current(p);

    if (tok->type == TOKEN_IF) {
        parser_advance(p);
        ASTNode *cond = parser_parse_expression(p);
        if (parser_current(p)->type == TOKEN_LBRACE) {
            parser_advance(p);
            ASTNode **stmts = malloc(1000 * sizeof(ASTNode*));
            int stmt_count = 0;
            while (parser_current(p)->type != TOKEN_RBRACE && parser_current(p)->type != TOKEN_EOF) {
                stmts[stmt_count++] = parser_parse_statement(p);
            }
            if (parser_current(p)->type == TOKEN_RBRACE) parser_advance(p);
            ASTNode *then_body = ast_block(stmts, stmt_count);
            ASTNode *else_body = NULL;
            if (parser_current(p)->type == TOKEN_ELSE) {
                parser_advance(p);
                if (parser_current(p)->type == TOKEN_LBRACE) {
                    parser_advance(p);
                    ASTNode **else_stmts = malloc(1000 * sizeof(ASTNode*));
                    int else_count = 0;
                    while (parser_current(p)->type != TOKEN_RBRACE && parser_current(p)->type != TOKEN_EOF) {
                        else_stmts[else_count++] = parser_parse_statement(p);
                    }
                    if (parser_current(p)->type == TOKEN_RBRACE) parser_advance(p);
                    else_body = ast_block(else_stmts, else_count);
                }
            }
            return ast_if(cond, then_body, else_body);
        }
    }

    if (tok->type == TOKEN_WHILE) {
        parser_advance(p);
        ASTNode *cond = parser_parse_expression(p);
        if (parser_current(p)->type == TOKEN_LBRACE) {
            parser_advance(p);
            ASTNode **stmts = malloc(1000 * sizeof(ASTNode*));
            int stmt_count = 0;
            while (parser_current(p)->type != TOKEN_RBRACE && parser_current(p)->type != TOKEN_EOF) {
                stmts[stmt_count++] = parser_parse_statement(p);
            }
            if (parser_current(p)->type == TOKEN_RBRACE) parser_advance(p);
            return ast_while(cond, ast_block(stmts, stmt_count));
        }
    }

    if (tok->type == TOKEN_FOR) {
        parser_advance(p);
        char var_name[256];
        if (parser_current(p)->type == TOKEN_IDENT) {
            strcpy(var_name, parser_current(p)->value);
            parser_advance(p);
        }
        if (parser_current(p)->type == TOKEN_IN) parser_advance(p);
        ASTNode *iterable = parser_parse_expression(p);
        if (parser_current(p)->type == TOKEN_LBRACE) {
            parser_advance(p);
            ASTNode **stmts = malloc(1000 * sizeof(ASTNode*));
            int stmt_count = 0;
            while (parser_current(p)->type != TOKEN_RBRACE && parser_current(p)->type != TOKEN_EOF) {
                stmts[stmt_count++] = parser_parse_statement(p);
            }
            if (parser_current(p)->type == TOKEN_RBRACE) parser_advance(p);
            ASTNode *node = malloc(sizeof(ASTNode));
            node->type = AST_FOR;
            strcpy(node->data.for_stmt.var_name, var_name);
            node->data.for_stmt.iterable = iterable;
            node->data.for_stmt.body = ast_block(stmts, stmt_count);
            return node;
        }
    }

    if (tok->type == TOKEN_REPEAT) {
        parser_advance(p);
        ASTNode *count = parser_parse_expression(p);
        if (parser_current(p)->type == TOKEN_LBRACE) {
            parser_advance(p);
            ASTNode **stmts = malloc(1000 * sizeof(ASTNode*));
            int stmt_count = 0;
            while (parser_current(p)->type != TOKEN_RBRACE && parser_current(p)->type != TOKEN_EOF) {
                stmts[stmt_count++] = parser_parse_statement(p);
            }
            if (parser_current(p)->type == TOKEN_RBRACE) parser_advance(p);
            ASTNode *node = malloc(sizeof(ASTNode));
            node->type = AST_REPEAT;
            node->data.repeat_stmt.count = count;
            node->data.repeat_stmt.body = ast_block(stmts, stmt_count);
            return node;
        }
    }

    if (tok->type == TOKEN_BREAK) {
        parser_advance(p);
        ASTNode *node = malloc(sizeof(ASTNode));
        node->type = AST_BREAK;
        return node;
    }

    if (tok->type == TOKEN_CONTINUE) {
        parser_advance(p);
        ASTNode *node = malloc(sizeof(ASTNode));
        node->type = AST_CONTINUE;
        return node;
    }

    if (tok->type == TOKEN_RETURN) {
        parser_advance(p);
        ASTNode *node = malloc(sizeof(ASTNode));
        node->type = AST_RETURN;
        if (parser_current(p)->type != TOKEN_SEMICOLON && parser_current(p)->type != TOKEN_EOF) {
            node->data.return_stmt.value = parser_parse_expression(p);
        } else {
            node->data.return_stmt.value = NULL;
        }
        return node;
    }

    if (tok->type == TOKEN_FUNCTION) {
        parser_advance(p);
        char func_name[256] = {0};
        if (parser_current(p)->type == TOKEN_IDENT) {
            strcpy(func_name, parser_current(p)->value);
            parser_advance(p);
        }

        char **params = malloc(100 * sizeof(char*));
        int param_count = 0;
        if (parser_current(p)->type == TOKEN_LPAREN) {
            parser_advance(p);
            while (parser_current(p)->type != TOKEN_RPAREN && parser_current(p)->type != TOKEN_EOF) {
                if (parser_current(p)->type == TOKEN_IDENT) {
                    params[param_count] = malloc(256);
                    strcpy(params[param_count], parser_current(p)->value);
                    param_count++;
                    parser_advance(p);
                }
                if (parser_current(p)->type == TOKEN_COMMA) parser_advance(p);
            }
            if (parser_current(p)->type == TOKEN_RPAREN) parser_advance(p);
        }

        if (parser_current(p)->type == TOKEN_LBRACE) {
            parser_advance(p);
            ASTNode **stmts = malloc(1000 * sizeof(ASTNode*));
            int stmt_count = 0;
            while (parser_current(p)->type != TOKEN_RBRACE && parser_current(p)->type != TOKEN_EOF) {
                stmts[stmt_count++] = parser_parse_statement(p);
            }
            if (parser_current(p)->type == TOKEN_RBRACE) parser_advance(p);

            ASTNode *node = malloc(sizeof(ASTNode));
            node->type = AST_FUNCTION_DEF;
            strcpy(node->data.function_def.name, func_name);
            node->data.function_def.params = params;
            node->data.function_def.param_count = param_count;
            node->data.function_def.body = ast_block(stmts, stmt_count);
            return node;
        }
    }

    // Assignment or Expression Statement
    ASTNode *expr = parser_parse_expression(p);

    if (parser_current(p)->type == TOKEN_EQUALS) {
        parser_advance(p);
        ASTNode *value = parser_parse_expression(p);

        if (expr->type == AST_IDENT) {
            ASTNode *node = malloc(sizeof(ASTNode));
            node->type = AST_ASSIGN;
            strcpy(node->data.assign.var_name, expr->data.ident);
            node->data.assign.value = value;
            return node;
        }
    }

    return expr;
}

int break_flag = 0;
int continue_flag = 0;
int return_flag = 0;
Value *return_value = NULL;

Value *interp_get_variable(const char *name) {
    for (int i = 0; i < global_interp->var_count; i++) {
        if (strcmp(global_interp->variables[i].name, name) == 0) {
            return global_interp->variables[i].value;
        }
    }
    return value_null();
}

void interp_set_variable(const char *name, Value *value) {
    for (int i = 0; i < global_interp->var_count; i++) {
        if (strcmp(global_interp->variables[i].name, name) == 0) {
            global_interp->variables[i].value = value;
            return;
        }
    }

    if (global_interp->var_count < MAX_VARIABLES) {
        strcpy(global_interp->variables[global_interp->var_count].name, name);
        global_interp->variables[global_interp->var_count].value = value;
        global_interp->var_count++;
    }
}

void interp_push_scope() {
    if (global_interp->scope_count < MAX_STACK_FRAMES) {
        global_interp->scopes[global_interp->scope_count].vars = malloc(MAX_VARIABLES * sizeof(Variable));
        global_interp->scopes[global_interp->scope_count].count = global_interp->var_count;
        for (int i = 0; i < global_interp->var_count; i++) {
            global_interp->scopes[global_interp->scope_count].vars[i] = global_interp->variables[i];
        }
        global_interp->scope_count++;
    }
}

void interp_pop_scope() {
    if (global_interp->scope_count > 0) {
        global_interp->scope_count--;
        global_interp->var_count = global_interp->scopes[global_interp->scope_count].count;
        for (int i = 0; i < global_interp->var_count; i++) {
            global_interp->variables[i] = global_interp->scopes[global_interp->scope_count].vars[i];
        }
        free(global_interp->scopes[global_interp->scope_count].vars);
    }
}

SSL_CTX *ssl_ctx = NULL;

Value *interp_eval_builtin(const char *name, Value **args, int arg_count) {
    if (strcmp(name, "print") == 0) {
        for (int i = 0; i < arg_count; i++) {
            if (args[i]->type == VAL_NUMBER) printf("%g", args[i]->data.number);
            else if (args[i]->type == VAL_STRING) printf("%s", args[i]->data.string);
            else if (args[i]->type == VAL_BOOL) printf("%s", args[i]->data.boolean ? "true" : "false");
            else if (args[i]->type == VAL_NULL) printf("null");
            else if (args[i]->type == VAL_LIST) printf("[List]");
            else if (args[i]->type == VAL_MAP) printf("{Map}");
            else printf("[Object]");
        }
        printf("\n");
        return value_null();
    }

    if (strcmp(name, "len") == 0 && arg_count == 1) {
        Value *arg = args[0];
        if (arg->type == VAL_STRING) return value_number(strlen(arg->data.string));
        if (arg->type == VAL_LIST) return value_number(arg->data.list.count);
        if (arg->type == VAL_MAP) return value_number(arg->data.map.count);
        return value_number(0);
    }

    if (strcmp(name, "push") == 0 && arg_count == 2) {
        Value *list = args[0];
        Value *item = args[1];
        if (list->type == VAL_LIST) {
            value_list_append(list, item);
        }
        return value_null();
    }

    if (strcmp(name, "pop") == 0 && arg_count == 1) {
        Value *list = args[0];
        if (list->type == VAL_LIST && list->data.list.count > 0) {
            return list->data.list.items[--list->data.list.count];
        }
        return value_null();
    }

    if (strcmp(name, "string") == 0 && arg_count == 1) {
        Value *arg = args[0];
        if (arg->type == VAL_NUMBER) {
            char buf[256];
            sprintf(buf, "%g", arg->data.number);
            return value_string(buf);
        }
        if (arg->type == VAL_STRING) return arg;
        if (arg->type == VAL_BOOL) return value_string(arg->data.boolean ? "true" : "false");
        return value_string("null");
    }

    if (strcmp(name, "number") == 0 && arg_count == 1) {
        Value *arg = args[0];
        if (arg->type == VAL_NUMBER) return arg;
        if (arg->type == VAL_STRING) return value_number(atof(arg->data.string));
        if (arg->type == VAL_BOOL) return value_number(arg->data.boolean ? 1 : 0);
        return value_number(0);
    }

    if (strcmp(name, "fetch") == 0 && arg_count == 1) {
        const char *url = args[0]->data.string;
        char host[256] = {0};
        char path[256] = {0};
        char port_str[6] = "80";
        int sock = -1;
        SSL *ssl = NULL;

        if (strncmp(url, "https://", 8) == 0) {
            strcpy(port_str, "443");
            sscanf(url + 8, "%255[^/]%255s", host, path);
            if (!ssl_ctx) {
                ssl_ctx = SSL_CTX_new(TLS_client_method());
                if (!ssl_ctx) {
                    ERR_print_errors_fp(stderr);
                    return value_string("Failed to create SSL context");
                }
            }
        } else if (strncmp(url, "http://", 7) == 0) {
            sscanf(url + 7, "%255[^/]%255s", host, path);
        }

        if (strlen(path) == 0) strcpy(path, "/");

        struct hostent *he = gethostbyname(host);
        if (!he) return value_string("Failed to resolve host");

        struct sockaddr_in addr;
        addr.sin_family = AF_INET;
        addr.sin_port = htons(atoi(port_str));
        addr.sin_addr = *(struct in_addr *)he->h_addr_list[0];

        sock = socket(AF_INET, SOCK_STREAM, 0);
        if (sock < 0) return value_string("Failed to create socket");

        if (connect(sock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
            close(sock);
            return value_string("Failed to connect");
        }

        if (atoi(port_str) == 443) {
            ssl = SSL_new(ssl_ctx);
            SSL_set_fd(ssl, sock);
            if (SSL_connect(ssl) <= 0) {
                SSL_free(ssl);
                close(sock);
                return value_string("SSL connection failed");
            }
        }

        char request[1024];
        sprintf(request, "GET %s HTTP/1.1\r\nHost: %s\r\nConnection: close\r\n\r\n", path, host);

        if (ssl) SSL_write(ssl, request, strlen(request));
        else send(sock, request, strlen(request), 0);

        char response[8192] = {0};
        int total = 0;
        char buf[1024];
        while (1) {
            int n;
            if (ssl) n = SSL_read(ssl, buf, sizeof(buf));
            else n = recv(sock, buf, sizeof(buf), 0);

            if (n <= 0) break;

            if (total + n < sizeof(response)) {
                memcpy(response + total, buf, n);
                total += n;
            } else {
                // Buffer overflow protection
                break;
            }
        }

        if (ssl) SSL_shutdown(ssl);
        if (ssl) SSL_free(ssl);
        close(sock);

        char *body = strstr(response, "\r\n\r\n");
        if (body) body += 4; else body = response;

        return value_string(body);
    }

    if (strcmp(name, "json_parse") == 0 && arg_count == 1) {
        cJSON *json = cJSON_Parse(args[0]->data.string);
        if (!json) return value_null();

        Value *result = value_map();

        if (cJSON_IsObject(json)) {
            cJSON *item = json->child;
            while (item) {
                Value *v;
                if (cJSON_IsNumber(item)) v = value_number(item->valuedouble);
                else if (cJSON_IsString(item)) v = value_string(item->valuestring);
                else if (item->type == cJSON_True) v = value_bool(1);
                else if (item->type == cJSON_False) v = value_bool(0);
                else v = value_null();
                value_map_set(result, item->string, v);
                item = item->next;
            }
        }

        cJSON_Delete(json);
        return result ? result : value_null();
    }

    if (strcmp(name, "json_stringify") == 0 && arg_count == 1) {
        Value *val = args[0];
        cJSON *json = NULL;

        if (val->type == VAL_NUMBER) {
            json = cJSON_CreateNumber(val->data.number);
        } else if (val->type == VAL_STRING) {
            json = cJSON_CreateString(val->data.string);
        } else if (val->type == VAL_BOOL) {
            json = val->data.boolean ? cJSON_CreateTrue() : cJSON_CreateFalse();
        } else if (val->type == VAL_NULL) {
            json = cJSON_CreateNull();
        } else if (val->type == VAL_LIST) {
            json = cJSON_CreateArray();
            for (int i = 0; i < val->data.list.count; i++) {
                Value *item = val->data.list.items[i];
                cJSON *j = NULL;
                if (item->type == VAL_NUMBER) j = cJSON_CreateNumber(item->data.number);
                else if (item->type == VAL_STRING) j = cJSON_CreateString(item->data.string);
                else if (item->type == VAL_BOOL) j = item->data.boolean ? cJSON_CreateTrue() : cJSON_CreateFalse();
                else j = cJSON_CreateNull();
                cJSON_AddItemToArray(json, j);
            }
        } else if (val->type == VAL_MAP) {
            json = cJSON_CreateObject();
            for (int i = 0; i < val->data.map.count; i++) {
                Value *item = val->data.map.values[i];
                cJSON *j = NULL;
                if (item->type == VAL_NUMBER) j = cJSON_CreateNumber(item->data.number);
                else if (item->type == VAL_STRING) j = cJSON_CreateString(item->data.string);
                else if (item->type == VAL_BOOL) j = item->data.boolean ? cJSON_CreateTrue() : cJSON_CreateFalse();
                else j = cJSON_CreateNull();
                cJSON_AddItemToObject(json, val->data.map.keys[i], j);
            }
        }

        if (json) {
            char *string = cJSON_Print(json);
            Value *result = value_string(string);
            free(string);
            cJSON_Delete(json);
            return result;
        }

        return value_string("null");
    }

    if (strcmp(name, "socket_send") == 0 && arg_count >= 2) {
        int sock = (int)args[0]->data.number;
        const char *data = args[1]->data.string;
        send(sock, data, strlen(data), 0);
        return value_null();
    }

    if (strcmp(name, "socket_receive") == 0 && arg_count >= 2) {
        int sock = (int)args[0]->data.number;
        int size = (int)args[1]->data.number;
        char buf[8192] = {0};
        int n = recv(sock, buf, size < sizeof(buf) ? size : sizeof(buf) - 1, 0);
        if (n > 0) buf[n] = 0;
        return value_string(buf);
    }

    if (strcmp(name, "socket_close") == 0 && arg_count >= 1) {
        int sock = (int)args[0]->data.number;
        close(sock);
        return value_null();
    }

    if (strcmp(name, "file_read") == 0 && arg_count >= 1) {
        const char *filename = args[0]->data.string;
        FILE *f = fopen(filename, "r");
        if (!f) return value_string("");
        fseek(f, 0, SEEK_END);
        long size = ftell(f);
        fseek(f, 0, SEEK_SET);
        char *buf = malloc(size + 1);
        size_t read = fread(buf, 1, size, f);
        buf[read] = 0;
        fclose(f);
        Value *result = value_string(buf);
        free(buf);
        return result;
    }

    if (strcmp(name, "file_write") == 0 && arg_count >= 2) {
        const char *filename = args[0]->data.string;
        const char *data = args[1]->data.string;
        FILE *f = fopen(filename, "w");
        if (!f) return value_bool(0);
        fwrite(data, 1, strlen(data), f);
        fclose(f);
        return value_bool(1);
    }

    if (strcmp(name, "sleep") == 0 && arg_count >= 1) {
        int seconds = (int)args[0]->data.number;
        sleep(seconds);
        return value_null();
    }

    return value_null();
}

Value *interp_eval(ASTNode *node) {
    if (break_flag || continue_flag || return_flag) return value_null();

    switch (node->type) {
        case AST_NUMBER: return value_number(node->data.number);
        case AST_STRING: return value_string(node->data.string);
        case AST_BOOL: return value_bool(node->data.boolean);
        case AST_NULL: return value_null();
        case AST_IDENT: return interp_get_variable(node->data.ident);

        case AST_LIST: {
            Value *list = value_list();
            for (int i = 0; i < node->data.list.count; i++) {
                value_list_append(list, interp_eval(node->data.list.items[i]));
            }
            return list;
        }

        case AST_MAP: {
            Value *map = value_map();
            for (int i = 0; i < node->data.map.count; i++) {
                Value *val = interp_eval(node->data.map.values[i]);
                value_map_set(map, node->data.map.keys[i], val);
            }
            return map;
        }

        case AST_BINARY_OP: {
            Value *left = interp_eval(node->data.binary_op.left);
            Value *right = interp_eval(node->data.binary_op.right);
            const char *op = node->data.binary_op.op;

            if (strcmp(op, "+") == 0) {
                if (left->type == VAL_NUMBER && right->type == VAL_NUMBER) {
                    return value_number(left->data.number + right->data.number);
                } else if (left->type == VAL_STRING || right->type == VAL_STRING) {
                    char result[MAX_STRING_LEN];
                    if (left->type == VAL_STRING) strcpy(result, left->data.string);
                    else sprintf(result, "%g", left->data.number);

                    if (right->type == VAL_STRING) strcat(result, right->data.string);
                    else {
                        char buf[256];
                        sprintf(buf, "%g", right->data.number);
                        strcat(result, buf);
                    }
                    return value_string(result);
                }
            } else if (strcmp(op, "-") == 0) {
                return value_number(left->data.number - right->data.number);
            } else if (strcmp(op, "*") == 0) {
                if (left->type == VAL_STRING && right->type == VAL_NUMBER) {
                    char result[MAX_STRING_LEN];
                    result[0] = 0;
                    for (int i = 0; i < (int)right->data.number; i++) {
                        strcat(result, left->data.string);
                    }
                    return value_string(result);
                }
                return value_number(left->data.number * right->data.number);
            } else if (strcmp(op, "/") == 0) {
                if (right->data.number == 0) error("Division by zero");
                return value_number(left->data.number / right->data.number);
            } else if (strcmp(op, "%") == 0) {
                if (right->data.number == 0) error("Modulo by zero");
                return value_number(fmod(left->data.number, right->data.number));
            } else if (strcmp(op, "^") == 0) {
                return value_number(pow(left->data.number, right->data.number));
            } else if (strcmp(op, "==") == 0) {
                if (left->type == VAL_NUMBER && right->type == VAL_NUMBER) {
                    return value_bool(left->data.number == right->data.number);
                } else if (left->type == VAL_STRING && right->type == VAL_STRING) {
                    return value_bool(strcmp(left->data.string, right->data.string) == 0);
                }
                return value_bool(0);
            } else if (strcmp(op, "!=") == 0) {
                if (left->type == VAL_NUMBER && right->type == VAL_NUMBER) {
                    return value_bool(left->data.number != right->data.number);
                } else if (left->type == VAL_STRING && right->type == VAL_STRING) {
                    return value_bool(strcmp(left->data.string, right->data.string) != 0);
                }
                return value_bool(1);
            } else if (strcmp(op, "&&") == 0) {
                int left_true = (left->type == VAL_BOOL && left->data.boolean) || (left->type == VAL_NUMBER && left->data.number != 0);
                int right_true = (right->type == VAL_BOOL && right->data.boolean) || (right->type == VAL_NUMBER && right->data.number != 0);
                return value_bool(left_true && right_true);
            } else if (strcmp(op, "||") == 0) {
                int left_true = (left->type == VAL_BOOL && left->data.boolean) || (left->type == VAL_NUMBER && left->data.number != 0);
                int right_true = (right->type == VAL_BOOL && right->data.boolean) || (right->type == VAL_NUMBER && right->data.number != 0);
                return value_bool(left_true || right_true);
            } else if (strcmp(op, "in") == 0) {
                if (right->type == VAL_LIST) {
                    for (int i = 0; i < right->data.list.count; i++) {
                        Value *item = right->data.list.items[i];
                        if (left->type == VAL_NUMBER && item->type == VAL_NUMBER && left->data.number == item->data.number) {
                            return value_bool(1);
                        }
                        if (left->type == VAL_STRING && item->type == VAL_STRING && strcmp(left->data.string, item->data.string) == 0) {
                            return value_bool(1);
                        }
                    }
                }
                return value_bool(0);
            }
            break;
        }

        case AST_UNARY_OP: {
            Value *operand = interp_eval(node->data.unary_op.operand);
            const char *op = node->data.unary_op.op;
            if (strcmp(op, "!") == 0) {
                int is_true = (operand->type == VAL_BOOL && operand->data.boolean) || (operand->type == VAL_NUMBER && operand->data.number != 0);
                return value_bool(!is_true);
            } else if (strcmp(op, "-") == 0) {
                if (operand->type == VAL_NUMBER) return value_number(-operand->data.number);
            }
            break;
        }

        case AST_ASSIGN: {
            Value *val = interp_eval(node->data.assign.value);
            interp_set_variable(node->data.assign.var_name, val);
            return val;
        }

        case AST_IF: {
            Value *cond = interp_eval(node->data.if_stmt.condition);
            int cond_true = (cond->type == VAL_BOOL && cond->data.boolean) || (cond->type == VAL_NUMBER && cond->data.number != 0);

            if (cond_true) {
                return interp_eval(node->data.if_stmt.then_body);
            } else if (node->data.if_stmt.else_body) {
                return interp_eval(node->data.if_stmt.else_body);
            }
            return value_null();
        }

        case AST_WHILE: {
            Value *result = value_null();
            while (1) {
                Value *cond = interp_eval(node->data.while_stmt.condition);
                int cond_true = (cond->type == VAL_BOOL && cond->data.boolean) || (cond->type == VAL_NUMBER && cond->data.number != 0);
                if (!cond_true) break;

                result = interp_eval(node->data.while_stmt.body);
                if (break_flag) { break_flag = 0; break; }
                if (continue_flag) { continue_flag = 0; continue; }
                if (return_flag) break;
            }
            return result;
        }

        case AST_REPEAT: {
            Value *count_val = interp_eval(node->data.repeat_stmt.count);
            int count = (int)count_val->data.number;
            Value *result = value_null();
            for (int i = 0; i < count; i++) {
                result = interp_eval(node->data.repeat_stmt.body);
                if (break_flag) { break_flag = 0; break; }
                if (continue_flag) { continue_flag = 0; continue; }
                if (return_flag) break;
            }
            return result;
        }

        case AST_FOR: {
            Value *iterable = interp_eval(node->data.for_stmt.iterable);
            Value *result = value_null();

            if (iterable->type == VAL_LIST) {
                for (int i = 0; i < iterable->data.list.count; i++) {
                    int found = 0;
                    for (int j = 0; j < global_interp->var_count; j++) {
                        if (strcmp(global_interp->variables[j].name, node->data.for_stmt.var_name) == 0) {
                            global_interp->variables[j].value = iterable->data.list.items[i];
                            found = 1;
                            break;
                        }
                    }
                    if (!found) {
                        strcpy(global_interp->variables[global_interp->var_count].name, node->data.for_stmt.var_name);
                        global_interp->variables[global_interp->var_count].value = iterable->data.list.items[i];
                        global_interp->var_count++;
                    }

                    result = interp_eval(node->data.for_stmt.body);

                    if (break_flag) { break_flag = 0; break; }
                    if (continue_flag) { continue_flag = 0; continue; }
                    if (return_flag) break;
                }
            }
            return result;
        }

        case AST_BLOCK: {
            Value *result = value_null();
            for (int i = 0; i < node->data.block.count; i++) {
                result = interp_eval(node->data.block.statements[i]);
                if (break_flag || continue_flag || return_flag) break;
            }
            return result;
        }

        case AST_FUNCTION_DEF: {
            Value *v = value_new(VAL_FUNCTION);
            v->data.function.body = node->data.function_def.body;
            v->data.function.param_count = node->data.function_def.param_count;
            v->data.function.params = malloc(v->data.function.param_count * sizeof(Variable));
            for (int i = 0; i < v->data.function.param_count; i++) {
                strcpy(v->data.function.params[i].name, node->data.function_def.params[i]);
            }
            interp_set_variable(node->data.function_def.name, v);
            return v;
        }

        case AST_FUNCTION_CALL: {
            Value *func_val = interp_eval(node->data.function_call.function);
            Value **args = malloc((size_t)node->data.function_call.arg_count * sizeof(Value*));
            for (int i = 0; i < node->data.function_call.arg_count; i++) {
                args[i] = interp_eval(node->data.function_call.args[i]);
            }

            if (func_val->type == VAL_FUNCTION) {
                interp_push_scope();

                for (int i = 0; i < node->data.function_call.arg_count; i++) {
                    if (i < func_val->data.function.param_count) {
                        interp_set_variable(func_val->data.function.params[i].name, args[i]);
                    }
                }

                Value *result = interp_eval(func_val->data.function.body);

                interp_pop_scope();

                free(args);

                if (return_flag) {
                    return_flag = 0;
                    Value *ret = return_value;
                    return_value = NULL;
                    return ret;
                }
                return result;
            } else if (func_val->type == VAL_NULL && node->data.function_call.function->type == AST_IDENT) {
                Value *result = interp_eval_builtin(node->data.function_call.function->data.ident, args, node->data.function_call.arg_count);
                free(args);
                return result;
            }

            error("Attempted to call a non-function value");
            free(args);
            return value_null();
        }

        case AST_RETURN: {
            return_flag = 1;
            return_value = node->data.return_stmt.value ? interp_eval(node->data.return_stmt.value) : value_null();
            return value_null();
        }

        case AST_BREAK: break_flag = 1; return value_null();
        case AST_CONTINUE: continue_flag = 1; return value_null();
        case AST_MEMBER: {
            Value *obj = interp_eval(node->data.member_op.object);
            if (obj->type == VAL_MAP) {
                return value_map_get(obj, node->data.member_op.member);
            }
            return value_null();
        }

        default:
            return value_null();
    }
    return value_null();
}

void repl() {
    printf("LavaScript Programming Language - Interactive REPL\n");
    printf("Beginner-Friendly • Turing-Complete • Production-Ready\n");
    printf("Type 'exit' to quit\n\n");

    while (1) {
        printf(">>> ");
        fflush(stdout);

        char line[4096];
        if (!fgets(line, sizeof(line), stdin)) break;

        if (strncmp(line, "exit", 4) == 0) break;

        Token *tokens = lexer_tokenize(line);
        Parser *parser = parser_new(tokens);
        ASTNode *ast = parser_parse_statement(parser);

        if (ast) {
            Value *result = interp_eval(ast);
            if (result->type == VAL_NUMBER) printf("%g\n", result->data.number);
            else if (result->type == VAL_STRING) printf("%s\n", result->data.string);
            else if (result->type == VAL_BOOL) printf("%s\n", result->data.boolean ? "true" : "false");
            else if (result->type == VAL_NULL) printf("null\n");
        }

        if (global_interp && global_interp->gc.count >= global_interp->gc.threshold) {
            gc_collect();
        }

        free(tokens);
        free(parser);
    }
}

int main(int argc, char **argv) {
    global_interp = malloc(sizeof(Interpreter));
    global_interp->variables = malloc(MAX_VARIABLES * sizeof(Variable));
    global_interp->var_count = 0;
    global_interp->scope_count = 0;
    global_interp->gc.head = NULL;
    global_interp->gc.count = 0;
    // --- START: GC DYNAMIC THRESHOLD main INIT ---
    global_interp->gc.collections_count = 0;
    global_interp->gc.threshold = GC_DEFAULT_THRESHOLD; // Initialize with the default
    // --- END: GC DYNAMIC THRESHOLD main INIT ---

    SSL_library_init();
    OpenSSL_add_all_algorithms();
    SSL_load_error_strings();

    if (argc > 1) {
        FILE *f = fopen(argv[1], "r");
        if (f) {
            fseek(f, 0, SEEK_END);
            long size = ftell(f);
            fseek(f, 0, SEEK_SET);
            char *code = malloc(size + 1);
            size_t read = fread(code, 1, size, f);
            code[read] = 0;
            fclose(f);

            Token *tokens = lexer_tokenize(code);
            Parser *parser = parser_new(tokens);
            ASTNode **statements = malloc(MAX_TOKENS * sizeof(ASTNode*));
            int stmt_count = 0;

            while (parser->lexer.current < parser->lexer.count - 1) {
                ASTNode *stmt = parser_parse_statement(parser);
                if (stmt) statements[stmt_count++] = stmt;
            }

            ASTNode *program = ast_block(statements, stmt_count);
            interp_eval(program);

            free(code);
            free(tokens);
            free(parser);
        } else {
            printf("Error: Could not open file %s\n", argv[1]);
        }
    } else {
        repl();
    }

    return 0;
}ts, stmt_count);
            interp_eval(program);

            free(code);
            free(tokens);
            free(parser);
        } else {
            printf("Error: Could not open file %s\n", argv[1]);
        }
    } else {
        repl();
    }

    return 0;
};
}

# ToyC Compiler

一个用OCaml实现的简单C语言编译器，能够将ToyC源代码编译为RISC-V汇编代码。

## 项目结构

```
ToyC/
├── src/                    # 源代码目录
│   ├── main.ml            # 主程序入口
│   ├── toyc_ast.ml        # 抽象语法树定义
│   ├── toyc_lexer.mll     # 词法分析器
│   ├── toyc_parser.mly    # 语法分析器
│   ├── toyc_semantic.ml   # 语义分析器
│   ├── toyc_codegen.ml    # 代码生成器
│   └── test/              # 测试文件
├── dune-project           # Dune构建配置
├── toyc.opam             # OCaml包管理配置
└── README.md             # 项目说明文档
```

## 功能特性

- **词法分析**：支持标识符、数字、关键字、运算符等token识别
- **语法分析**：支持函数定义、变量声明、表达式、控制流语句
- **语义分析**：类型检查、作用域管理、符号表维护
- **代码生成**：生成RISC-V汇编代码

### 支持的语言特性

- 基本数据类型：`int`
- 函数定义和调用
- 变量声明和赋值
- 算术运算：`+`, `-`, `*`, `/`
- 比较运算：`==`, `!=`, `<`, `>`, `<=`, `>=`
- 控制流：`if-else`, `while`
- 函数参数和返回值

## 构建和运行

### 环境要求

- OCaml 4.14+
- Dune 3.0+
- Menhir (语法分析器生成器)

### 构建项目

```bash
# 安装依赖
opam install dune menhir

# 构建项目
dune build

# 运行编译器
dune exec ./src/main.exe < input.tc
```

### 使用示例

创建一个ToyC源文件 `example.tc`：

```c
int factorial(int n) {
    if (n <= 1) {
        return 1;
    } else {
        return n * factorial(n - 1);
    }
}

int main() {
    return factorial(5);
}
```

编译并生成RISC-V汇编：

```bash
dune exec ./src/main.exe < example.tc
```

## 测试

项目包含多个测试用例：

- `test_input.tc` - 基本功能测试
- `test_function_call.tc` - 函数调用测试
- `test_comprehensive.tc` - 综合功能测试（递归函数）

运行测试：

```bash
# 测试基本功能
dune exec ./src/main.exe < test_input.tc

# 测试函数调用
dune exec ./src/main.exe < test_function_call.tc

# 测试递归函数
dune exec ./src/main.exe < test_comprehensive.tc
```

## 编译器架构

1. **词法分析** (`toyc_lexer.mll`) - 将源代码转换为token流
2. **语法分析** (`toyc_parser.mly`) - 将token流解析为抽象语法树
3. **语义分析** (`toyc_semantic.ml`) - 类型检查和符号表管理
4. **代码生成** (`toyc_codegen.ml`) - 生成RISC-V汇编代码

## 开发者

本项目作为编译原理课程的实践项目开发。

## 许可证

MIT License
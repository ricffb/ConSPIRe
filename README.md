# ConSPire

A Language and Tool to reason about data independence in CSP.

## Overview

The Project consists of 2 Parts:

+ `cspir`: A dialect of CSPm that is used to model data independent programs
+ `ConSPire`: A type checker for `cspir`.

## Installation

The tool is written in haskell and build with stack. You can use
```
cd ConSPire
stack install .
```
to compile and install the binary.

## Usage

After installing the tool and creating a `filename.cpsir` file you can run the tool on it
```
cpsir filename.cspir
```
The tool will then evaluate the assertions stated in the file.


# Cspir

The core of this tool is the CSP Intermediate Representation (cspir). 
While CSPm provides a feature rich functional language for data creation 
and manipulation, cspir is constraint to a few fundamental operators.


Consider the following CSP Process:

<img  src="https://render.githubusercontent.com/render/math?math=\text{NondReg}%20=%20in.x%20\rightarrow%20\text{Nondreg}%27(x)">
<img  src="https://render.githubusercontent.com/render/math?math=\text{NondReg}%27(x)%20=%20(in?y%20\rightarrow%20\text{if}\,x%20=%20y%20\,\text{then}\,\text{NondReg}%27(x)%20\,\text{else}\,\text{NondReg}%27(x)%20\sqcap%20\text{NondReg}%27(y))%20\,\square\,%20(out!x%20\rightarrow%20\text{NondReg}%27(x))">

We can translate this process to cspire:
```
typevar X
datatype T = in.X | out.X

NondReg = in?x -> NondReg'(x)

NondReg'(x : X) = (
    in?y -> if x==y then NondReg'(x) else NondReg'(x) |~| NondReg'(y)) 
  []
    (out!x -> NondReg'(x))

assert {} |- NondReg : Proc(T)
```

Similar to CSPm there are three main components making up a program file: `datatypes`,
`processes` and `asserts`.
The name for a data type must begin with a capital letter, while the name of a sum type
constructor must start with a lower case letter. () denotes the empty product type. We can
also declare type variables:
```
typevar X
```
We can translate the alphabet, ie., the set of all visible events occurring in NondReg, into a datatype in cspir.
```
datatype T = in.X | out.X
```
The description of a process is very similar to CSPm . A major variation is, that only ‘!’,
‘?’, and ‘$’ are allowed in a prefixing. We also require the arguments of a process to have
a type. This is because the argument syntax for processes is merely sugar for the actual
lambda functions that bind the arguments.

The `assert` consists of the type context Γ and the alphabet Σ.
In the NondReg example above we do not have a type context, ie., there are no free constants in the program. 
The alphabet in this example is `T = in.X | out.X`.

## Syntax

This section introduces the syntactic concepts of cspir. 
The calculus builds on the work by [Ranko Lazic](doc/semantic_study_of_di.pdf). 
Cspir is closely aligned to the language presented by Lazic in Chapter 2.

### Defining Data Types
The rules in this section are designed to be used in conjunction with the language proposal by Lazic.
The will follow the same order and show how those types translate in cspir. All datatype
names must start with a capital letter.

**Type Variable.**
Type Variables must start with a capital letter.
```
typevar X
```
**Sum Type.** 
Sum types consist of one or more identifiers followed by a type. The identifiers
must start with a lowercase letter.
```
datatype ST = id1.T1 | id2.T2 | idn.Tn
```
**Product Type.**
```
datatype PT = T1.T2.Tn
```
**Inductive Type.**
An example for an inductive type would be a list.
```
datatype ID = \Y -> nil.() | cont.T.Y
```
**Function Type.**
```
datatype Fun = T1 -> T2
```
**Builtin Types.**
The types Bool and Int are built in.
```
datatype UseBuiltins = Bool.Int
```

### Defining Terms

In this section we will use `r` for a term or more precise an expression representable in cspir.
Let `bexp` be a boolean expression and `nexp` be an expression yielding an integer.
**Sum Introduce.**
```
exp = id1.r
```
**Sum Eliminate.**
Let r be of type ST from Section B.1. The case need not be exhaustive.
```
exp = case r of id1 -> \y: T1 -> r1
of id2 -> \y: T2 -> r2
```
**If-Then-Else.**
```
exp = if bexp then r1 else r2
```
**Tuple Construct.**
```
exp = (r1, r2)
```
**Tuple Project.**
```
exp = pr nexp r
```
**Ind Introduce.**
There is no in keyword in cspir. The inductive type check will
automatically unfold the inductive type to fit the expression.
```
exp = cons.(1,nil.())
```
**Ind Eliminate.**
```
exp = fold r s
```
**Fun Abstract.**
```
exp = \y : T -> r
```
**Fun Apply.**
```
exp = r s
```
**Equality.**
```
bexp = r == s
bexp = r != s
```
**Math.**
```
nexp=nexp1+nexp2
nexp=nexp1∗nexp2
nexp=nexp1-nexp2
nexp=nexp1/nexp2
```

### Defining CSP Processes

Let datatype `Talph = id1.T11.T12 | id2.T21` be the alphabet, `v` be a variable name
starting with a lowercase letter, and `P`,`Q` be processes in the following rules. Let `S` be a Set
obeying the Set-rules in this section. **Processes must start with a capital letter**. This makes
a process definition distinguishable from an expression definition.
**Prefixing.**
```
Pr = id1!r1?v -> P
```
**External Choice.**
```
Pr = P [] Q
```
**Internal Coice.**
```
Pr = P |~| Q
```
**Replicated Internal Choice.**
```
Pr = |~| v : T @ P
```
**Parallel Composition.**
```
Pr = P [| S |] Q
```
**Hiding.**
```
Pr = P \ S
```
**Recursion.**
Recursion is implemented via process invocation. A process can invoke
another process including itself. At this moment a process may only be called with a list of
variable names, not with expressions.
```
Pr = id2?v -> Pr'(v)
Pr'(v: T21) = id2!v -> Pr'(v)
```
**Sets and Elems.** 
The elements in a set are expressions with the addition of a special
literal `∗{T}`. The `∗{T}` denotes that all elements of T are captured by S.
```
{ r1, r2, r3, id1.∗{T11.T12}}
```
**Let-Binding.** 
At this moment processes can only be called with variable names. New
variables binding an expression can be created using let statements
```
Pr = let v = exp within P
```
### Program File Format

A program file sets up the processes, data types and expressions that are used for the type
assertions.

**Assert.**
A type assertion is of the form:
```
assert { x1: T1, xn: Tn} |- Pr : Proc( Talph )
```

`x1` and `xn` are constants and `Pr` the process to be checked. `Talph` is a type serving as
alphabet.
A program file consists of any number of constructs. A construct is one of:
* A type definition `datatype ST = . . .`
* A type variable declaration `typevar X`
* A process definition `Pr = . . .`
* An expression definition followed by a semicolon `expr = . . . ;`
* An assert statement

Examples of such files can be found in the examples folder.












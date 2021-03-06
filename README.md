# Haski


The purpose of this artifact is to illustrate the writing of Haski programs in a Haskell environment and the inspection of C code generated by the Haski compiler---discussed in sections 2-6 of the paper. Specifically, this artifact contains the implementation of the Haski compiler and the source of the examples found in these sections. For a more up to date version of this artifact, we encourage the reader to check the repository at https://github.com/OctopiChalmers/haski.


At the time of writing this, the compiler does not provide a complete runtime system, which means that running the generated code requires manual intervention. For the convenience of the reader, some fully executable examples (which combine the generated code and manual additions) are also included in this artifact by marking the parts of the code that are generated (see `csamples` directory - `halexa/` implements the Halexa Bluetooth code while `octaviustemp/` implements the remote temperature & octavius Bluetooth code). 

The Haski compiler is a Haskell project written using the [GHC](https://www.haskell.org/platform/) compiler and the build tool [stack](https://docs.haskellstack.org/en/stable/README/), and hence using Haski requires these to be installed.


## Interacting with the source

Navigate to the directory of the project and then run:

```
[user]$ stack ghci
```
This loads `GHCi` with the required extensions and configuration, and loads all the files in the project.
Load some file containing Haski programs, such as:
```
*...> :l Haski.Example.Simple
```
To generate code for an example and inspect it, use the function `compile :: HT a => Haski (Stream a) -> IO ()`.
This function (defined in `Haski.Lang`) runs the compiler the prints the generated C-code to the terminal of the REPL.

```
*Haski.Example.Simple> compile nats
struct main_mem
{ int b;
};

void (main_reset(struct main_mem (* self))) {
  ((*(self)).b) = (0);
}

int (main_step(struct main_mem (* self))) {
  int a;
  (a) = ((*(self)).b);
  ((*(self)).b) = ((1) + (a));
  return a;
  
  ```

## Navigating the source

Here's a brief description of the `src` directory:

```
src/Haski     -- source of the compiler and examples
..Examples    -- all the examples
....Simple.hs -- examples suitable for starting with Haski
....Cache.hs  -- a sample implementation of a cache mechanism in Haski
....Paper.hs  -- examples from the paper
....csamples  -- contains executable C code for some examples
..DCLabel     -- clone of the `dclabel-0.0.6` package with some fixes
..Backend     -- backend implementations
....C.hs      -- C backend
..*.hs        -- source files of the compiler (Lang.hs is a good starting point)
```


## Writing Haski programs

This project can be used as a library to write Haski programs. To do this, run `stack install`
in the directory of the project. Note that this only registers the package, and does not
generate any executables. To write a `Haski` program, we start out by importing the `Haski.Lang` module 
and adding the necessary extensions `LambdaCase` and `RecursiveDo`.

```
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecursiveDo #-}

module MyModule where

import Haski.Lang

// your code here

```
## Known issues

Currently there's a bug in the node parser (in `Haski.Lang`) which prevents the compiler from generating correct code for
a node which calls another node. This is entirely an implementation issue and doesn't invalidate the design of our compiler. 
To circumvent this bug (till it's fixed), we may simple remove the `node` combinator from the called node. This causes
the body of the called node to be inlined and thus yields similar runtime behavior---albeit at the cost of inlining. 


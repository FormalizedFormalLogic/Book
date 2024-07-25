# [Book of Formalized Formal Logic](https://formalizedformallogic.github.io/Book/)

[![Deploy Status](https://github.com/FormalizedFormalLogic/book/actions/workflows/deploy.yml/badge.svg)](https://github.com/FormalizedFormalLogic/book/actions/workflows/deploy.yml)

Summary and brief explanation of formalized results in this project.

## Contributing

If you find a typo, spelling error or else, feel free to report us. [Issues](https://github.com/FormalizedFormalLogic/Book/issues) and [pull requests](https://github.com/FormalizedFormalLogic/Book/pulls) are welcome.

### Compile

To compile this book, you need bookmd and some plugins.

- [mdbook](https://github.com/rust-lang/mdBook)
- [mdbook-katex](https://github.com/lzanini/mdbook-katex) for [KaTeX](https://katex.org/)

```shell
mdbook serve md

mdbook build md
```

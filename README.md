# liquidhaskell-course
Course on Liquid Haskell 


## Building

### Deploy on Github

```
$ cp package.yaml.pandoc package.yaml
$ mkdir _site dist
$ stack install pandoc
$ make html
$ make pdf
$ cp dist/pbook.pdf _site/book.pdf
```

#### Producing .pdf Book

```bash
$ make pdf
$ evince dist/pbook.pdf
```


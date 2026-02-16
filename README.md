The `fduthesis` Class
=====================

*LaTeX thesis template for Fudan University, v0.9a*

Overview
--------

This template supports doctoral or master dissertion and undergraduate
thesis, both in Chinese or English. With the help of modern LaTeX
technology, `fduthesis` aims to create a simple interface, a normative
format, as well as a hackable class for the users.

At present, `fduthesis` only supports XeTeX and LuaTeX engines.
Support for pdfTeX and [ApTeX](https://github.com/clerkma/ptex-ng) is
still under development. `fduthesis` only allows UTF-8 encoding.

The documentation can be found in
[fduthesis.pdf](http://mirrors.ctan.org/macros/latex/contrib/fduthesis/fduthesis.pdf)
(in Chinese) or
[fduthesis-en.pdf](http://mirrors.ctan.org/macros/latex/contrib/fduthesis/fduthesis-en.pdf)
(in English).

GitHub repository: <https://github.com/stone-zeng/fduthesis>.

Installation
------------

To install `fduthesis`, you can use one of the following methods:

- If you are running TeX Live, the simplest way is to run

      tlmgr install fduthesis

- Download
  [fduthesis.tds.zip](http://mirror.ctan.org/install/macros/latex/contrib/fduthesis.tds.zip)
  from CTAN, extract it in the root of one of your TDS trees, and
  update the filename database.

- Get the source from GitHub:

      git clone https://github.com/stone-zeng/fduthesis.git

  Run `install-win.bat` (Windows) or `install-unix.sh` (Linux or macOS)
  to generate the templates and configuration files. These files would
  be found in a new-created `thesis` folder. You can enjoy `fduthesis`
  here at once.

  For permanent installation, you may move the following files into a
  directory where LaTeX will find them (e.g.
  `TEXMF/tex/latex/fduthesis/`):

  - `fduthesis.cls`
  - `fduthesis-en.cls`
  - `fduthesis.def`
  - `fdudoc.cls`
  - `fdulogo.sty`
  - `fudan-emblem.pdf`
  - `fudan-emblem-new.pdf`
  - `fudan-name.pdf`

  Do not forget to update the filename database afterwards.

Contributing
------------

[Issues](https://github.com/stone-zeng/fduthesis/issues) and
[pull requests](https://github.com/stone-zeng/fduthesis/pulls)
are always welcome.

License
-------

This work may be distributed and/or modified under the conditions of
the [LaTeX Project Public License](http://www.latex-project.org/lppl.txt),
either version 1.3c of this license or (at your option) any later
version.

-----

Copyright (C) 2017&ndash;2024 by Xiangdong Zeng <xdzeng96@gmail.com>.

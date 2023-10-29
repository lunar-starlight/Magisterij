% LTeX: enabled=false
\newcommand\fileversion{1.1.0}
\newcommand\filedate{2022-03-06}
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{fmfdelo-muf}[\filedate\space FMFdelo by Strah (v\fileversion)]

\RequirePackage{etoolbox, ifthen, keyval}

\newcommand{\@ifthen}[2]{\ifthenelse{#1}{#2}{\relax}}
\newcommand{\@unless}[2]{\ifthenelse{#1}{\relax}{#2}}
\newcommand{\@blank}[1]{\equal{#1}{}}

\newboolean{@english}
\newboolean{@print}

\DeclareOption{mat1}{\def\@program{Matematika}\def\@stopnja{1.~stopnja}\def\@tipdela{Delo diplomskega seminarja}}
\DeclareOption{fin1}{\def\@program{Finančna matematika}\def\@stopnja{1.~stopnja}\def\@tipdela{Delo diplomskega seminarja}}
\DeclareOption{isrm1}{\def\@program{Interdisciplinarni študij računalništva in matematike}\def\@stopnja{1.~stopnja}\def\@tipdela{Delo diplomskega seminarja}}
\DeclareOption{mat2}{\def\@program{Matematika}\def\@stopnja{2.~stopnja}\def\@tipdela{Magistrsko delo}}
\DeclareOption{fin2}{\def\@program{Finančna matematika}\def\@stopnja{2.~stopnja}\def\@tipdela{Magistrsko delo}}
\DeclareOption{isrm2}{\def\@program{Interdisciplinarni študij računalništva in matematike}\def\@stopnja{2.~stopnja}\def\@tipdela{Magistrsko delo}}

\DeclareOption{en}{\setboolean{@english}{true}}
\DeclareOption{print}{\setboolean{@print}{true}}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{amsart}}

\ProcessOptions\relax

\RequirePackage{newfile}
\AtEndPreamble{%
  \newoutputstream{xmpdatafile}
  \openoutputfile{\jobname.xmpdata}{xmpdatafile}
    \addtostream{xmpdatafile}{%
    \protect\Title{\@naslov}
    \protect\Author{\@avtor}
    \protect\Keywords{\@kljucnebesede}
    \protect\Subject{matematika}
  }
}

\LoadClass[a4paper,12pt]{amsart}

\RequirePackage[a-2b]{pdfx}

\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{amsfonts}
\RequirePackage{amsthm}

\RequirePackage{fontspec}
\RequirePackage{unicode-math}

\RequirePackage{polyglossia}
% \RequirePackage[backend=biber,bibencoding=utf8,style=numeric]{biblatex}
\RequirePackage{doi}
% \def\printbibliography{%
%   \bibliographystyle{fmf-sl}
%   \bibliography{diploma}
% }

\RequirePackage{qcircuit}
\RequirePackage{tikz}
  \usetikzlibrary{cd}
  \usetikzlibrary{babel}
  \usetikzlibrary{angles,quotes}
\RequirePackage{quiver}
\RequirePackage{mathpartir}
\RequirePackage{minted}
\RequirePackage[shortlabels]{enumitem}

\ifthenelse{\boolean{@english}}{
  \RequirePackage[style=english]{csquotes}
}{
  \RequirePackage[style=german]{csquotes}
}
\RequirePackage{stmaryrd}

\RequirePackage[normalem]{ulem}
\renewcommand{\ULdepth}{1.8pt}
\newcommand{\ul}[1]{\uline{#1}}

% \setmainfont{TeX Gyre Pagella}
% \setmathfont{TeX Gyre Pagella Math}
\setmathfont{Asana Math}
\setmathfont{Latin Modern Math}
\setmathfont{Asana Math}[range={scr}]
\setmathfont{STIX Two Math-Regular}[range={bb,"1D538-"1D56B,"0211D}]
\setmathfont{STIX Two Math-Regular}[range={"2102,"210D,"2115,"2119,"211A,"211D,"2124}]
% \setmathfont{Asana Math}[range={"007B,"007D}]  % {}
\setmathfont{Asana Math}[range={8709,"29B6,"2987,"2988}]  % U+2205, emptyset, ⦶, ⦇, ⦈
\ifthenelse{\boolean{@english}}{
}{
  \setmainlanguage{slovene}
  \setotherlanguage{english}
  % \DeclareLanguageMapping{slovenian}{slovene}
}

\hypersetup{%
  psdextra,
  bookmarksopen,
  bookmarksdepth=3, 
  % final=true,
  % pdfdisplaydoctitle=false,
  % plainpages=false, 
  % pdfstartview=,
  % pdftoolbar=true,
  % pdfmenubar=true,
  % bookmarksopen=true,
  % bookmarksopenlevel=0,
  % bookmarksnumbered=true,
  % breaklinks=true,
  % linktocpage,
  % hidelinks,
  colorlinks=true,
  linkcolor=blue,
  urlcolor =blue,
  citecolor=red,
  anchorcolor=green,
  % pdfpagelayout=OneColumn,
  % pdfpagemode=UseOutlines,
  pdfencoding=unicode,
}
\ifthenelse{\boolean{@english}}{
  \hypersetup{pdflang=en}
}{
  \hypersetup{pdflang=sl}
}

\textwidth 15cm
\textheight 24cm
\oddsidemargin.5cm
\evensidemargin.5cm
\topmargin-5mm
\addtolength{\footskip}{10pt}
\pagestyle{plain}
\overfullrule=15pt

\def\@mentorji{}
\newcommand{\dodajmentorja}[2]{%
  \g@addto@macro\@mentorji{#1: & #2 \\}%
}
\newcommand{\dodajdvamentorja}[3]{%
  \g@addto@macro\@mentorji{#1: & #2 \\ & #3 \\}%
}
\newcommand{\mentor}[1]{\dodajmentorja{Mentor}{#1}}
\newcommand{\somentor}[1]{\dodajmentorja{Somentor}{#1}}
\newcommand{\mentorica}[1]{\dodajmentorja{Mentorica}{#1}}
\newcommand{\somentorica}[1]{\dodajmentorja{Somentorica}{#1}}
\newcommand{\mentorja}[2]{\dodajdvamentorja{Mentorja}{#1}{#2}}
\newcommand{\somentorja}[2]{\dodajdvamentorja{Somentorja}{#1}{#2}}
\newcommand{\mentorici}[2]{\dodajdvamentorja{Mentorici}{#1}{#2}}
\newcommand{\somentorici}[2]{\dodajdvamentorja{Somentorici}{#1}{#2}}
\newcommand{\program}[1]{\def\@program{#1}}
\newcommand{\avtor}[1]{\def\@avtor{#1}}
\newcommand{\naslov}[1]{\def\@naslov{#1}}
\renewcommand{\title}[1]{\def\@title{#1}}
\newcommand{\letnica}[1]{\def\@letnica{#1}}
\newcommand{\povzetek}[1]{\def\@povzetek{#1}}
\renewcommand{\abstract}[1]{\def\@abstract{#1}}
\newcommand{\klasifikacija}[1]{\def\@klasifikacija{#1}}
\newcommand{\kljucnebesede}[1]{\def\@kljucnebesede{#1}}
\renewcommand{\keywords}[1]{\def\@keywords{#1}}

\newtheorem{theorem}{Izrek}[section]
\newtheorem{proposition}[theorem]{Trditev}
\newtheorem{lemma}[theorem]{Lema}
\newtheorem*{corrolary}{Posledica}

\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definicija}

\newtheorem{example*}{Primer}[section]
\newtheorem*{@example}{Primer}
\newtheorem*{@examples}{Primeri}

\newenvironment{example}[1][]{\begin{@example}[#1]\renewcommand*{\qedsymbol}{$\diamondsuit$}\pushQED{\qed}}{\popQED\end{@example}}
\newenvironment{examples}[1][]{\begin{@examples}[#1]\renewcommand*{\qedsymbol}{$\diamondsuit$}\pushQED{\qed}}{\popQED\end{@examples}}

\theoremstyle{remark}
\newtheorem*{remark}{Opomba}
\newtheorem*{convention}{Dogovor}

\newcounter{axiom}
\setcounter{axiom}{0}
\renewcommand\theaxiom{\Alph{axiom}}
\newenvironment{axiom}[2][-1]{
    \ifnum#1>0
        \refsetcounter{axiom}{#1}
    \fi
    \refstepcounter{axiom}
    \setlength\parindent{0pt}
    \ifblank{#2}{}{\vskip.5em #2\par}
    \nopagebreak
    \textbf{Aksiom \theaxiom.}
}{
}

% ukaz za slovarsko geslo
\newcommand{\geslo}[2]{\noindent\textbf{#1}\hspace*{3mm}\hangindent=\parindent\hangafter=1 #2\par}

% Ukaz za izpis začetnih strani.
\AfterEndPreamble{%

\thispagestyle{empty}
\noindent{\large
UNIVERZA V LJUBLJANI\\[1mm]
FAKULTETA ZA MATEMATIKO IN FIZIKO\\[5mm]
\@program\ -- \@stopnja}
\vfill

\begin{center}{\large
\@avtor\\[2mm]
{\bf \@naslov}\\[10mm]
\@tipdela\\[1cm]
\begin{tabular}{rl} \@mentorji \end{tabular}
}
\end{center}
\vfill

\noindent{\large
Ljubljana, \@letnica}
\pagebreak

\thispagestyle{empty}
\tableofcontents
\vfill
\pagebreak

\thispagestyle{empty}
\begin{center}
{\bf \@naslov}\\[3mm]
{\sc Povzetek}
\end{center}
\@povzetek
\vfill
\begin{center}
{\bf \@title}\\[3mm]
{\sc Abstract}
\end{center}
\@abstract
\vfill\noindent
{\bf Math. Subj. Class. (2020):} \@klasifikacija \\[1mm]
{\bf Ključne besede:} \@kljucnebesede \\[1mm]
{\bf Keywords:} \@keywords
\pagebreak
\setcounter{page}{0}
}

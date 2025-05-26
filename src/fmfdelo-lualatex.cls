\newcommand\fileversion{1.1.0}
\newcommand\filedate{2024-01-26}
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{fmfdelo-lualatex}[\filedate\space Zakljucna dela na FMF lualatex (v\fileversion)]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% NALAGANJE PAKETOV
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

\RequirePackage{pdf14}
\RequirePackage{amsfonts,amsmath,amssymb,amsthm}
\RequirePackage{lmodern}
\RequirePackage{newfile}
\RequirePackage{etoolbox}
\RequirePackage{ifthen}
\RequirePackage{keyval}
\RequirePackage{makeidx}
\def\normalsize{}
\RequirePackage{fontspec}
\RequirePackage{stmaryrd}
% \RequirePackage{lualatex-math}
\RequirePackage{mathtools}
\RequirePackage{unicode-math}
\RequirePackage{polyglossia}
% \RequirePackage{doi}
\RequirePackage{enumerate}
\RequirePackage{tikz}
\usetikzlibrary{babel}
\usetikzlibrary{cd,positioning}
\usetikzlibrary{angles,quotes}

\newcommand{\@ifthen}[2]{\ifthenelse{#1}{#2}{\relax}}
\newcommand{\@unless}[2]{\ifthenelse{#1}{\relax}{#2}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OPCIJE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newboolean{@drugastopnja}
\newboolean{@enovitistudij}
\newboolean{@fri}
\newboolean{@anglescina}
\newboolean{@tisk}
\newboolean{@trst}
\newcommand{\@sloeng}[2]{\ifthenelse{\boolean{@anglescina}}{#2}{#1}}
\newcommand{\@iftrst}[2]{\@ifthen{\boolean{@trst}}{#1}}
\def\@bibbackend{biber}
\def\@citationstyle{numeric}

\DeclareOption{anglescina}{\setboolean{@anglescina}{true}}
\DeclareOption{mat1}{
  \def\@program{Matematika}
  \def\@programme{Mathematics}
}
\DeclareOption{fin1}{
  \def\@program{Finančna matematika}
  \def\@programme{Financial Mathematics}
}
\DeclareOption{mat2}{
  \def\@program{Matematika}
  \def\@programme{Mathematics}
  \setboolean{@drugastopnja}{true}
}
\DeclareOption{fin2}{
  \def\@program{Finančna matematika}
  \def\@programme{Financial Mathematics}
  \setboolean{@drugastopnja}{true}
}
\DeclareOption{isrm2}{
  \def\@program{Računalništvo in matematika}
  \def\@programme{Computer Science and Mathematics}
  \setboolean{@drugastopnja}{true}
  \setboolean{@fri}{true}
}
\DeclareOption{ped}{
  \def\@program{Pedagoška matematika}
  \def\@programme{Mathematics Education}
  \setboolean{@drugastopnja}{true}
  \setboolean{@enovitistudij}{true}
}
\DeclareOption{tisk}{
  \setboolean{@tisk}{true}
  \PassOptionsToClass{twoside}{article}
}
\DeclareOption{bibtex}{
  \def\@bibbackend{bibtex}
}
\DeclareOption{alpha}{
  \def\@citationstyle{alphabetic}
}
\DeclareOption{trst1}{
  \setboolean{@anglescina}{true}
  \setboolean{@trst}{true}
  \def\@programme{Programme for a double diploma in mathematics}
  \def\@it@thesistype{Tesi finale}
}
\DeclareOption{trst2}{
  \setboolean{@anglescina}{true}
  \setboolean{@trst}{true}
  \setboolean{@drugastopnja}{true}
  \def\@programme{Programme for a double master's degree in mathematics}
  \def\@it@thesistype{Tesi finale}
}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}

\ProcessOptions\relax
\LoadClass[12pt, a4paper]{article}
\ifthenelse{\boolean{@drugastopnja}}{
  \def\@stopnja{2. stopnja}
  \def\@tipdela{Magistrsko delo}
  \def\@cycle{2nd cycle}
  \def\@thesistype{Master's thesis}
}{
  \def\@stopnja{1. stopnja}
  \def\@tipdela{Delo diplomskega seminarja}
  \def\@cycle{1st cycle}
  \def\@thesistype{Diploma seminar work}
}

\@sloeng{
  \setmainlanguage{slovene}
  \setotherlanguage{english}
  \RequirePackage[style=german]{csquotes}
}{
  \setmainlanguage{english}
  \RequirePackage[style=english]{csquotes}
}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% NASTAVITEV FONTOV
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\setmainfont{Latin Modern Roman}
% \setmainfont{TeX Gyre Pagella}
% \setmathfont{TeX Gyre Pagella Math}
\setmathfont{Latin Modern Math}
\setmathfont{Asana Math}[range={scr}]
\setmathfont{STIX Two Math-Regular}[range={bb,"1D538-"1D56B,"0211D}]
\setmathfont{STIX Two Math-Regular}[range={"2102,"210D,"2115,"2119,"211A,"211D,"2124}]
% \setmathfont{TeX Gyre Pagella Math}[range={8730}]
% \setmathfont{Asana Math}[range={"007B,"007D}]  % {}
\setmathfont{Asana Math}[range={8709, \setminus, "2216, "29F5}]  % U+2205, emptyset
%\setmathfont{Asana Math}[range={"3088}] % U+3088, よ
%\setmathfont{Source Han Sans JP}[range={"3088}, math-style=TeX] % U+3088, よ
%\newfontfamily\cjkfont[Script=CJK]{Kochi Mincho}
%\setmathfont[range={"3088}]{Source Han Sans JP}
%%------ workaround ------
%
%%usage: \adjustmathfont{arg1}{arg2}{arg3}
%%   where  arg1 is the beginning of the unicode range, e.g. "4E00
%%          arg2 is the end of the unicode range, e.g. "9FFF
%%          arg3 is the font number, e.g. "4
%\newcounter{my@char}
%\newcommand{\adjustmathfont}[3]{%
%  \ifnumgreater{#1}{#2}{%
%    \PackageWarning{}{No adjustment of math font since #1 is greater than #2.}
%  }{
%    \setcounter{my@char}{#1}
%    \Umathcode\value{my@char}="0 #3 \value{my@char}
%    \whileboolexpr{%
%      test {\ifnumless{\value{my@char}}{#2}} 
%    }{%
%      \stepcounter{my@char}
%      \Umathcode\value{my@char}="0 #3 \value{my@char}
%    }
%  }
%}
%\adjustmathfont{"3088}{"3088}{"10}

\RequirePackage{luatexja}
%\RequirePackage{luatexja-fontspec}




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% VNOS METAPODATKOV
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\@definefield}[2]{
  % \definefield{@imepolja}{...} načeloma naredi \def\@imepolja{...},
  % le da pri tem iz ... pobriše presledke
  % Iz imena ukaza dobimo ukaz s pomočjo \csname kot
  %   \csname imeukaza\endcsname ~> \imeukaza
  % Če bi napisali \def\csname @imepolja\endcsname{...} bi to povozilo ukaz
  % \csname, zato moramo uporabiti \expandafter, da najprej izvedemo \csname,
  % šele nato \def.
  \expandafter\def\csname #1\endcsname{\ifblank{#2}{}{#2}}
}
\newcommand{\@definerequiredfield}[2]{
  \@definefield{#1}{#2}
  {
    % Ker ključne besede vsebujejo nedefinirano ločilo \sep, ga za potrebe
    % preverjanja lokalno definiramo (zato par zavitih oklepajev).
    \def\sep{\relax}
    \@ifthen{\equal{\csname #1\endcsname}{}}{
      \PackageError{fmfdelo}{Polje #1 je zahtevano.}{}
    }
  }
}
\def\@mentorji{}
\def\@supervisors{}
\def\@it@supervisors{}
\newcommand{\@dodajmentorja}[3]{%
  \g@addto@macro\@mentorji{#1: & #3 \\}%
}
\newcommand{\@dodajdvamentorja}[4]{%
  \g@addto@macro\@mentorji{#1: & #3 \\ & #4 \\}%
}
\newcommand{\@addsupervisor}[3]{%
  \g@addto@macro\@supervisors{#1: & #3 \\}%
}
\newcommand{\@addsupervisors}[4]{%
  \g@addto@macro\@supervisors{#1: & #3 \\ & #4 \\}%
}
\newcommand{\@it@addsupervisor}[3]{%
  \g@addto@macro\@it@supervisors{#1: & #3 \\}%
}
\newcommand{\@it@addsupervisors}[4]{%
  \g@addto@macro\@it@supervisors{#1: & #3 \\ & #4 \\}%
}

\newcommand{\avtor}{\@definerequiredfield{@avtor}}
\newcommand{\naslov}{\@definerequiredfield{@naslov}}
\renewcommand{\title}{\@definerequiredfield{@title}}
\newcommand{\letnica}{\@definerequiredfield{@letnica}}
\newcommand{\zahvala}{\@definefield{@zahvala}}
\newcommand{\osnovnaliteratura}{\@definefield{@osnovnaliteratura}}
\newcommand{\povzetek}{\@definerequiredfield{@povzetek}}
\renewcommand{\abstract}{\@definerequiredfield{@abstract}}
\newcommand{\klasifikacija}{\@definerequiredfield{@klasifikacija}}
\newcommand{\kljucnebesede}{\@definerequiredfield{@kljucnebesede}}
\newcommand{\keywords}{\@definerequiredfield{@keywords}}
\newcommand{\slovar}{\@definefield{@slovar}}
\newcommand{\literatura}{\@definefield{@literatura}}

\@ifthen{\boolean{@anglescina}}{
  \newcommand{\razsirjenipovzetek}{\@definerequiredfield{@razsirjenipovzetek}}
}

\@ifthen{\boolean{@trst}}{
  \newcommand{\titolo}{\@definerequiredfield{@it@title}}
  \newcommand{\sommario}{\@definerequiredfield{@it@abstract}}
  \newcommand{\parolechiave}{\@definerequiredfield{@it@keywords}}
  \newcommand{\sintesiestesa}{\@definerequiredfield{@it@razsirjenipovzetek}}
}

\newcommand{\geslo}[2]{\noindent\textbf{#1}\hspace*{3mm}\hangindent=\parindent\hangafter=1 #2\par}

\newcommand{\mentor}{\@dodajmentorja{Mentor}{mentorja}}
\newcommand{\somentor}{\@dodajmentorja{Somentor}{somentorja}}
\newcommand{\mentorica}{\@dodajmentorja{Mentorica}{mentorice}}
\newcommand{\somentorica}{\@dodajmentorja{Somentorica}{somentorice}}
\newcommand{\mentorja}{\@dodajdvamentorja{Mentorja}{mentorjev}}
\newcommand{\somentorja}{\@dodajdvamentorja{Somentorja}{somentorjev}}
\newcommand{\mentorici}{\@dodajdvamentorja{Mentorici}{mentoric}}
\newcommand{\somentorici}{\@dodajdvamentorja{Somentorici}{somentoric}}
\newcommand{\supervisor}[1]{\@addsupervisor{Supervisor}{Supervisor's}{#1}}
\newcommand{\cosupervisor}[1]{\@addsupervisor{Co-supervisor}{Co-supervisor's}{#1}}
\newcommand{\supervisors}[2]{\@addsupervisors{Supervisors}{Supervisors'}{#1}{#2}}
\newcommand{\cosupervisors}[2]{\@addsupervisors{Co-supervisors}{Co-supervisors'}{#1}{#2}}
\newcommand{\supervisore}[1]{\@it@addsupervisor{Supervisore}{supervisore}{#1}}
\newcommand{\cosupervisore}[1]{\@it@addsupervisor{Co-supervisore}{co-supervisore}{#1}}
\newcommand{\supervisori}[2]{\@it@addsupervisors{Supervisori}{supervisorsi}{#1}{#2}}
\newcommand{\cosupervisori}[2]{\@it@addsupervisors{Co-supervisori}{co-supervisori}{#1}{#2}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% IZPIS PDF/A
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\AtEndPreamble{%
\let\oldtexorpdfstring\texorpdfstring
\renewcommand{\texorpdfstring}[2]{#2}
\let\sep{\protect\sep}
\newoutputstream{xmpdatafile}
\openoutputfile{\jobname.xmpdata}{xmpdatafile}
\ifthenelse{\boolean{@anglescina}}{
  \addtostream{xmpdatafile}{%
  \protect\Title{\@title}
  \protect\Author{\@avtor}
  \protect\Keywords{\@keywords}
  \protect\Subject{\@thesistype, \@programme, \@klasifikacija}
}}{
  \addtostream{xmpdatafile}{%
  \protect\Title{\@naslov}
  \protect\Author{\@avtor}
  \protect\Keywords{\@kljucnebesede}
  \protect\Subject{\@tipdela, \@program, \@klasifikacija}
}}
\closeoutputstream{xmpdatafile}

\let\texorpdfstring\oldtexorpdfstring

% Nalozimo paket za zagotavljanje PDF/A-2B (ustrezni fonti, barvni profili, UTF-8 zapis simbolov, ...)
\RequirePackage[a-2b,pdf17]{pdfx}
\ifthenelse{\boolean{@tisk}}{
  \definecolor{linkcolor}{RGB}{0,0,0}
}{
  \definecolor{linkcolor}{RGB}{0,84,147}
}
\hypersetup{bookmarksopen, bookmarksdepth=3, colorlinks=true,
  linkcolor=linkcolor, anchorcolor=linkcolor, citecolor=linkcolor, filecolor=linkcolor,
  menucolor=linkcolor, runcolor=linkcolor, urlcolor=linkcolor, pdfencoding=auto,
  breaklinks=true, psdextra}
}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% BIBLIOGRAFIJA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\RequirePackage[style=\@citationstyle,
                hyperref=auto,
                isbn=false,
                doi=true,
                url=false,
                date=year,
                giveninits=true,
                maxnames=3,
                useprefix=true,
                backend=\@bibbackend]{biblatex}

\AtEndPreamble{%
\ifdefined\@literatura
\addbibresource{\@literatura}
\fi
\@sloeng{
  \DefineBibliographyStrings{slovene}{%
    bathesis  = {diplomsko delo},
    mathesis  = {magistrsko delo},
    phdthesis = {doktorska disertacija},
    urlfrom   = {dostopno na},
    urlseen   = {ogled},
    andothers = {in dr.},
  }
}{
  \DefineBibliographyStrings{english}{%
    bathesis  = {Bachelor's thesis},
    mathesis  = {Master's thesis},
  }
}
% fix spacing
\setlength{\biblabelsep}{\labelsep}
\setlength{\bibitemsep}{1.5\itemsep}
% redeclare unit separator from period to comma
\renewcommand*{\newunitpunct}{\addcomma\space}
% re-declare field formats (font, brackets ...)
% omit " around title and make it italic
\DeclareFieldFormat*{title}{\textit{#1}}
% omit italics
\DeclareFieldFormat*{journaltitle}{#1}
\DeclareFieldFormat*{booktitle}{#1}
\DeclareFieldFormat*{plain}{#1}
% put brackets around number
\DeclareFieldFormat*{number}{\mkbibparens{#1}}

\@unless{\boolean{@anglescina}}{
% capitalise according to slovenian rules
\DeclareFieldFormat{sentencecase}{\MakeSentenceCase{#1}}
\renewbibmacro*{title}{%
  \ifthenelse{\iffieldundef{title}\AND\iffieldundef{subtitle}}
    {}
    {\ifthenelse{\ifentrytype{article}\OR\ifentrytype{inbook}%
      \OR\ifentrytype{incollection}\OR\ifentrytype{inproceedings}%
      \OR\ifentrytype{inreference}\OR\ifentrytype{book}}
      {\printtext[title]{%
        \printfield[sentencecase]{title}%
        \setunit{\subtitlepunct}%
        \printfield[sentencecase]{subtitle}}}%
      {\printtext[title]{%
        \printfield[titlecase]{title}%
        \setunit{\subtitlepunct}%
        \printfield[titlecase]{subtitle}}}%
     \newunit}%
  \printfield{titleaddon}}
}

% remove v:
\DeclareBibliographyDriver{article}{%
  \usebibmacro{bibindex}%
  \usebibmacro{begentry}%
  \usebibmacro{author/translator+others}%
  \setunit{\printdelim{nametitledelim}}\newblock
  \usebibmacro{title}%
  \newunit
  \printlist{language}%
  \newunit\newblock
  \usebibmacro{byauthor}%
  \newunit\newblock
  \usebibmacro{bytranslator+others}%
  \newunit\newblock
  \printfield{version}%
  \newunit\newblock
  % \usebibmacro{in:}%
  \usebibmacro{journal+issuetitle}%
  \newunit
  \usebibmacro{byeditor+others}%
  \newunit
  \usebibmacro{note+pages}%
  \newunit\newblock
  \iftoggle{bbx:isbn}
    {\printfield{issn}}
    {}%
  \newunit\newblock
  \usebibmacro{doi+eprint+url}%
  \newunit\newblock
  \usebibmacro{addendum+pubstate}%
  \setunit{\bibpagerefpunct}\newblock
  \usebibmacro{pageref}%
  \newunit\newblock
  \iftoggle{bbx:related}
    {\usebibmacro{related:init}%
     \usebibmacro{related}}
    {}%
  \usebibmacro{finentry}}

% print format <vol>(<number>) (year) <pages>
% remove str. for article (and periodical?)
\renewbibmacro*{volume+number+eid}{%
  \printfield[bold]{volume}%
  \printfield{number}%
  \setunit{\space}%
  \printfield[number]{year}%
  \setunit{\space}%
  \printfield[plain]{pages}}

% do not print the pages in this part (already done before)
\renewbibmacro*{note+pages}{%
  \printfield{note}}
% do not print the year in this part (already done before)
\renewbibmacro*{issue+date}{}
% print format <publisher>, <location>, year
\renewbibmacro*{publisher+location+date}{%
  \printlist{publisher}%
  \setunit{\addcomma\space}%
  \printlist{location}%
  \setunit{\addcomma\space}%
  \printfield{year}}

\renewbibmacro*{byeditor+others}{%
  \ifnameundef{editor}
    {}
    {\addspace%
    \mkbibparens{%
      \setunit{}%
      \usebibmacro{byeditor+othersstrg}%
      \setunit{\addspace}%
      \printnames[byeditor]{editor}%
      \clearname{editor}%
      \newunit}}%
  \usebibmacro{byeditorx}%
  \usebibmacro{bytranslator+others}}

\DeclareFieldFormat*{volume}{}
\renewbibmacro*{series+number}{%
  \printfield{series}%
  \setunit{\space}%
  \printfield[bold]{volume}}

\DeclareFieldFormat{url}{\bibstring{urlfrom}\space\url{#1}}
\DeclareFieldFormat{urldate}{\mkbibbrackets{\bibstring{urlseen}\space#1}}
\renewbibmacro*{url+urldate}{%
  \usebibmacro{urldate}%
  \newunit%
  \printfield{url}}

% automatically strip `van` and `von` from start of surname,
% if `sortname` is not already defined
% vir: https://tex.stackexchange.com/a/136565
\DeclareSourcemap{%
  \maps[datatype=bibtex]{
    \map[overwrite=false]{
      \step[fieldsource=translator]
      \step[fieldset=sortname, origfieldval]
      \step[fieldsource=editor]
      \step[fieldset=sortname, origfieldval]
      \step[fieldsource=author]
      \step[fieldset=sortname, origfieldval]
    }
    \map[overwrite=false]{
      \step[fieldsource=sortname, match=\regexp{(^|\s+)\Kv[a|o]n\s+}, replace={$1}]%$
    }
  }
}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DIMENZIJE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\textwidth 15cm
\textheight 24cm
\oddsidemargin.5cm
\evensidemargin.5cm
\topmargin-5mm
\addtolength{\footskip}{10pt}
\overfullrule=15pt

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% RAZNO
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\newcommand{\newdef}[1]{
  \theoremstyle{definition}
  \newtheorem{#1}[definicija]{\MakeUppercase #1}
}
\newcommand{\newex}[2]{
  \theoremstyle{definition}
  \newtheorem{#1*}[definicija]{\MakeUppercase #1}
  \newenvironment{#1}[1][]{
    \begin{#1*}[##1]\renewcommand*{\qedsymbol}{\(#2\)}\pushQED{\qed}
  }{
    \popQED\end{#1*}
  }
}

\newcommand{\newthm}[1]{
  \theoremstyle{plain}
  \newtheorem{#1}[definicija]{\MakeUppercase #1}
}

\newcommand{\newpf}[2]{
  \newenvironment{#1}[1][\MakeUppercase #1]{
    \begin{proof}[##1]\renewcommand*{\qedsymbol}{\(#2\)}
    }{
    \end{proof}
  }
}

\def\stripstar[#1*]{#1}


% pokončno napisan tekst
\theoremstyle{definition}
\newtheorem{definicija}{Definicija}[section]
\newdef{aksiom}
\newdef{opomba}
\newex{primer}{\diamondsuit}
\newex{zgled}{\diamondsuit}
\@ifthen{\boolean{@anglescina}}{
  \newdef{definition}
  \newdef{axiom}
  \newdef{remark}
  \newex{example}{\diamondsuit}
}

% poševno napisan tekst
\newthm{lema}
\newthm{izrek}
\newthm{trditev}
\newthm{posledica}
\@ifthen{\boolean{@anglescina}}{
\newthm{lemma}
\newthm{theorem}
\newthm{proposition}
\newthm{corollary}
}
\@ifthen{\boolean{@trst}}{
\newthm{teorema}
\newthm{proposicione}
\newthm{corollario}
\newpf{dimostrazione}
}

\numberwithin{equation}{section}  % števec za enačbe zgleda kot (2.7) in se resetira v vsakem razdelku
\newpf{dokaz}{\square}
%\newenvironment{dokaz}[1][Dokaz]{\begin{proof}[#1]}{\end{proof}}

% bold matematika znotraj \textbf{ }, tudi v naslovih
\g@addto@macro\bfseries{\boldmath}

% Poimenuj kazalo slik kot ``Kazalo slik'' in ne ``Slike''
\addto\captionsslovene{
  \renewcommand{\listfigurename}{Kazalo slik}%
}

% generiraj vsebinsko kazalo
\makeindex

\defbibenvironment{keyrefs}
  {\begin{enumerate}}
  {\end{enumerate}}
  {\item}
\DeclareBibliographyCategory{keyreferences}
\BiblatexSplitbibDefernumbersWarningOff

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% IZPIS ZAČETNIH STRANI
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\@sloeng{\def\@frontpages{\@frontpages@sl}}{\def\@frontpages{\@frontpages@en}}
\@ifthen{\boolean{@trst}}{\def\@frontpages{\@frontpages@trst}}

\def\@frontpages@sl{
  \@frontpages@sl@naslovnica
  \@frontpages@sl@zahvala
  \@frontpages@common@toc

  \pdfbookmark[1]{Povzetek}{povzetek}
  \@frontpages@sl@povzetek
  \@frontpages@en@abstract
  \@frontpages@sl@kljucnebesede
  \cleardoublepage
}
\def\@frontpages@en{
  \@frontpages@en@frontpage
  \@frontpages@sl@naslovnica
  \@frontpages@en@acknowledgements
  \@frontpages@common@toc

  \pdfbookmark[1]{Abstract}{abstract}
  \@frontpages@en@abstract
  \@frontpages@sl@povzetek
  \@frontpages@en@keywords
  \cleardoublepage
}
\def\@frontpages@trst{
  \@frontpages@trst@en@frontpage
  \@frontpages@trst@itslo@frontpage
  \@frontpages@en@acknowledgements
  \@frontpages@common@toc

  \pdfbookmark[1]{Abstract}{abstract}
  \@frontpages@en@abstract
  \@frontpages@trst@abstract
  \@frontpages@sl@povzetek
  \@frontpages@trst@keywords
  \cleardoublepage
}

\def\@frontpages@common@toc{
  \pdfbookmark[1]{\contentsname}{kazalo-vsebine}
  \tableofcontents
  \vfill
  \cleardoublepage
}
\def\@frontpages@sl@naslovnica{
  \thispagestyle{empty}
  \noindent
  {\large
  UNIVERZA V LJUBLJANI\\[1mm]
  FAKULTETA ZA MATEMATIKO IN FIZIKO
  \@ifthen{\boolean{@fri}}{\\[1mm]FAKULTETA ZA RAČUNALNIŠTVO IN INFORMATIKO}
  \\[5mm]
  \@program\@unless{\boolean{@enovitistudij}}{\ -- \@stopnja}
  }
  \vfill
  \begin{center}
  {\large
  \@avtor\\[2mm]
  {\Large\textbf{\MakeUppercase{\@naslov}}}\\[10mm]
  \@tipdela\\[1cm]
  \begin{tabular}{rl} \@mentorji \end{tabular}
  }
  \end{center}
  \vfill

  \noindent{\large
  Ljubljana, \@letnica}
  \cleardoublepage
}
\def\@frontpages@en@frontpage{
  \thispagestyle{empty}
  \noindent{\large
  UNIVERSITY OF LJUBLJANA\\[1mm]
  FACULTY OF MATHEMATICS AND PHYSICS
  \@ifthen{\boolean{@fri}}{\\[1mm]FACULTY OF COMPUTER AND INFORMATION SCIENCE}
  \\[5mm]
  \@programme\ -- \@cycle}
  \vfill

  \begin{center}{\large
  \@avtor\\[2mm]
  {\Large\textbf{\MakeUppercase{\@title}}}\\[10mm]
  \@thesistype\\[1cm]
  \begin{tabular}{rl} \@supervisors \end{tabular}
  }
  \end{center}
  \vfill

  \noindent{\large
  Ljubljana, \@letnica}
  \cleardoublepage
}
\newcommand{\dvastolpca}[3][0.45]{
  \hfill
  \parbox{#1\linewidth}{
    \center #2
  }
  \hfill
  \parbox{#1\linewidth}{
    \center #3
  }
  \hfill
}

\def\@frontpages@trst@en@frontpage{
  \thispagestyle{empty}
  \noindent
  \hfuzz=3pt % ker se spodnja minipagea prekrivata
  % minipage je potreben, ker dva parboxa ne pašeta lepo
  \begin{minipage}[6em]{0.5\linewidth}
    \small\center
    UNIVERSITY OF TRIESTE\\[1mm]
    DEPARTIMENT OF MATHEMATICS\\
    AND GEOLOGY
  \end{minipage}
  \begin{minipage}[6em]{0.5\linewidth}
    \small\center
    UNIVERZA V LJUBLJANI\\[1mm]
    FAKULTETA ZA MATEMATIKO\\
    IN FIZIKO
  \end{minipage}\\
  \begin{center}
    \@programme\ -- \@cycle
  \end{center}
  \vfill

  \begin{center}{\large
  \@avtor\\[2mm]
  {\Large\textbf{\MakeUppercase{\@title}}}\\[10mm]
  \@thesistype\\[1cm]
  \begin{tabular}{rl} \@supervisors \end{tabular}
  }
  \end{center}
  \vfill

  \begin{center}\large
    Ljubljana, \@letnica
  \end{center}
  \cleardoublepage
}
\def\@frontpages@trst@itslo@frontpage{
  \thispagestyle{empty}
  \noindent
  \hfuzz=3pt % ker se spodnja minipagea prekrivata
  % minipage je potreben, ker dva parboxa ne pašeta lepo
  \begin{minipage}[6em]{0.5\linewidth}
    \small\center
    UNIVERSITÀ DEGLI STUDI DI TRIESTE\\[1mm]
    DIPARTIMENTO DI MATEMATICA\\
    E GEOSCIENZE\\[1mm]
    Programma di doppio titolo\\
    in Matematica
  \end{minipage}
  \begin{minipage}[6em]{0.5\linewidth}
    \small\center\vspace*{2.5pt} % poravnava zaradi `À` v drugi univerzi
    UNIVERZA V LJUBLJANI\\[1mm]
    FAKULTETA ZA MATEMATIKO\\
    IN FIZIKO\\[1mm]
    Program dvojne diplome\\
    iz matematike
  \end{minipage}
  \vfill
  \begin{center}
  {\large
  \@avtor\\[2mm]
  \dvastolpca
    {\Large\textbf{\MakeUppercase{\@it@title}}}
    {\Large\textbf{\MakeUppercase{\@naslov}}}
  \\[10mm]
  \dvastolpca
    {\large\@it@thesistype}
    {\large\@tipdela}
  \\[1cm]
  \begin{tabular}{rl} \@it@supervisors \\ \@mentorji \end{tabular}
  }
  \end{center}
  \vfill

  \begin{center}\large
    Ljubljana, \@letnica
  \end{center}
  \cleardoublepage
}
\def\@frontpages@sl@zahvala{
  \ifdefined\@zahvala
    \pdfbookmark[1]{Zahvala}{zahvala}
    \section*{Zahvala}
    \@zahvala
    \vfill
    \cleardoublepage
  \fi
}
\def\@frontpages@en@acknowledgements{
  \ifdefined\@zahvala
    \pdfbookmark[1]{Acknowledgements}{zahvala}
    \section*{Acknowledgements}
    \@zahvala
    \vfill
    \cleardoublepage
  \fi
}
\def\@frontpages@sl@povzetek{
  \begin{center}
    \textbf{\@naslov}\\[3mm]
    \textsc{Povzetek}
  \end{center}
  \@povzetek
  \vfill
}
\def\@frontpages@en@abstract{
  \begin{center}
    \textbf{\@title}\\[3mm]
    \textsc{Abstract}
  \end{center}
  \@abstract
  \vfill
}
\def\@frontpages@trst@abstract{
  \begin{otherlanguage}{italian}
  \begin{center}
    \textbf{\@it@title}\\[3mm]
    \textsc{Sommario}
  \end{center}
  \@it@abstract
  \end{otherlanguage}
  \vfill
}
\def\@frontpages@sl@kljucnebesede{
  \noindent
  \textbf{Math. Subj. Class. (2020):} \@klasifikacija \\[1mm]
  \def\sep{, }% Pri izpisu ključne besede ločimo z vejico.
  \textbf{Ključne besede:} \@kljucnebesede \\[1mm]
  \textbf{Keywords:} \@keywords
}
\def\@frontpages@en@keywords{
  \noindent
  \textbf{Math. Subj. Class. (2020):} \@klasifikacija \\[1mm]
  \def\sep{, }% Pri izpisu ključne besede ločimo z vejico.
  \textbf{Keywords:} \@keywords \\[1mm]
  \textbf{Ključne besede:} \@kljucnebesede
}
\def\@frontpages@trst@keywords{
  \noindent
  \textbf{Math. Subj. Class. (2020):} \@klasifikacija \\[1mm]
  \def\sep{, }% Pri izpisu ključne besede ločimo z vejico.
  \textbf{Keywords:} \@keywords \\[1mm]
  \textbf{Parole chiave:} \@it@keywords \\[1mm]
  \textbf{Ključne besede:} \@kljucnebesede
}

\AfterEndPreamble{%
% začetne strani številčimo z rimskimi številkami
\pagenumbering{roman}
\@frontpages
% vsebino številčimo z arabskimi številkami od 1 naprej
\setcounter{page}{1}
\pagenumbering{arabic}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% IZPIS KONČNIH STRANI
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\@make@razsirjenipovzetek}[3]{
  % Args: jezik, naslov razš. povzetka (v jeziku), ime datoteke povzetka
  % V razširjenem povzetku želimo, da razdelki pripadajo nekemu
  % nad-razdelku "Razširjeni povzetek", zato vse razdelke premaknemo
  % en nivo nižje in nastavimo številčenje na podrazdelek.

  % shrani stare definicije razdelkov
  \let\oldthesection\thesection
  \let\oldthesubsection\thesubsection
  \let\oldsection\section
  \let\oldsubsection\subsection

  % nastavi številčenje po podrazdelkih
  \def\thesection{}
  \def\thesubsection{\@arabic\c@subsection}
  \numberwithin{equation}{subsection}

  % premakne nivoje razdelkov en nivo nižje, da nivo `\section' spada pod razdelek razširjenega povzetka
  \let\section\subsection
  \let\subsection\subsubsection

  \cleardoublepage
  \begin{otherlanguage}{#1}
    \phantomsection % potrebno za pravilno številčenje strani v kazalih
    \addcontentsline{toc}{section}{#2} % doda razdelek v kazalo in metapodatke
    \begin{center}
      \textsc{#2}
    \end{center}
    \input{#3}
  \end{otherlanguage}

  % obnovi stare definicije razdelkov
  \let\thesection\oldthesection
  \let\thesubsection\oldthesubsection
  \let\section\oldsection
  \let\subsection\oldsubsection
}


\AtEndDocument{%
\ifdefined\@slovar
\pdfbookmark[1]{Slovar strokovnih izrazov}{slovar}
\section*{Slovar strokovnih izrazov}
\@slovar
\fi
\ifdefined\@literatura
\cleardoublepage
\phantomsection
\@sloeng
  {\addcontentsline{toc}{section}{Literatura}}
  {\addcontentsline{toc}{section}{References}}
\printbibliography
\fi
\cleardoublepage
\printindex

\@ifthen{\boolean{@trst}}{
  \newtheorem{assioma}{Assioma}
  \newtheorem{definizione}{Definizione}[subsection]
  \newtheorem{osservazione}[definition]{Osservazione}
  \newtheorem{esempio*}[definition]{Esempio}
  \newenvironment{esempio}[1][]{
    \begin{esempio*}[#1]\renewcommand*{\qedsymbol}{$\diamondsuit$}\pushQED{\qed}
  }{
    \popQED\end{esempio*}
  }

  \@make@razsirjenipovzetek{italian}{Sintesi estesa}{\@it@razsirjenipovzetek}
}
\@ifthen{\boolean{@anglescina}}{
  % spremeni številčenje definicij, izrekov, ipd. na ustrezen nivo
  \let\definicija\undefined
  \let\c@definicija\undefined
  \theoremstyle{definition}
  \newtheorem{definicija}{Definicija}[subsection]

  \@make@razsirjenipovzetek{slovene}{Razsirjeni povzetek}{\@razsirjenipovzetek}
}
}

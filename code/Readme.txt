Note: This has been tested on Ubuntu 10.04 >= ; admin privileges on machine assumed. Mac users might find that portions of this might not work as expected/requires changes.

How to run this:
1. Install Ocaml. This should install ocaml 3.08 or >=
$ sudo apt-get install ocaml

2. Install CIL. Navigate your browser to http://sourceforge.net/projects/cil/ and download cil-1.5.1.tar.gz
Then,
a. Untar, configure, make and sudo make install
$ tar -xzf cil-1.5.1.tar.gz
$ cd cil-1.5.1; ./configure; make; sudo make install

CIL should now be installed.

3. Install CIL-template. This step assumes Mercurial client is install, otherwise
$ sudo apt-get install hg
$ hg clone https://bitbucket.org/zanderso/cil-template

Compile and install CIL-template as documented here: https://bitbucket.org/zanderso/cil-template/overview

CIL template should now be installed.

4. Apply "patch_this" patch in CIL-template's directory
$ cp patch_this <cil-template-dir>
$ cd cil-template
$ patch -p1 < patch_this

5. Copy linear_relations_analysis.ml to cil-template's src folder, renaming it tut16.ml in the destination directory:
$ cp linar_relations_analysis.ml <cil-template's src directory>/tut16.ml
Make clean, make and install again
$ make clean; sudo make install

6. Finally, run the example on a sample test program in test/
$ ciltutcc --enable-tut16 -o testprg <path to test/testprg.c>



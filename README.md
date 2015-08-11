# RSL Type Checker source code

Copyright (C) 1998 UNU/IIST

The RSL type checker is available free for both PC and Unix platforms.

See the LICENSE file for details of the license conditions.

See the README.orig for the original README file included in the distribution
and explanation about the content of folders.

This repository contains a copy of the source code of the RSL Type Checker
implemented in [Gentle](http://gentle.compilertools.net/). The implementation is
mainly located in the `src` folder.

## Dependencies
Make sure that you have the following programs installed and working on your
machine.

- [Gentle](http://gentle.compilertools.net/)
- [Cmake](http://www.cmake.org/)
- [Flex](http://flex.sourceforge.net/)
- [GNU Bison](http://www.gnu.org/software/bison/)
- gcc
- Automake

## Compilation & Installation
It is *strongly* recommended to compile the code on Unix/Linux.

- **Configure**: run `./configure` to configure the build folder using CMake.
  This creates folder `build` containing all necessary files for compilation. By
  default, the compiler tries to find Gentle's files in `/usr/share/gentle`
  folder. If you install Gentle in other location, you can tell `./configure` by
  running

  ```sh
  ./clean
  ./configure -DGENTLE=/path/to/your/gentle/installation
  ```

  If you want to clean up everything and re-configure

  ```sh
  ./clean
  ./configure
  ```

- **Compile**: 

  ```sh
  cd build
  make
  ```

- **Clean**: 

  ```sh
  cd build
  make clean
  ```

- **Install**:

  ```sh
  cd build
  sudo make install
  ```

- **Make Debian package**: 

  ```sh
  cd build
  cpack
  ```

- **Uninstall**:

  ```sh
  cd build
  sudo make uninstall
  ```


## Contribute
### Students: 
   Upon assigned a project, a branch will be created for your project.
   You have full access for the branch and implement all your work on that
   branch.

   *DO NOT commit changes to `master` branch, it is for stable code.*

### Others: 
   You are welcome to fork the code and make pull requests.

### Workflow
- Learn basic Git commands. E.g. try the following tutorials.
  
  [Git Documentation](http://git-scm.com/docs/gittutorial)

  [Atlassian's Git Tutorial](https://www.atlassian.com/git/tutorials/)

- *Remember to always make a `pull` before you `push` your changes.*

### FAQ

Some common questions and answers are listed in the following. For any further
questions, please contact the repository's owner.

- Where is the source code?
  
  The source code are the `.g` files in the `src` folder.
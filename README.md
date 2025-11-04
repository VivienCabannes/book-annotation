# Book Annotation

## Installation

#### Install Lean

You can install Lean with brew if on MacOs.

```sh
brew install elan-init
elan default stable
```

You may equally use curl.

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Check your installation.

```sh
lean --version
```

#### Set up a Lean project

Clone the repository and download Lean dependencies.

```sh
git clone git@github.com:VivienCabannes/book-annotation.git
cd book-annotation
lake exe cache get
```

Alternatively you can create a new project dependent on Mathlib, and download the required libraries.

```sh
lake new book-annotation math
cd book-annotation
lake exe cache get
```

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.

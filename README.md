# tfl-book

The [Zcash Trailing Finality Layer](https://daira.github.io/tfl-book/) design book.

This repository is the source text and rendering configuration for the book. To read the book, use the link above.

The `mdbook` tool renders the contents into a pretty format from `markdown` based source code

## GitHub CI

There are two GitHub CI workflows:

- `merge-acceptance.yaml`: triggers on `pull_request` to check that `mdbook build` succeeds and there aren’t dangling `md` files (e.g. you remove an entry in `SUMMARY.md` but forget to rm the file.)
- `render-site.yaml`: triggers on `push` to `main` to render the site to https://daira.github.io/tfl-book/
  - **Warning:** this workflow relies on full read/write access to the `gh-pages` branch. Don’t mess with that branch unless you're very confident in the impacts.

## `git-hooks`

There is a directory `git-hooks` that we advocate all contributors use.

Use this command to enable it:

```
git config --local core.hooksPath git-hooks
```

## Prerequisites

Note: Nix users can rely on `flake.nix` which packages the final rendered HTML into `<prefix>/share/doc/tfl-book`. Users can install this via `nix profile install 'github:Electric-Coin-Company/tfl-book'`, or to build the local version `nix build`.

### Rust prerequisites

- `cargo install mdbook`
- `cargo install mdbook-admonish`
- `cargo install mdbook-graphviz`
- `cargo install mdbook-katex`
- `cargo install mdbook-linkcheck`

### Other prerequisites

- `graphviz` - on debian-like: `sudo apt install graphviz`

## Rendering

- `mdbook build`

## Release Process

Releases are defined as distinct revisions that embody a consistent set of changes from the prior releases, identified by a version with `XXX.YYY.ZZZ` format. Releases serve a few purposes. They

- ensure that readers can better notice changes or updates between readings or in discussions with others;
- signify that the authors have converged after a period of editing onto a coherent integrated result;
- signify approximate maturity of the design, based on the version number; and
- serve as a natural milestone for announcements on design updates.

### Versioning Schema

The versioning scheme isn’t precise and roughly follows this rubrik:

When a version `X.Y.Z` increments, the scope of change since the prior release is implied by the new version:

- `<X+1>.0.0` - This release represents a complete, well analyzed design which the authors believe could be a suitable candidate for Zcash (or other crypto networks) to productionize by developing conforming implementations that activate in production.
- `X.<Y+1>.0` - This release introduces or changes substantial design decisions or analyses, or it changes the presentation (such as the order or content of chapters) significantly. A reader of only the prior release may be missing essential details in understanding this new release.
- `X.Y.<Z+1>` - This release improves the wording, layout, rendering, or other content in a manner that doesn’t rise to the threshold of the previous case.

### Release Process

To create a new release:

1. Decide that the `main` branch is in a coherent state without likely sources of confusion or self-inconsistency.
2. Decide the new release’s version as in [Versioning Schema](#versioning-schema) above.
3. Create a release branch named `release-<NEW VERSION>`.
4. Update the release branch with these changes:
  - `book.toml`: Modify the `title` to end with `vX.Y.Z`. This ensures the version is visible to readers on all pages.
  - `src/version-history.md`: Introduce a new heading `## X.Y.Z - <RELEASE TITLE>` above all prior entries (i.e. reverse chronologically).
    - The `RELEASE TITLE` should be a shorthand title capturing the primary change of the release.
    - The release body should always begin with a link titled `Issue Tracking` that navigates to the GitHub milestone page of completed issues in this release.
    - The rest of the release body should be a one- to three-sentence summary of changes. Readers who need more detail can follow issue tracking.
  - `src/introduction.md`: The first paragraph says `This is <VERSION LINK> of the book.` Update that link to point to the new release’s entry in `src/version-history.md`.
5. Submit those changes for GitHub pull-request review, resolve any blocking concerns, then merge to the `main` branch. Note: This step will render the release.
6. Create a git tag on the git commit that merges into `main`: `git tag vX.Y.Z && git push --tags`

Note: We don’t use GitHub "releases" since there’s no release artifact other than the already published rendering.

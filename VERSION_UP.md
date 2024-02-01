# Version Up

1. Update the crate version of each `Cargo.toml`.
1. Make sure the CHANGELOG.md is updated
1. Switch to release branch
1. Disable the `pre-commit` hook. (remove link `.git/hooks/pre-commit)
1. Change the dependency of `bsn1\_serde`.
1. Dry run `cargo publish`
    - `$ cargo publish --dry-run -p bsn1`
    - `$ cargo publish --dry-run -p bsn1\_serde`
    - `$ cargo publish --dry-run -p bsn1\_serde\_macros`
1. Create git tag
1. Push the local repository to github
1. Publish the updated crate
1. Swith to main branch

# Version Up

1. Make sure the followings
    - Entry `package.version` of each `Cargo.toml`
    - The version of each `CHANGELOG.md` file
    - The release date of each `CHANGELOG.md` file
    - All the tests are passed
1. Switch to release branch
1. Disable the `pre-commit` hook. (remove link `.git/hooks/pre-commit)
1. Change the dependency of each `Cargo.toml` file (The path the crates in the workspace should be fixed.)
1. Dry run `cargo publish`
    - `$ cargo publish --dry-run -p bsn1`
    - `$ cargo publish --dry-run -p bsn1\_serde`
    - `$ cargo publish --dry-run -p bsn1\_serde\_macros`
1. Create git tag
1. Push the tag to github
1. Publish the updated crate
1. Swith to main branch (Don't merge the release branch into main branch.)
1. Recover the `pre-commit` hook.

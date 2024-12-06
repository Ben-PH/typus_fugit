Work is done on dev branch. pulls into main are done for releases.

Core principal to remember is that this repo is intended to explore what an effort to migrate from const-generics to type-level values would look like, if te upstream `fugit` crate decided to make the change.

I would gladly take token-sponsorships (e.g. $1/month), but please consider sponsoring `fugit` first.

Please leave `#![clippy::pedantic]` active, but feel free to add extra `allows`.


I like to merge without squashing where possible. Please try to keep a clean, and coherent commit history. As a rough guide:

1. checkout and pull the target branch (typically `dev`)
2. checkout your contribution branch
3. `git checkout -b rebase_rehearse`
4. `git rebase -i <target_branch`
5. re-order, squash, rename, etc. your commits so they look nice
6. Make sure your contribution branch is already pushed so you can recover it if need be.
7. Once you're happy with what the rebase will look like, do the rebase on your contribution branch
8. When ready, `git push`, with a `--force` if need be

Please do your work on your own fork, and contribute through a PR from there. With that said, feel free to.

Use descriptive titles for your contribution branchs.

Avoid using `main`

In short, a typical flow is:

1. Fork
2. checkout to dev
3. branch off to a discriptive name
4. make your changes
5. correct clippy lints, or add allows
6. do your usual `fmt`, tests, etc.
7. clean up and consolodate commit log
8. Open PR onto the dev branch

## License Disclaimer

By contributing to this project, you agree that your contributions will be licensed under the terms of the MIT License or Apache License, Version 2.0, at your option.

You acknowledge that:

 - Any contributions you make will be governed by these dual licenses.
 - Your contributions must be original, or you must have sufficient rights to submit them under these terms.

 In addition, any contribution made is intended to be proactively made available to the upstream `fugit` project. 

If you have any questions or concerns, please reach out via an issue or discussion thread.

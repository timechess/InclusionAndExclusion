# Inclustion and Exclusion

This is a Lean4 project proving the **Principle of Inclusion and Exclusion** as the TBL group project in WestLake University, 2024.8.

You can visit https://timechess.github.io/InclusionAndExclusion/ to view the blueprint.

> Thank Wang Jingting of PKU for providing the proof of this theorem.


## PR Guide

If you are a leader, fork this repo by clicking the `fork` button on upper right of this page. Else fork your group leader's repo. This will create a copy of the repo in your account.

Let's assume the main repo is named `timechess/InclusionAndExclusion`, the forked repo is named `yourname/repo`.

First, clone your repo to your local by the command below:

```bash
git clone https://github.com/yourname/InclusionAndExclusion.git
```

The url can be copied from your repo's page by clicking the `Code` button.

Open terminal in the directory of the cloned repo. You can use vscode to open the folder and open terminal in vscode. Type `git remote` in the terminal and you will see `origin`. This is the alias of your remote repo, representing the url https://github.com/yourname/InclusionAndExclusion.git.

You can use `git pull origin master` to pull changes from your remote repo and use `git push origin master` to push changes from local to remote.

To open a pull request, first change the files in your local repo, and use `git add .` and `git commit -m "Your commit message"` to update your local repo. Now your local repo is ahead of your remote. Use `git push origin master` to sync.

Now open your repo on the GitHub. You can see `your branch is xx commits ahead of xx`. If you see `xx commits behind`, your repo is not sync with the parent repo. You need to sync with it before pull request.

In your local repo, use the command below to add the parent remote repo as a remote.
```bash
git remote add upstream https://github.com/timechess/InclusionAndExclusion.git
```

> Remember, if you are not a leader, change `timechess` to your leader's GitHub name.

This only needs to be done once. And now you can `git pull upstream master` to pull changes from your parent repo. This will sync your local repo with your parent remote repo. If there is a conflict, vscode will show the conflicts. You can see `Resolve in Merge Editor` in the conflict files. Click it and choose the changes to accept until no conflicts remain. Click `Complete Merge`. After all conflicts resolved, you can `git push origin master` to sync your remote repo with your local, in other words, sync with your parent repo. You will see your remote repo only `ahead of` the parent repo if everything is right(If not, maybe the parent repo updated again).

Now you can click `contribute` and `Open pull request`. Follow the guide of GitHub to open pull request. Ask your leader to review your pull request. After your PR being merged, you will see your remote repo have both commits ahead and behind. Now use the following command to clean up:
```bash
git pull upstream master --rebase
git push origin master --force
```

Now your local repo and remote repo are both up to date.

Repeat the whole process if you want to start another PR.
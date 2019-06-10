# BESSPIN Voting System - Revision Control Practices

This document defines the revision control practices to be used on the BESSPIN Voting System (BVS) Project.

## Git Development Workflow

The BESSPIN Voting System project uses Git for revision control. Currently, we are using Galois's externally-accessible GitLab server for hosting and code review. The development workflow is as follows:

1. Locally, pull the latest changes on the `master` branch of the
   upstream repository.
2. Check out a new topic branch based on the above changes.
3. Commit changes to your local branch.
4. For the sake of visibility, you may open a work-in-progress Pull
   Request from your branch to `master`. If you do, add the `wip`
   label.
5. When you are ready to merge to `master`, make sure your branch has
   been pushed to the upstream repository and open a Pull Request (if
   you haven't already). Remove any `wip` label and add the `ready for review`
   label.
6. Typically, at least one _other_ person must review any changes to the `master`
   branch and approve it via the GitHub PR interface comments. A
   _reviewer_ should check that all necessary comments are addressed.
7. Before it can be merged, you will generally have to `rebase` your
   branch on to the `master` branch in order to preserve a clean commit
   history. You can do this with commands in your branch: `git fetch`,
   then `git rebase origin/master` (addressing any merge conflicts if
   necessary), and finally
   `git push --force-with-lease origin <yourbranch>`.
8. Note that *force-pushes can be dangerous*, so make sure that you know
   that no one else has pushed changes to the branch that aren't in the
   history of your local branch.  If others on the team are pulling and
   testing it locally, they will need to fix up their local branches with
   `git checkout <yourbranch>`, `git fetch`, and
   `git reset --hard origin/<yourbranch>`.
   For more details, see
   [The Dark Side of the Force Push - Will Anderson](http://willi.am/blog/2014/08/12/the-dark-side-of-the-force-push/)
   and [--force considered harmful; understanding git's --force-with-lease - Atlassian Developers](https://developer.atlassian.com/blog/2015/04/force-with-lease/)
9. Once it has been rebased, a _reviewer_ with merge permissions can merge 
   the PR using the GitLab "Merge" button, _without_ selecting "Squash commits".
   This will introduce an _unsigned_ merge commit, but
   preserve the signatures, if any, on the actual branch's commits. 
10. Finally, the PR submitter, not the reviewer, should delete the merged
   branch from both their local repository and GitLab. If more work is to be done
   continuing from the branch, a new branch should be created.

**Guidelines:**

- Do not commit directly to `master`.
- To support bisecting, do not merge WIP commits that break the build.
  On topic branches, squash commits as needed before merging, but only 
  to reduce excessive small commits; the development history of topic branches
  should be preserved as much as is reasonable. Use your judgement.
- Write short, useful commit messages with a consistent style. Follow
  these
  [seven rules](https://chris.beams.io/posts/git-commit/#seven-rules),
  with the amendment that on this project, we have adopted the
  convention of ending the subject line with a period.
- Keep your topic branches small to facilitate review.
- Before merging someone else's PR, make sure other reviewers'
  comments are resolved, and that the PR author considers the PR ready
  to merge.
- For security-sensitive code, ensure your changes have received an
  in-depth review, preferably from multiple reviewers.
- (optional, but desirable!) Configure Git so that your commits are
  [signed](https://git-scm.com/book/en/v2/Git-Tools-Signing-Your-Work).
- Whenever possible, use automation to avoid committing errors or
  noise (e.g. extraneous whitespace). Use linters, automatic code
  formatters, test runners, and other static analysis tools. Configure
  your editor to use them, and when feasible, integrate them into the
  upstream continuous integration checks.




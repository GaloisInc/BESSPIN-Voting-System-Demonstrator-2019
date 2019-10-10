# BESSPIN Voting System - Revision Control Practices

This document defines the revision control practices to be used on the BESSPIN
Voting System (BVS) Project.

## Git Development Workflow

The BESSPIN Voting System project uses Git for revision control. Currently, we
are using Galois's externally-accessible GitLab server for hosting and code
review. The development workflow is as follows:

1. Locally, pull the latest changes on the `master` branch of the
   upstream repository.
2. Check out a new topic branch based on the above changes.
3. Commit changes to your local branch, and push upstream at reasonable
   intervals. If you are working with another developer on the same topic
   branch, use `git pull --rebase` to rebase your local branch against the
   remote topic branch (resolving any conflicts that arise) before pushing,
   which will keep history clean on the topic branch.
4. For the sake of visibility, you may open a work-in-progress Merge Request
   (MR) from your branch to `master`. Such a MR should include a brief
   characterization of work being carried out in the branch, be CC'd to
   individuals who should be aware of that work (even if they are not the
   assignees of the MR), and an explicit statement of the expected outcomes of
   the MR. Be sure to designate  _assignees_, a _milestone_, and appropriate
   _labels_ when opening the MR. If you open a MR while the work is in progress,
   prefix its name with _"WIP:"_ (this makes GitLab explicitly treat it as work
   in progress). The `wip` label is optional for MRs on GitLab; the work in
   progress status is based solely on the _"WIP:"_ prefix on the MR name.
5. When you are ready to merge to `master`, make sure your branch has been
   pushed to the upstream repository and open a MR (if you haven't already).
   Remove the "WIP:" prefix and add the `ready for review` label. Before it can
   be merged, you will generally have to `rebase` your branch on to the `master`
   branch in order to preserve a clean commit history. You can do this with
   commands in your branch: `git fetch`, then
   `git rebase --exec 'git commit --amend --no-edit -n -S' origin/master`
   (addressing any merge conflicts if necessary), and finally
   `git push --force-with-lease origin <yourbranch>`. **Do _NOT_ use the GitLab
   "Rebase" button (in the MR), because it will generate unsigned commits.**
6. Note that *force-pushes can be dangerous*, so make sure that you know that no
   one else has pushed changes to the branch that aren't in the history of your
   local branch.  If others on the team are pulling and testing it locally, they
   will need to fix up their local branches with `git checkout <yourbranch>`,
   `git fetch`, and `git reset --hard origin/<yourbranch>`. For more details,
   please see [The Dark Side of the Force Push] and
   [--force considered harmful; understanding git's --force-with-lease].
7. Typically, at least one _other_ person must review any changes to the
   `master` branch and approve it using the GitLab MR interface. A _reviewer_
   should check that all necessary comments are addressed.
8. Once it has been approved, a _reviewer_ with merge permissions should 
   sign the tip commit `git commit -S --amend --no-edit -n`, push (force with
   lease), and then merge the MR using the GitLab "Merge" button, with the
   "Delete source branch" checkbox _checked_ and the "Squash commits" checkbox
   _not checked_. This will introduce an _unsigned_ merge commit, but preserve
   the signatures, if any, on the actual branch's commits, and will delete the
   branch once it is merged.
9. If, for some reason, the "Delete source branch" checkbox was not checked,
   the reviewer that merges the branch should manually delete the branch
   after the merge.

[The Dark Side of the Force Push]: http://willi.am/blog/2014/08/12/the-dark-side-of-the-force-push/
[--force considered harmful; understanding git's --force-with-lease]: https://developer.atlassian.com/blog/2015/04/force-with-lease/

**Guidelines:**

- Do not commit directly to `master`.
- To support bisecting, do not merge WIP commits that break the build. On topic
  branches, squash commits as needed before merging, but only to reduce
  excessive small commits; the development history of topic branches should be
  preserved as much as is reasonable. Use your judgement.
- Write short, useful commit messages with a consistent style. Follow these
  [seven rules], with the amendment that on this project, we have adopted the
  convention of ending the subject line with a period.
- Keep your topic branches small to facilitate review.
- Before merging someone else's MR, make sure other reviewers' comments are
  resolved, and that the MR author considers the MR ready to merge.
- For security-sensitive code, ensure your changes have received an in-depth
  review, preferably from multiple reviewers.
- Configure Git so that your commits are [signed].
- Whenever possible, use automation to avoid committing errors or noise (e.g.
  extraneous whitespace). Use linters, automatic code formatters, test runners,
  and other static analysis tools. Configure your editor to use them, and when
  feasible, integrate them into the upstream continuous integration checks.

[seven rules]: https://chris.beams.io/posts/git-commit/#seven-rules
[signed]: https://git-scm.com/book/en/v2/Git-Tools-Signing-Your-Work

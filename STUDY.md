# Mathematics in Lean


## LLM

```bash
# create virtual env
python3 -v venv venv

# activate it
source venv/bin/activate

# install vLLM from pip:
pip install vllm

# Load and run the model:
vllm serve "EleutherAI/llemma_7b"

# Call the server using curl:
curl -X POST "http://localhost:8000/v1/chat/completions" \
	-H "Content-Type: application/json" \
	--data '{
		"model": "EleutherAI/llemma_7b"
		"messages": [
			{"role": "user", "content": "Hello!"}
		]
	}'

```



## Books

The training section has the material to be coded in the MIL folder
and is following the same order of sub-folders found in MIL

* [ai-tivar-danka](https://www.amazon.com/Mathematics-Machine-Learning-Calculus-Probability/dp/1837027870)
* [rare-skills-tutorial](https://www.rareskills.io/zk-book)
* [ai-by-hand](https://www.byhand.ai/)

### Training

* [algorithms](https://medium.com/techie-delight/500-data-structures-and-algorithms-practice-problems-35afe8a1e222)
* [theorem-proving](https://leanprover.github.io/theorem_proving_in_lean4/)
* [mechanics-of-proof](https://hrmacbeth.github.io/math2001/)
* [hitchhikers-guide](https://github.com/blanchette/logical_verification_2023/blob/main/hitchhikers_guide.pdf)
* [logic-and-proof](https://leanprover.github.io/logic_and_proof/introduction.html)
* [lean-manual](https://lean-lang.org/lean4/doc/)
* [lean-for-curious](https://lftcm2023.github.io/tutorial/index.html)
* [math-in-lean](https://leanprover-community.github.io/mathematics_in_lean)
* [logic-and-mechanized-reasoning](https://github.com/avigad/lamr)

### Theory

* [lean-intro](https://lftcm2023.github.io/tutorial/index.html)
* [main-website](https://leanprover.github.io)
* [mechanics-of-proof-repo](https://github.com/hrmacbeth/math2001)
* [functional-programming](https://lean-lang.org/functional_programming_in_lean/)
* [100-theorems](https://leanprover-community.github.io/100.html)
* [math-lib-docs](https://leanprover-community.github.io/mathlib4_docs/)
* [community-website](https://leanprover-community.github.io/)
* [teaching-logic](https://www.andrew.cmu.edu/user/avigad/Talks/fmtea.pdf)
* [lean4-logic-formalization](https://github.com/iehality/lean4-logic/tree/master)
* [project-euler](https://github.com/pcpthm/pe/blob/master/PE.lean)

## ZK

* [verified-zk-evm](https://github.com/Verified-zkEVM/ZKLib)
* [clean-circuit](https://github.com/Verified-zkEVM/clean)

## References
* [math-gloss-database](https://mathgloss.github.io/MathGloss/)
* [algorithm-database](https://www.techiedelight.com/)

## Games
* [lean-game-server](https://adam.math.hhu.de/#/)
* [lean-maze](https://github.com/dwrensha/lean4-maze)

## Tools and Articles
* [vscode-plugin](https://www.youtube.com/watch?v=zyXtbb_eYbY)
* [math-intro](https://leanprover-community.github.io/mathematics_in_lean/C01_Introduction.html)
* [tutorial](https://leanprover-community.github.io/learn.html)
* [glimpse](https://github.com/PatrickMassot/GlimpseOfLean)
* [natural-game](https://adam.math.hhu.de/#/g/hhu-adam/NNG4)
* [chat](https://leanprover.zulipchat.com/)
* [on-line-ide](https://lean.math.hhu.de/)

## Tatics


* [tatics](https://github.com/leanprover/theorem_proving_in_lean4/blob/master/tactics.md)
* [tatics-list](https://github.com/henry-hz/lean3-tactic-lean4)
* [tatics-learn4](https://github.com/madvorak/lean4-tactics)

## Videos

* [intro-video](https://www.youtube.com/watch?v=S-aGjgIDQZY)
* [install-lean-vscode](https://www.youtube.com/watch?v=yZo6k48L0VY)
* [simple-prove](https://www.youtube.com/watch?v=POHVMMG7pqE&list=PL88g1zsvCrjexLVWaHTnXs23kuwDUZIbL)
* [prime-prover-demo](https://www.youtube.com/watch?v=b59fpAJ8Mfs&list=PL88g1zsvCrjexLVWaHTnXs23kuwDUZIbL&index=2)
* [language-overview](https://www.youtube.com/watch?v=UeGvhfW1v9M)
* [seminar-intro](https://www.youtube.com/watch?v=S-aGjgIDQZY)
* [proof-intro](https://www.youtube.com/watch?v=Lji9_p6rkPc&list=PLLSwxwJoqOFFXB1bEL643JIgQMI11bkih)
* [empowering-math](https://www.youtube.com/watch?v=rDe0nIHINXs&t=1865s)


# Mathematics in Lean

This tutorial depends on Lean 4, VS Code, and Mathlib.
You can find the textbook both online and in this repository
in
[html format](https://leanprover-community.github.io/mathematics_in_lean/)
or as a
[pdf document](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf).
The book is designed to be read as you
work through examples and exercises,
using a copy of this repository on your computer.
Alternatively, you can use Github Codespaces or Gitpod to run Lean and VS Code in the cloud.

This version of *Mathematics in Lean* is designed for [Lean 4](https://leanprover.github.io/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).
For the Lean 3 version, see [https://github.com/leanprover-community/mathematics_in_lean3](https://github.com/leanprover-community/mathematics_in_lean3).


## To use this repository on your computer

Do the following:

1. Install Lean 4 and VS Code following
   these [instructions](https://leanprover-community.github.io/get_started.html).

2. Make sure you have [git](https://git-scm.com/) installed.

3. Follow these [instructions](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project)
   to fetch the `mathematics_in_lean` repository and open it up in VS Code.

4. Each section in the textbook has an associated Lean file with examples and exercises.
   You can find them in the folder `MIL`, organized by chapter.
   We strongly recommend making a copy of that folder and experimenting and doing the
   exercises in that copy.
   This leaves the originals intact, and it also makes it easier to update the repository as it changes (see below).
   You can call the copy `my_files` or whatever you want and use it to create
   your own Lean files as well.

At that point, you can open the textbook in a web browser
at [https://leanprover-community.github.io/mathematics_in_lean/](https://leanprover-community.github.io/mathematics_in_lean/)
and start reading and doing the exercises in VS Code.

The textbook and this repository are still a work in progress.
You can update the repository by typing `git pull`
followed by `lake exe cache get` inside the `mathematics_in_lean` folder.
(This assumes that you have not changed the contents of the `MIL` folder,
which is why we suggested making a copy.)


## To use this repository with Github Codespaces

If you have trouble installing Lean, you can use Lean directly in your browser using Github
Codespaces.
This requires a Github account. If you are signed in to Github, click here:

<a href='https://codespaces.new/leanprover-community/mathematics_in_lean' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

Make sure the Machine type is `4-core`, and then press `Create codespace`
(this might take a few minutes).
This creates a virtual machine in the cloud,
and installs Lean and Mathlib.

Opening any `.lean` file in the MIL folder will start Lean,
though this may also take a little while.
We suggest making a copy of the `MIL` directory, as described
in the instructions above for using MIL on your computer.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get` as above.

Codespaces offers a certain number of free hours per month. When you are done working,
press `Ctrl/Cmd+Shift+P` on your keyboard, start typing `stop current codespace`, and then
select `Codespaces: Stop Current Codespace` from the list of options.
If you forget, don't worry: the virtual machine will stop itself after a certain
amount of time of inactivity.

To restart a previous workspace, visit <https://github.com/codespaces>.


## To use this repository with Gitpod

Gitpod is an alternative to Github Codespaces, but is a little less convenient,
since it requires you to verify your phone number.
If you have a Gitpod account or are willing to sign up for one,
point your browser to
[https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean](https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean).
This creates a virtual machine in the cloud,
and installs Lean and Mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
We suggest making a copy of the `MIL` directory, as described
in the instructions above for using MIL on your computer.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get` as above.

Gitpod gives you 50 free hours every month.
When you are done working, choose `Stop workspace` from the menu on the left.
The workspace should also stop automatically
30 minutes after the last interaction or 3 minutes after closing the tab.

To restart a previous workspace, go to [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).
If you change the filter from Active to All, you will see all your recent workspaces.
You can pin a workspace to keep it on the list of active ones.


## Contributing

PRs and issues should be opened at the upstream
[source repository](https://github.com/avigad/mathematics_in_lean_source).

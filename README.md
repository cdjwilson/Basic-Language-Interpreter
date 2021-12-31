[![Open in Visual Studio Code](https://classroom.github.com/assets/open-in-vscode-f059dc9a6f8d3a56e377f745f24479a46679e63a5d9fe6f495e02850cd0d8118.svg)](https://classroom.github.com/online_ide?assignment_repo_id=6213942&assignment_repo_type=AssignmentRepo)
Everything in Main.hs was written by me except the actual main function.
It takes a file written in the Logic language defined for this project.
It parses that file and then evaluates it
To run the parser you do 
cabal run -- logic -p .\tests\tests1.l
To run the full interpreter you do
cabal run -- logic .\tests\tests1.l

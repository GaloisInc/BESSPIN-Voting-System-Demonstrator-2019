This is an example of how to overwrite a function call in the SBB code with a different function call. The trick here is that functions are called using the `jal` instruction which is a relative jump, so you must compute the relative offset of the function you want to jump to. This exploit walks through how to change the control flow after a ballot has been inserted to immediately cast the ballot.

This is a placeholder, more documentation and code to follow. 

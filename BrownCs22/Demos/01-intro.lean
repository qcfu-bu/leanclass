/-

Lean is a language that we will be using in CS22 this year.

If you're in this class, you've most likely used a programming language before.
Lean is a programming language too. But we'll be using it for a different reason:
Lean lets us state *propositions*, write *proofs* of these propositions, and *check*
automatically that these proofs are correct.

Some basic Lean syntax:

* Block comments, like this one, are written as /- ... -/.
* Line comments begin with -- 
* If a file imports other files, this appears at the very top of the file.
  You shouldn't change these imports!

**Definition**. A *proposition* is a statement with a truth value.
That is, it is a statement that could be either true or false.

"Lean is a language" is a proposition. "Lean is not a language" is a proposition.
"1 + 1 = 2" is a proposition, as is "1 + 1 = 3".
But "Lean" is not a proposition, nor is "1 + 1", nor is "is Lean a language?".

-/

#check Prop 

/-

Lean uses the shorthand `Prop` for proposition.
The `#check` command asks Lean to tell us "what kind of thing" something is.
(This will be very useful for us!)
Lean tells us that `Prop` is a Type, that is, a "kind of thing" -- not very enlightening!

But what if we try some of our examples from above?

-/

#check 1 + 1 = 2
#check 1 + 1 = 3

#check True 
#check False 
> # Murder Mystery Puzzle
> a logic murder mystery word problem solved in lean prover
> 
> Murder occurred one evening in the home of a father and mother and 
> their son and daughter. Each family member played a distict role. One member of the family murdered another member, 
> the third member witnessed the crime, and the fourth helped cover it up 
> so they were an accessory after the fact.
> 
> - Clue #1. The accessory and the witness were of opposite sex.
> - Clue #2. The oldest member and the witness were of opposite sex.
> - Clue #3. The youngest member and the victim were of opposite sex.
> - Clue #4. The accessory was older than the victim.
> - Clue #5. The father was the oldest member.
> - Clue #6. The murderer was not the youngest member.
> 
> Solve this Murder, and provide a clear argument that proves your allegations

## Solution

* Assumption #1. Since each family member played a distict role we know that: No two family members had the same role and no two roles were held by the same family member.

* Assumption #2. In addition, we can assume there are only two exclusive sexes: male or female (otherwise the term "opposite" used thoughtout the would not make sense).

* Assumtpion #3. Furthermore, mothers and daughters are female while fathers and sons are male (from the basic usages of the words in the english language).

* Assumtpion #4. From biology, we know that children are always yonger than their parents. 
  
From Clue #5 we know that the father was was the oldest and from Clue #2 he is therefore the opposite sex from the witnesses. Hence (by Assumption #2),

** Fact #1. The witness had to have been either the mother or the daughters (not that by Assumption #1, the witness cannot be both the mother and daughter)

Since by Clue #1 the accessory and witness were of the opposite sex, it follows that (by Assumption #2 and Fact #1),

** Fact #2. The accessory had to have been either the father or the son (but not both by Assumption #1).

---
  
By Assumtpion #4, we can conclude that the yongest had to have been either the son or the daughter. 

Suppose, for argument's sake that it was in fact the son who was the yongest. Then from Clue #3 (the yongest member and the victim were of opposite sex) we know that, the victim consequently must have been the mother or the daughter.
Assuming the victim was the mother, then (by Fact #1 and Assumption #1, since witness was not the mother) the witness had to have been the daughter. Therefore the murderer was either the father or the son (by Assumption #1). However, the murderer could in fact not be the son since we have assumed (for argument's sake), that the son was the yongest and we know from Clue #6 that the yongest was not the murderer. Thus, in this case, the father was the murderer and (by Assumption #1) the son must have have had the only remaining role  which was that of accessory. However this situation contradicts Clue #4; which states that the accessory (in this case, the son) was *older than* the murderer (in this case, the father).

If we assume instead that the victim was the daughter, then by a similar argument to above (Fact #1), the mother had to have been the witness. Similarly, the murderer was either the father or the son and could not be the son (by Clue #6 as above) so was in fact the father. This again would imply that the son was the accessory which due to Clue #4 is absurd.

We have shown that the above assumption (for arguments sake), that the son was the yongest, always results in contradiction. Therefore that assumption must not be valid. Since only the son or the daughter could have been the yongest (as children are yonger that their parents by Assumtpion #4), and we now know for sure that it was not the son, it must be the case that in fact: 

#### The daughter was the yongest.

Now, since we know the daughter was the yongest, by Clue #3 (the yongest member and the victim were of opposite sex), the victim consequently must have been either the father or the son. 
Assuming the victim was the Father, then (by Fact #2, since accessory was not the Father) the accessory had to have been the Son. However, this would mean that Clue #4 (accessory in this case, was the son, being older than the victim, who in this case was the father) violates biology! (see Assumtpion #3). This violation contradicts the assumption that the victim was the Father. Thus (by Fact #2):

### The Son was the Victim

Since the Son was the victim and therefore not the accessory (Fact #2 and Assumption #1):

### The accessory must have been the Father. 

Since we now know for sure what two of the roles (victim and accessory) for two of the family members (Father and Son) had to have been, it follows that the murderer was either one of the remaining family members i.e. the mother or the daughter. However, the murderer could in fact not be the daughter since we know that the daughter was the yongest and we know from Clue #6 that the yongest was not the murderer. Thus: 

### The Mother was the murderer.

Consequently: 

### The Daughter must have had the only remaining role which is that of Witness.




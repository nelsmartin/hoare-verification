/-

A register machine is sequence of instructions of the form

  CLR (r): CLeaR register r. (Set r to zero.)
  INC (r): INCrement the contents of register r.
  DEC (r): DECrement the contents of register r.
  CPY (rj, rk): CoPY the contents of register rj to register rk leaving the contents of rj intact.
  JZ (r, z): IF register r contains Zero THEN Jump to instruction z ELSE continue in sequence.
  JE (rj, rk, z): IF the contents of register rj Equals the contents of register rk THEN Jump to instruction z ELSE continue in sequence.

We also add

  SET (r,v) : SET the value of register r to v

--/

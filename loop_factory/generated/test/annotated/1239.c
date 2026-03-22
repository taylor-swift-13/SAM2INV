int main1(){
  int he, sa, t0, j3, kcv, hhq, i723;
  he=20;
  sa=1;
  t0=sa;
  j3=he;
  kcv=sa;
  hhq=(1%6)+2;
  i723=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 1 <= kcv;
  loop invariant t0 >= 1;
  loop invariant j3 >= 0;
  loop invariant i723 <= -5;
  loop invariant 0 <= kcv <= he;
  loop invariant 0 <= hhq <= 6;
  loop assigns kcv, t0, j3, hhq, i723;
*/
while (kcv<he) {
      kcv = kcv + 1;
      t0 = t0*hhq+1;
      j3 = j3*hhq;
      hhq = hhq*hhq+hhq;
      i723 = i723*4+(kcv%2)+1;
      hhq = hhq%7;
  }
}
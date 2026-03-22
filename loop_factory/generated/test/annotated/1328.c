int main1(int i){
  int zkpo, s9, pczp, wtq;
  zkpo=i+3;
  s9=0;
  pczp=1;
  wtq=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wtq == 1 + 2*s9;
  loop invariant i == \at(i, Pre) + 15*(s9/6) + ((s9%6) * ((s9%6) + 1))/2;
  loop invariant pczp == (s9 + 1) * (s9 + 1);
  loop invariant s9 >= 0;
  loop invariant zkpo == \at(i, Pre) + 3;
  loop assigns i, s9, wtq, pczp;
*/
while (pczp<=zkpo) {
      s9++;
      wtq += 2;
      i = i+(s9%6);
      pczp += wtq;
  }
}
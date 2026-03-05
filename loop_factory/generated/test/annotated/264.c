int main1(){
  int ex8, zy1, hpdh, r7;
  ex8=1+12;
  zy1=2;
  hpdh=2;
  r7=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hpdh == 5*zy1 - 8;
  loop invariant r7 == 5*zy1 - 3;
  loop invariant ex8 == 13;
  loop invariant 2 <= zy1 <= ex8;
  loop assigns hpdh, r7, zy1;
*/
while (zy1<ex8) {
      hpdh = hpdh + 5;
      r7 = r7 + 5;
      zy1++;
  }
}
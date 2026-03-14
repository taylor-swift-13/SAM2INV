int main1(){
  int n62, f, i, a4, r, bo6i, pr;
  n62=1;
  f=1;
  i=0;
  a4=0;
  r=0;
  bo6i=(1%18)+5;
  pr=n62;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a4 == i;
  loop invariant r == i;
  loop invariant bo6i + i == 6;
  loop invariant n62 == 1;
  loop invariant (pr >= 1);
  loop invariant ((i % 3) == 2) ==> (pr == i + 2);
  loop invariant ((i % 3) != 2) ==> (pr == i + 1);
  loop assigns i, a4, r, bo6i, pr;
*/
while (bo6i>=1) {
      i = i+1*1;
      a4 = a4+1*1;
      r = r+1*1;
      bo6i = bo6i - 1;
      pr = pr+(i%3);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a4 == r;
  loop invariant n62 == 1;
  loop invariant (0 <= f && f <= 1);
  loop assigns bo6i, a4, f, r;
*/
while (f>=1) {
      bo6i = bo6i+1*1;
      a4 = a4+1*1;
      f--;
      r = r+1*1;
      bo6i = bo6i*bo6i+bo6i;
  }
}
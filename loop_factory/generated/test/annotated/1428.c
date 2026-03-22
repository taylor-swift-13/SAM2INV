int main1(){
  int x, wk, h1;
  x=0;
  wk=66;
  h1=33;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x + wk == 66;
  loop invariant 0 <= h1 <= 33;
  loop invariant x + 3*h1 == 99;
  loop assigns x, h1, wk;
*/
while (1) {
      if (!(h1>0)) {
          break;
      }
      x = x + 3;
      h1--;
      wk = wk - 3;
  }
}
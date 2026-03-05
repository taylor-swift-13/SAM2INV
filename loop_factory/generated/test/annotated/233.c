int main1(int a){
  int s, z6;
  s=59;
  z6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a >= \at(a, Pre);
  loop invariant (a - \at(a, Pre)) % 2 == 0;
  loop invariant ((z6 == 0) || (z6 == 2) || (z6 == 4) || (z6 == 6)) && (z6 <= s) && (z6 >= 0);
  loop invariant s == 59;
  loop assigns a, z6;
*/
while (z6<s) {
      z6 = (z6+1)%6;
      z6 += 1;
      a += z6;
  }
}
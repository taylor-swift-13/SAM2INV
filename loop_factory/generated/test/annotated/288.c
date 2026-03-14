int main1(){
  int s1, d0, zyl;
  s1=35;
  d0=0;
  zyl=s1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zyl == s1 + 2*d0;
  loop invariant d0 >= 0;
  loop invariant zyl == 2*d0 + 35;
  loop assigns zyl, d0;
*/
for (; d0<=s1-1; d0 += 2) {
      zyl += 4;
  }
}
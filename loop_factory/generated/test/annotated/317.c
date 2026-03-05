int main1(){
  int w2, ub, jzk, k9e;
  w2=1-2;
  ub=w2;
  jzk=0;
  k9e=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ub - k9e == -2;
  loop invariant k9e >= 1;
  loop invariant jzk >= 0;
  loop invariant jzk <= k9e;
  loop invariant ub - k9e == w2 - 1;
  loop assigns jzk, k9e, ub;
*/
while (jzk>0&&k9e<=w2) {
      if (jzk>k9e) {
          jzk = jzk - k9e;
      }
      else {
          jzk = 0;
      }
      jzk += 1;
      k9e++;
      ub += 1;
  }
}
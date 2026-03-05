int main1(){
  int e, kc, i;
  e=(1%33)+6;
  kc=1;
  i=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 5*(kc - 1);
  loop invariant 1 <= kc;
  loop invariant kc <= e;
  loop invariant e == 7;
  loop assigns i, kc;
*/
while (kc<e) {
      if (kc%2==0) {
          if (i>0) {
              i--;
              i = i + 1;
          }
      }
      else {
          if (i>0) {
              i--;
              i = i + 1;
          }
      }
      kc += 1;
      i = i + 5;
  }
}
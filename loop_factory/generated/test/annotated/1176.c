int main1(){
  int eq, hh8, i, kl;
  eq=(1%60)+60;
  hh8=(1%9)+2;
  i=0;
  kl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= i;
  loop invariant 0 <= kl;
  loop invariant hh8 >= i + 3;
  loop invariant kl < hh8;
  loop assigns kl, i, hh8;
*/
while (1) {
      if (eq<=hh8*i+kl) {
          break;
      }
      if (kl==hh8-1) {
          kl = 0;
          i = i + 1;
      }
      else {
          kl += 1;
      }
      hh8 = (i)+(hh8);
  }
}
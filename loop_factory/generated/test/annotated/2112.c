int main1(){
  int xa, u, ms5, nel;
  xa=xa;
  u=0;
  ms5=xa;
  nel=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u >= 0;
  loop invariant 8 * ms5 == xa * nel;
  loop invariant nel >= 8;
  loop invariant nel > 0;
  loop invariant (ms5 * 8) == (xa * nel);
  loop invariant nel % 8 == 0;
  loop assigns ms5, u, nel;
*/
while (u > 0) {
      ms5 = ms5 + ms5;
      u--;
      nel = nel + nel;
  }
}
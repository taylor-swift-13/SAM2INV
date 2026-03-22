int main1(){
  int v, xgw, ls, jf5, kpc;
  v=48;
  xgw=v;
  ls=1;
  jf5=0;
  kpc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kpc == (ls*(ls+1))/2 - 1;
  loop invariant jf5 == ((ls-1)*ls*(2*ls - 1))/6;
  loop invariant 1 <= ls;
  loop invariant ls <= v + 1;
  loop invariant v == 48;
  loop assigns kpc, ls, jf5;
*/
while (ls<=v) {
      jf5 = jf5+ls*ls;
      ls++;
      kpc = kpc + ls;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ls >= 1;
  loop invariant kpc >= 0;
  loop invariant v == 48;
  loop assigns kpc, ls;
*/
while (ls<v) {
      kpc = v-ls;
      ls = ls + 3;
      if ((xgw%4)==0) {
          kpc += xgw;
      }
  }
}
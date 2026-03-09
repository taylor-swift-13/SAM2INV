int main1(){
  int gw, kuar, kl8b, ss;
  gw=74;
  kuar=0;
  kl8b=0;
  ss=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kuar == (kl8b % 3);
  loop invariant ss >= 10 + 3*kl8b;
  loop invariant ss <= 10 + 5*kl8b;
  loop invariant 0 <= kl8b <= gw;
  loop assigns kuar, kl8b, ss;
*/
while (1) {
      if (!(kl8b<=gw-1)) {
          break;
      }
      kuar = (kuar+1)%3;
      kl8b = kl8b + 1;
      ss = ss + kuar;
      ss = ss + 3;
  }
}
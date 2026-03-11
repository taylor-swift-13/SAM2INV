int main1(int v){
  int ip, dje, qzk, gf, am1;
  ip=(v%23)+6;
  dje=0;
  qzk=0;
  gf=0;
  am1=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gf == qzk*(qzk-1)/2;
  loop invariant ip == (\at(v, Pre) % 23) + 6;
  loop invariant am1 >= 0;
  loop invariant 0 <= qzk;
  loop assigns gf, am1, qzk;
*/
while (qzk<ip) {
      gf += qzk;
      am1 = am1 + gf;
      qzk = qzk + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ip >= ((\at(v, Pre)) % 23) + 6;
  loop invariant dje == 0;
  loop invariant gf >= 0;
  loop assigns am1, gf, ip;
*/
while (gf<dje) {
      am1 = dje-gf;
      gf += 8;
      ip = ip + gf;
  }
/*@
  assert !(gf<dje) &&
         (gf == qzk*(qzk-1)/2);
*/

}
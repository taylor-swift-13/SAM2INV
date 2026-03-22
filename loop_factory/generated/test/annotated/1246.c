int main1(int h){
  int u, jxd, nu4, rgh, p4, q;
  u=(h%18)+7;
  jxd=u;
  nu4=2;
  rgh=u;
  p4=-2;
  q=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jxd == rgh;
  loop invariant jxd >= ((\at(h, Pre) % 18) + 7);
  loop invariant q >= 1;
  loop invariant nu4 >= 2;
  loop invariant p4 <= -2;
  loop invariant p4 % 2 == 0;
  loop invariant jxd >= u;
  loop assigns rgh, nu4, q, p4, jxd;
*/
while (jxd-1>=0) {
      rgh = rgh + 1;
      nu4 = nu4+rgh*rgh*rgh*rgh;
      q = q+(nu4%5);
      p4 = p4*2;
      jxd += 1;
  }
}
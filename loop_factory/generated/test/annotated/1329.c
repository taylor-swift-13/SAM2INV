int main1(int k){
  int le, hqy, dyf, ex, u, re;
  le=(k%11)+20;
  hqy=le+6;
  dyf=0;
  ex=1;
  u=1;
  re=hqy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ex == (dyf + 1) * (dyf + 1);
  loop invariant 0 <= dyf;
  loop invariant u == 2*dyf + 1;
  loop invariant le == ((\at(k, Pre) % 11) + 20);
  loop invariant re == le + 6 + dyf * le;
  loop assigns ex, dyf, re, u;
*/
while (1) {
      if (!(ex<=le)) {
          break;
      }
      u += 2;
      dyf += 1;
      re = re + le;
      ex = ex + u;
  }
}
int main1(){
  int l4, m8, t0, xra, t, uqy;
  l4=1;
  m8=1;
  t0=1;
  xra=3;
  t=0;
  uqy=m8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xra == 3 + (t0 - 1) * (t0 - 1);
  loop invariant t0 >= 1;
  loop invariant l4 >= 1;
  loop invariant t0 <= l4 + 1;
  loop invariant t == l4 * (t0 - 1);
  loop assigns xra, t, t0;
*/
while (t0<=l4) {
      xra = xra+2*t0-1;
      t += l4;
      t0 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (uqy - 1) % 4 == 0;
  loop invariant l4 == 1 - 2 * (((uqy - 1) / 4) * (((uqy - 1) / 4) - 1));
  loop invariant l4 >= 1;
  loop invariant uqy <= m8;
  loop invariant m8 == 1;
  loop invariant (uqy == 1) || (xra == m8 - (uqy - 4));
  loop assigns l4, uqy, xra;
*/
while (uqy<m8) {
      xra = m8-uqy;
      uqy += 4;
      l4 = l4 + xra;
  }
}
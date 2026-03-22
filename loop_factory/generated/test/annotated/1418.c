int main1(int k){
  int eh, nyh, cnu, m;
  eh=17;
  nyh=0;
  cnu=nyh;
  m=k;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nyh <= eh;
  loop invariant nyh >= 0;
  loop invariant cnu == nyh * \at(k, Pre) + nyh * (nyh - 1) / 2;
  loop invariant m == \at(k, Pre) + nyh;
  loop invariant cnu == nyh * k + nyh * (nyh - 1) / 2;
  loop invariant m == k + nyh;
  loop invariant eh == 17;
  loop assigns nyh, cnu, m;
*/
while (nyh < eh) {
      nyh += 1;
      cnu = cnu + m;
      m++;
  }
}
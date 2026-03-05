int main1(int v,int c){
  int jd, s8, k;
  jd=45;
  s8=jd;
  k=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k >= -3;
  loop invariant s8 == 45;
  loop invariant jd == 45;
  loop invariant c == \at(c, Pre);
  loop invariant v == \at(v, Pre);
  loop invariant (k + 8) % 5 == 0;
  loop invariant k == -3 || k % 2 == 0;
  loop assigns k;
*/
while (s8-4>=0) {
      k += 4;
      k = k + k;
  }
}
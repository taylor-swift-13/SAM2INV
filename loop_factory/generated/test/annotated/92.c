int main1(int t){
  int vd3, gdmq, m1c, wj;
  vd3=8;
  gdmq=0;
  m1c=0;
  wj=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == \at(t, Pre) + m1c * vd3;
  loop invariant gdmq == 0;
  loop invariant vd3 == 8;
  loop invariant m1c >= 0;
  loop invariant m1c == 0 ==> wj == vd3;
  loop invariant m1c > 0 ==> wj + m1c == vd3 + 1;
  loop assigns wj, m1c, t;
*/
while (gdmq<vd3) {
      wj = vd3-m1c;
      m1c += 1;
      t = t + vd3;
  }
}
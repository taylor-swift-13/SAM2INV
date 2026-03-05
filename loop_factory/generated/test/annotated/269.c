int main1(int q){
  int w35a, hq4, z1ft;
  w35a=q-6;
  hq4=w35a;
  z1ft=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z1ft == 3 + 2*(hq4 - w35a);
  loop invariant hq4 <= w35a;
  loop invariant q == \at(q, Pre);
  loop invariant z1ft - 2*hq4 == 15 - 2*\at(q, Pre);
  loop invariant hq4 - w35a >= 0;
  loop invariant w35a == q - 6;
  loop assigns z1ft, hq4;
*/
while (hq4<w35a) {
      z1ft += 2;
      hq4 += 1;
  }
}
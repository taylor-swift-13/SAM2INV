int main1(int i,int e){
  int ofi, t8i3, g5v, a68r, k7;
  ofi=(i%7)+16;
  t8i3=0;
  g5v=0;
  a68r=1;
  k7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a68r == 1 + g5v;
  loop invariant t8i3 <= ofi;
  loop invariant a68r == 1 + g5v*(g5v+1)/2;
  loop invariant t8i3 == 0 || t8i3 == ofi;
  loop invariant g5v >= 0;
  loop invariant i == \at(i, Pre);
  loop invariant e == \at(e, Pre);
  loop invariant 0 <= t8i3;
  loop invariant (t8i3 == 0) ==> (g5v == 0 && a68r == 1);
  loop assigns g5v, a68r, t8i3;
*/
while (t8i3<=ofi-1) {
      g5v++;
      a68r += g5v;
      t8i3 = ofi;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ofi == (\at(i, Pre) % 7) + 16;
  loop invariant e == \at(e, Pre);
  loop invariant t8i3 >= 0;
  loop invariant k7 == 0;
  loop invariant i == \at(i, Pre);
  loop invariant t8i3 == ofi;
  loop assigns k7, i, t8i3;
*/
while (t8i3<g5v) {
      k7 = g5v-t8i3;
      i += k7;
      t8i3++;
  }
}
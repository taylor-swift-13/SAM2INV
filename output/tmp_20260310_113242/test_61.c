int main1(int s,int g){
  int do6, t4, l, s7r4;
  do6=g;
  t4=0;
  l=0;
  s7r4=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t4 >= 0;
  loop invariant s7r4 >= 0;
  loop invariant l == t4*(15 - t4)/2;
  loop invariant s7r4 == 7 - t4;
  loop invariant do6 == g;
  loop invariant s == \at(s, Pre) + t4*(t4+1)*(22 - t4)/6;
  loop assigns l, t4, s, s7r4;
*/
while (t4<do6&&s7r4>0) {
      l += s7r4;
      t4 = t4 + 1;
      s += l;
      s7r4--;
  }
}
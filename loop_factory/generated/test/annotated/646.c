int main1(int m,int l){
  int yc, x8, w, pc, lh51;
  yc=72;
  x8=0;
  w=0;
  pc=25;
  lh51=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w % 4 == 0;
  loop invariant w <= yc;
  loop invariant lh51 == 4 + (w/4) * x8;
  loop invariant 0 <= w;
  loop assigns pc, w, lh51;
*/
while (w<yc) {
      pc = (yc)+(-(w));
      w += 4;
      lh51 += x8;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == \at(l, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant yc == 72;
  loop assigns w;
*/
for (; w<=pc-1; w += 1) {
  }
}
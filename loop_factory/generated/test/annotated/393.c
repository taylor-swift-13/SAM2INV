int main1(int p,int b){
  int g, x1, g1, w, no;
  g=b+19;
  x1=0;
  g1=3;
  w=0;
  no=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant no == x1;
  loop invariant g1 == 3 + (x1 / 8);
  loop invariant g == b + 19;
  loop invariant x1 == 8*(g1 - 3) + w;
  loop invariant 0 <= w < 8;
  loop invariant g == \at(b, Pre) + 19;
  loop invariant 0 <= x1;
  loop assigns no, w, g1, x1;
*/
while (x1<=g-1) {
      no += 1;
      w += 1;
      if (w>=8) {
          w -= 8;
          g1 += 1;
      }
      x1++;
  }
}
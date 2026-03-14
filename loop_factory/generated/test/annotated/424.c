int main1(int i,int m){
  int dr9, l8, g2kh;
  dr9=m;
  l8=0;
  g2kh=dr9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g2kh == dr9 + l8;
  loop invariant dr9 == m;
  loop invariant l8 >= 0;
  loop invariant l8 == (\at(i,Pre) - i);
  loop invariant dr9 == \at(m,Pre);
  loop assigns i, g2kh, l8;
*/
while (1) {
      i--;
      g2kh++;
      l8 += 1;
      if (l8>=dr9) {
          break;
      }
  }
}
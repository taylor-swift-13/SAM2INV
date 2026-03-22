int main1(int m){
  int zh, dy8, j1y, xix, o1tg;
  zh=0;
  dy8=zh;
  j1y=-6;
  xix=m;
  o1tg=(m%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xix - j1y == \at(m,Pre) + 6;
  loop invariant zh == 0;
  loop invariant xix >= \at(m, Pre);
  loop invariant o1tg <= ((\at(m, Pre) % 35) + 8);
  loop invariant dy8 >= 0;
  loop assigns xix, dy8, j1y, m, o1tg;
*/
while (1) {
      if (!(o1tg>0)) {
          break;
      }
      xix = (o1tg*o1tg)+(xix);
      dy8 = dy8+j1y*j1y;
      j1y = j1y+o1tg*o1tg;
      m = m + xix;
      o1tg -= 1;
  }
}
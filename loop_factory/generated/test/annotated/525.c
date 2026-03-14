int main1(int x,int y){
  int m7j, ifu, v, okz;
  m7j=x*4;
  ifu=m7j;
  v=10;
  okz=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x - y == \at(x, Pre) - \at(y, Pre);
  loop invariant v >= 10;
  loop invariant okz >= 6;
  loop invariant m7j == 4 * \at(x, Pre);
  loop invariant (ifu == m7j) || (ifu == 0);
  loop invariant x == \at(x, Pre);
  loop invariant ifu <= m7j;
  loop assigns v, okz, x, y, ifu;
*/
while (1) {
      if (!(ifu>0)) {
          break;
      }
      v += 6;
      okz += v;
      x = x+m7j-ifu;
      y = (y+m7j)+(-(ifu));
      ifu = 0;
  }
}
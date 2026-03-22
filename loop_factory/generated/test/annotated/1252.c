int main1(int y){
  int qyp4, i4, c1cf, y6z, gs4, vn;
  qyp4=y+6;
  i4=qyp4+3;
  c1cf=i4;
  y6z=y;
  gs4=0;
  vn=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qyp4 == y + 6;
  loop invariant 0 <= (y6z - y);
  loop invariant y6z >= \at(y, Pre);
  loop invariant qyp4 == \at(y, Pre) + 6;
  loop invariant (i4 - qyp4 == 0) || (i4 - qyp4 == 3);
  loop assigns y6z, c1cf, gs4, i4, vn;
*/
while (1) {
      if (!(i4>qyp4)) {
          break;
      }
      y6z = y6z + 1;
      c1cf = c1cf+y6z*y6z*y6z;
      gs4 = gs4*3+(y6z%5)+0;
      i4 = qyp4;
      if (y+1<qyp4) {
          vn = vn*vn+gs4;
      }
      if ((i4%2)==0) {
          vn = vn%5;
      }
  }
}
int main1(int y){
  int qyp4, i4, c1cf, y6z, gs4, vn;

  qyp4=y+6;
  i4=qyp4+3;
  c1cf=i4;
  y6z=y;
  gs4=0;
  vn=y;

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

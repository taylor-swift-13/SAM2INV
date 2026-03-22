int main1(int q){
  int ger6, z, vb, x1, ulx, el7, d2, lt;

  ger6=110;
  z=ger6;
  vb=(q%20)+10;
  x1=(q%15)+8;
  ulx=z;
  el7=z;
  d2=q+5;
  lt=0;

  while (vb>0&&x1>0) {
      if (!(!(z%2==0))) {
          vb--;
      }
      else {
          x1 -= 1;
      }
      z += 1;
      if ((z%8)==0) {
          lt = lt + q;
      }
      d2 += 2;
      ulx = ulx + 1;
      q += vb;
      el7 = el7 + x1;
      ulx = ulx + 3;
  }

}

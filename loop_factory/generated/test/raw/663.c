int main1(){
  int f6, xre, sn, x5, i;

  f6=110;
  xre=f6;
  sn=4;
  x5=0;
  i=6;

  while (xre-5>=0) {
      i = i + xre;
      x5 = x5+sn*xre;
      sn = sn + i;
      xre += 1;
  }

  while (xre+5<=sn) {
      f6 = f6 + x5;
      x5 = x5*2;
      i = i+(f6%8);
      sn = (xre+5)-1;
  }

}

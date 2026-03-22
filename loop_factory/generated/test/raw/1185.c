int main1(){
  int ypg, gv, zq2, uu5, aw, wt;

  ypg=1-7;
  gv=(1%28)+8;
  zq2=(1%22)+5;
  uu5=0;
  aw=0;
  wt=ypg;

  while (zq2!=0) {
      if (zq2%2==1) {
          uu5 = uu5 + gv;
          zq2--;
      }
      zq2 = zq2/2;
      wt = wt*3+(uu5%3)+3;
      gv = 2*gv;
      aw = aw*4+(uu5%4)+0;
  }

}

int main1(){
  int r0r, ksz, gyxp, me, xqv;

  r0r=1+15;
  ksz=0;
  gyxp=23;
  me=1;
  xqv=0;

  while (1) {
      if (!(gyxp>0&&me<=r0r)) {
          break;
      }
      if (gyxp>me) {
          gyxp -= me;
      }
      else {
          gyxp = 0;
      }
      xqv = xqv + 1;
      ksz += 1;
      me = me + 1;
  }

}

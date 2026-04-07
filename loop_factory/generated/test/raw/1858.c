int main1(){
  int r, i, t1s, du, ax, dc6, nx5, od, bkez, mq;

  r=(1%38)+12;
  i=0;
  t1s=r;
  du=i;
  ax=r;
  dc6=r;
  nx5=i;
  od=1+4;
  bkez=-1;
  mq=r;

  while (1) {
      if (i%3==0) {
          t1s++;
      }
      else {
          du++;
      }
      if (i%3==1) {
          ax++;
      }
      else {
      }
      od = od + ax;
      bkez = bkez + du;
      nx5 = (od)+(nx5);
      mq = mq + i;
      od = od + dc6;
      if (bkez+7<r) {
          nx5++;
      }
      i = i + 1;
      if (i>=r) {
          break;
      }
  }

}

int main1(int t,int w){
  int uw, t6, olp, n30k, xe, cq, td, djzd;

  uw=w-9;
  t6=uw;
  olp=0;
  n30k=0;
  xe=uw;
  cq=0;
  td=10;
  djzd=uw;

  while (olp<uw) {
      olp += 2;
      if (cq<=xe) {
          xe = cq;
      }
      if ((t6%4)==0) {
          w += t6;
      }
      td = td + xe;
      t = t + 3;
      n30k = n30k + xe;
      cq = cq+olp-xe;
      djzd = djzd+xe-xe;
      n30k++;
      cq = cq - 1;
  }

}

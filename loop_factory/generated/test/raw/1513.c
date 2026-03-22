int main1(int j,int q){
  int a37, qfw, zk8, m, fm9, n4c, clls, p, bq;

  a37=(j%30)+17;
  qfw=0;
  zk8=0;
  m=0;
  fm9=0;
  n4c=0;
  clls=0;
  p=0;
  bq=q;

  while (1) {
      if (!(qfw<a37+(j%7))) {
          break;
      }
      if (!(!(qfw%7==0))) {
          if (qfw%4==0) {
              m++;
              clls += 2;
          }
          else {
              if (qfw%2==0) {
                  fm9++;
                  clls = clls + 3;
              }
              else {
                  if (1) {
                      n4c = n4c + 1;
                      clls += 4;
                  }
              }
          }
      }
      else {
          zk8 = zk8 + 1;
          clls++;
      }
      qfw++;
      bq = bq + n4c;
      p = p+qfw%4;
      bq++;
  }

}

int main1(int d,int p){
  int x, ej, qznn, o, dawt, gi;

  x=d+23;
  ej=x;
  qznn=43;
  o=0;
  dawt=1;
  gi=0;

  while (1) {
      if (!(qznn>0&&ej<x)) {
          break;
      }
      if (qznn<=dawt) {
          gi = qznn;
      }
      else {
          gi = dawt;
      }
      o += gi;
      qznn -= gi;
      ej = ej + 1;
      dawt = dawt + 1;
  }

}

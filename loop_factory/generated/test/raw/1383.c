int main1(int s,int m){
  int bqqn, mf, i, rrwy, kj, l1;

  bqqn=(s%35)+15;
  mf=(s%35)+15;
  i=1;
  rrwy=0;
  kj=0;
  l1=1;

  while (1) {
      if (!(bqqn!=mf)) {
          break;
      }
      if (bqqn>mf) {
          bqqn = bqqn - mf;
          i -= rrwy;
          kj = kj - l1;
      }
      else {
          mf -= bqqn;
          rrwy = rrwy - i;
          l1 = l1 - kj;
      }
      m = m+(rrwy%5);
  }

}

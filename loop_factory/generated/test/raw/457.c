int main1(int a,int s){
  int qe, x, gu1, ps31, ck, g;

  qe=a*4;
  x=0;
  gu1=0;
  ps31=0;
  ck=0;
  g=s;

  while (1) {
      if (!(ps31<=qe-1)) {
          break;
      }
      gu1 = gu1 + a;
      ps31 = ps31 + 1;
      a += x;
      ck += x;
  }

  while (g<ck) {
      g++;
      gu1 = gu1+ck-qe;
      ps31 = ps31 + a;
      x += qe;
  }

}

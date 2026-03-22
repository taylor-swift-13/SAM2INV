int main1(int u,int d){
  int am, mh, cj;

  am=18;
  mh=0;
  cj=3;

  while (1) {
      if (!(mh<am)) {
          break;
      }
      cj = cj+u+d;
      cj++;
      u = u + mh;
      mh = mh + 1;
  }

}

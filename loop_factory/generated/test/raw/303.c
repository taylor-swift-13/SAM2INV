int main1(int m){
  int u, fl, msi;

  u=m;
  fl=u;
  msi=0;

  while (fl<u) {
      if (fl%2==0) {
          if (msi>0) {
              msi = msi - 1;
              msi += 1;
          }
      }
      else {
          if (msi>0) {
              msi = msi - 1;
              msi += 1;
          }
      }
      fl = fl + 1;
      m = m + msi;
  }

}

int main1(int u){
  int iod, l5, zf, l0, r8ph, gt, l;

  iod=79;
  l5=0;
  zf=0;
  l0=0;
  r8ph=0;
  gt=0;
  l=iod;

  while (l5<iod) {
      if (!(!(l5%9==0))) {
          if (l5%6==0) {
              r8ph += 1;
          }
          else {
              if (l5%3==0) {
                  l0 = l0 + 1;
              }
              else {
                  zf += 1;
              }
          }
      }
      else {
          gt = gt + 1;
      }
      l5 += 1;
      l = l + gt;
  }

}

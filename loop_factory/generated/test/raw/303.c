int main1(int n){
  int iy, ni, szlo, fv, je;

  iy=n;
  ni=4;
  szlo=3;
  fv=0;
  je=n;

  while (szlo<=iy) {
      fv = fv+szlo*szlo;
      szlo = szlo + 1;
      je = je + ni;
  }

  while (1) {
      if (!(szlo<je)) {
          break;
      }
      szlo = szlo + 1;
      ni = je-szlo;
      n = n + ni;
  }

}

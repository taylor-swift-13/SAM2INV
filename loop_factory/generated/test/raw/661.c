int main1(int i){
  int lj, zo, k, yr;

  lj=i+13;
  zo=0;
  k=lj;
  yr=0;

  while (1) {
      if (!(zo<lj)) {
          break;
      }
      yr = yr + k;
      zo = lj;
  }

  while (lj<=yr-1) {
      zo = zo + k;
      lj = yr;
  }

}

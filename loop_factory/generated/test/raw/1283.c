int main1(int q){
  int ffjf, ng, qj, gz67, xul, d8ne;

  ffjf=q-2;
  ng=0;
  qj=0;
  gz67=0;
  xul=0;
  d8ne=7;

  while (ng<ffjf) {
      gz67 = ng%5;
      if (ng>=d8ne) {
          xul = (ng-d8ne)%5;
          qj = qj+gz67-xul;
      }
      else {
          qj += gz67;
      }
      ng = ng + 1;
      d8ne = d8ne + qj;
  }

}

int main1(int c,int j){
  int y9m, bcgz, d, ta4;

  y9m=j+19;
  bcgz=y9m;
  d=0;
  ta4=0;

  while (1) {
      if (!(ta4<y9m)) {
          break;
      }
      ta4++;
      d = d + c;
      c = c + ta4;
  }

  while (1) {
      if (!(bcgz<y9m)) {
          break;
      }
      bcgz += 1;
      d = d + c;
      j += bcgz;
  }

}

int main1(int c){
  int kg, fv, u, e;

  kg=25;
  fv=0;
  u=-1;
  e=fv;

  while (fv<=kg-1) {
      if (fv<kg/2) {
          u = u + e;
      }
      else {
          u = u + 1;
      }
      e += kg;
      e += 4;
  }

}

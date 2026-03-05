int main1(){
  int j7x, uad, vb, zp;

  j7x=1+9;
  uad=j7x;
  vb=7;
  zp=0;

  while (uad<j7x) {
      zp = uad%5;
      if (uad>=vb) {
          vb = (uad-vb)%5;
          vb = vb+zp-vb;
      }
      else {
          vb += zp;
      }
      vb = vb + 1;
      uad += 1;
  }

}

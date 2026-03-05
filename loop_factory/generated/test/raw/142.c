int main1(int x){
  int dn, lj, kwp, wy;

  dn=x+19;
  lj=0;
  kwp=0;
  wy=11;

  while (lj<dn) {
      if (kwp==0) {
          kwp += 1;
          wy--;
          kwp = 1;
      }
      else {
          kwp = kwp - 1;
          wy = wy + 1;
          kwp = 0;
      }
      lj++;
      x += dn;
  }

}

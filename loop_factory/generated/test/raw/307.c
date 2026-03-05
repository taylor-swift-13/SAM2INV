int main1(int u,int s){
  int r, etp7, fks;

  r=42;
  etp7=0;
  fks=0;

  while (etp7<r) {
      if (fks==0) {
          fks = fks + 3;
          fks = fks - 3;
          fks = 1;
      }
      else {
          fks = fks - 3;
          fks = fks + 3;
          fks = 0;
      }
      etp7 = etp7 + 1;
      u += fks;
  }

}

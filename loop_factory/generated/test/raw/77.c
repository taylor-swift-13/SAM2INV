int main1(int s,int x){
  int cr2, so, maf, ke, bh;

  cr2=x-5;
  so=0;
  maf=0;
  ke=0;
  bh=x;

  while (1) {
      if (!(maf<cr2)) {
          break;
      }
      ke += maf;
      s += so;
      maf += 1;
      bh = bh + 3;
  }

}

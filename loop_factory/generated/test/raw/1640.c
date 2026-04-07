int main1(){
  int q, sfv, dj, t2, f2;

  q=41;
  sfv=0;
  dj=10;
  t2=8;
  f2=12;

  while (sfv < q) {
      sfv = (dj = dj - 1, t2 = t2 - 1, f2 = f2 - 1, sfv + 1);
      t2++;
      t2 += f2;
  }

}

int main1(int l){
  int yp, cy, n2;

  yp=(l%30)+11;
  cy=0;
  n2=0;

  while (cy<yp) {
      cy++;
      n2 = n2 + 16;
      l += n2;
  }

}

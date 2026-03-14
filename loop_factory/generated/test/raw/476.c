int main1(int j){
  int kq, jm, h3mn, k, d2, ko;

  kq=(j%37)+18;
  jm=0;
  h3mn=0;
  k=0;
  d2=jm;
  ko=0;

  while (k<=kq-1) {
      d2 += kq;
      k += 1;
      h3mn += j;
  }

  while (ko<d2) {
      ko += 1;
      jm += j;
      j = j+d2-h3mn;
  }

}

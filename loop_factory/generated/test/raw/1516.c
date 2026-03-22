int main1(int u){
  int c3, skj, qc, be, r6gj, j, mp, h;

  c3=u+13;
  skj=0;
  qc=skj;
  be=c3;
  r6gj=skj;
  j=u;
  mp=3;
  h=-3;

  while (1) {
      if (!(skj<c3)) {
          break;
      }
      if (skj<c3/2) {
          qc = qc + be;
      }
      else {
          qc += 1;
      }
      if (skj+7<=c3+c3) {
          u += 6;
      }
      r6gj += qc;
      be++;
      h = h+(skj%2);
      mp = mp+(skj%2);
      r6gj = r6gj - 1;
      if (j+5<c3) {
          be++;
      }
      if ((skj%2)==0) {
          j++;
      }
      else {
          be = u-be;
      }
      skj = c3;
  }

}

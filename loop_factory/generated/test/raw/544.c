int main1(int g){
  int nk4e, y, c, rj;

  nk4e=g-7;
  y=0;
  c=0;
  rj=7;

  while (1) {
      if (!(y<nk4e&&rj>0)) {
          break;
      }
      c += rj;
      y++;
      rj -= 1;
      g += nk4e;
  }

}

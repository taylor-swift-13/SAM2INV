int main1(){
  int w, dr1, mw2, qj;

  w=(1%27)+17;
  dr1=0;
  mw2=dr1;
  qj=0;

  while (dr1 < w) {
      dr1 += 1;
      qj = qj + 1;
      mw2 = mw2 + qj * qj;
  }

}

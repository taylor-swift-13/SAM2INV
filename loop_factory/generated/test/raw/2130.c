int main1(){
  int rr, dm, x2vq, fwq;

  rr=1+22;
  dm=0;
  x2vq=dm;
  fwq=2;

  while (1) {
      if (!(dm+1<=rr)) {
          break;
      }
      if (x2vq+3<=rr) {
          x2vq = x2vq + 3;
      }
      else {
          x2vq = rr;
      }
      fwq = fwq + dm;
      rr = (dm+1)-1;
  }

}

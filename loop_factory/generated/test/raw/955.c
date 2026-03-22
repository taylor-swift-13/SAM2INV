int main1(int r,int g){
  int qr, r2pr, rr, c;

  qr=g-9;
  r2pr=1;
  rr=qr;
  c=16;

  while (rr<qr) {
      rr = rr + 3;
      c += r2pr;
      r += 2;
      c = c + 3;
  }

}

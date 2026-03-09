int main1(int l){
  int qr, yxvi, w, lt, lnx, af;

  qr=(l%31)+15;
  yxvi=-6;
  w=5;
  lt=0;
  lnx=l;
  af=3;

  while (lt<=qr-1) {
      af += yxvi;
      w += l;
      lt += 1;
      lnx += 2;
      af += lnx;
  }

}

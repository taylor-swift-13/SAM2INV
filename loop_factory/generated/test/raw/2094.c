int main1(){
  int qr, i4i, d5, isz;

  qr=(1%39)+12;
  i4i=0;
  d5=qr;
  isz=qr;

  while (i4i < qr) {
      d5 += isz;
      i4i = i4i + (qr - i4i + 1)/2;
      d5 += 4;
  }

}

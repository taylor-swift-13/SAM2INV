int main1(){
  int qr, m, i, ow, t6d;

  qr=(1%35)+13;
  m=0;
  i=0;
  ow=0;
  t6d=4;

  while (i<qr&&t6d>0) {
      ow += t6d;
      i = i + 1;
      ow = ow + m;
      t6d--;
  }

}

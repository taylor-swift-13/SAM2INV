int main1(int s){
  int bp9f, ljh, qr, oj;

  bp9f=72;
  ljh=2;
  qr=-1;
  oj=ljh;

  while (qr<=bp9f-1) {
      qr += 1;
      oj = bp9f-qr;
      s = s + bp9f;
  }

  while (1) {
      if (!(bp9f<qr)) {
          break;
      }
      bp9f = bp9f + 1;
      ljh = qr-bp9f;
      s = s + bp9f;
  }

}

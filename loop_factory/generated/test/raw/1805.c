int main1(){
  int l7h, krw, t6, qh;

  l7h=10;
  krw=1;
  t6=0;
  qh=0;

  while (1) {
      if (!(l7h > 0)) {
          break;
      }
      l7h--;
      krw = krw * 2;
      t6 = t6+(qh%6);
      qh = qh + 3;
  }

}

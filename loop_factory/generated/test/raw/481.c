int main1(int p){
  int uk, azjh, l1, y, t4q;

  uk=0;
  azjh=0;
  l1=0;
  y=0;
  t4q=(p%18)+5;

  while (1) {
      if (!(t4q>=1)) {
          break;
      }
      y = y+p*p;
      l1 = l1+p*p;
      t4q = t4q - 1;
      azjh = azjh+p*p;
      p += uk;
  }

  while (l1>y) {
      l1 = l1 - y;
      y = (1)+(y);
      uk = uk+(l1%3);
      p = p + l1;
  }

}

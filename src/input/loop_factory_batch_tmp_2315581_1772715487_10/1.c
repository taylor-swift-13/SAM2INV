int main1(int t){
  int a3, jka, bm;

  a3=t*2;
  jka=a3;
  bm=4;

  while (jka<a3) {
      bm = jka%5;
      if (jka>=bm) {
          bm = (jka-bm)%5;
          bm = bm+bm-bm;
      }
      else {
          bm = bm + bm;
      }
      jka++;
      t += a3;
  }

}

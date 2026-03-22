int main1(int m){
  int c1, sf, db3p, yw, tnn, rt5, ol;

  c1=32;
  sf=0;
  db3p=3;
  yw=3;
  tnn=0;
  rt5=3;
  ol=0;

  while (sf<c1) {
      if (sf%3==0) {
          if (db3p>0) {
              db3p -= 1;
              tnn = tnn + 1;
          }
      }
      else {
          if (db3p<rt5) {
              db3p++;
              yw = yw + 1;
          }
      }
      sf++;
      ol = ol + 1;
  }

}

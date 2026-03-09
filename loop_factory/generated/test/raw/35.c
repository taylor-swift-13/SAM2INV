int main1(int b){
  int pj, e5, e9r5, g, jb9j, i0bs;

  pj=b;
  e5=0;
  e9r5=0;
  g=0;
  jb9j=0;
  i0bs=0;

  while (1) {
      if (!(e5<pj)) {
          break;
      }
      if (e5%11==0) {
          i0bs = i0bs + 1;
      }
      else {
          if (e5%9==0) {
              jb9j++;
          }
          else {
              if (e5%3==0) {
                  g++;
              }
              else {
                  e9r5++;
              }
          }
      }
      e5++;
      b = b + e9r5;
  }

}

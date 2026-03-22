int main1(int k){
  int i0, f, ra, nb, v5, b, yk;

  i0=k;
  f=0;
  ra=0;
  nb=0;
  v5=0;
  b=0;
  yk=0;

  while (1) {
      if (!(ra<=i0-1)) {
          break;
      }
      if (ra%11==0) {
          yk = yk + 1;
      }
      else {
          if (ra%5==0) {
              b += 1;
          }
          else {
              if (ra%6==0) {
                  v5 = v5 + 1;
              }
              else {
                  nb++;
              }
          }
      }
      ra++;
      k += nb;
  }

  while (b<f) {
      ra += b;
      i0 = i0+f-nb;
      b += 1;
      k += b;
  }

}

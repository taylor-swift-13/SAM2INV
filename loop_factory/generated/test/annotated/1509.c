int main1(int o,int f){
  int bru, c0, j, c6, hb, ho, xt6x, uj4n, wr;
  bru=60;
  c0=0;
  j=0;
  c6=0;
  hb=0;
  ho=0;
  xt6x=0;
  uj4n=0;
  wr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uj4n == 2*c6 + 3*hb + 4*ho + 5*xt6x + (c0 - ((c0 + 10) / 11));
  loop invariant 0 <= c0 <= bru;
  loop invariant 0 <= j;
  loop invariant 0 <= uj4n;
  loop invariant 0 <= wr;
  loop assigns c0, wr, j, uj4n, c6, hb, ho, xt6x;
*/
while (c0<bru) {
      if (!(!(c0%11==0))) {
          if (c0%8==0) {
              c6 = c6 + 1;
              uj4n += 2;
          }
          else {
              if (c0%5==0) {
                  hb++;
                  uj4n = uj4n + 3;
              }
              else {
                  if (c0%4==0) {
                      ho += 1;
                      uj4n += 4;
                  }
                  else {
                      if (1) {
                          xt6x += 1;
                          uj4n = uj4n + 5;
                      }
                  }
              }
          }
      }
      else {
          j++;
          uj4n++;
      }
      c0 = c0 + 1;
      wr = wr+c0%8;
  }
}